# 执行分析的核心过程
import datetime
import json
import logging
import multiprocessing
import os
import pickle
import random
import re
import sys
import time
import traceback
from collections import Counter, deque
from multiprocessing import Pool
from typing import Dict, List, Optional, Set

import Levenshtein
import networkx as nx
from tqdm import tqdm

from apk import (
    Apk,
    _descriptor_tokens_from_signature,
    descriptor_index_version,
    empty_descriptor_token,
)
from lh_config import (
    apk_pickle_dir,
    bucket_pickle_dir,
    class_similar,
    lib_similar,
    max_thread_num,
    method_similar,
    pickle_dir,
    setup_logger,
    skeleton_pickle_dir,
)
from lib import ThirdLib
from lib_groups import build_lib_groups
abstract_method_weight =3


HEAVY_BUCKET_FAMILIES = {
    "com.fasterxml.jackson.core.jackson-databind",
    "com.google.guava.guava",
    "org.jetbrains.kotlin.kotlin-stdlib",
}
HEAVY_BUCKET_PRIORITY = (
    "com.google.guava.guava",
    "org.jetbrains.kotlin.kotlin-stdlib",
    "com.fasterxml.jackson.core.jackson-databind",
)

MODULE_SCOPE_LABELS = {
    "collections_iterators_functors",
    "collections_list_set_bag",
    "collections_map",
    "compress_archivers",
    "compress_compressors",
    "compress_gzip_bzip2",
    "compress_tar",
    "compress_zip",
    "io_input",
    "io_output",
    "io_root_file",
}


class _StubThirdLib:
    """Compatibility shim for skeleton pickles created from a __main__ helper."""

    pass


# Get each opcode and its corresponding number (from 1 to 232).
def get_opcode_coding(path):
    opcode_dict = {}
    with open(path, "r", encoding="utf-8") as file:
        for line in file.readlines():
            line = line.strip("\n")
            if line != "":
                opcode = line[:line.find(":")]
                num = line[line.find(":") + 1:]
                opcode_dict[opcode] = num

    return opcode_dict


# Implement the library mapping file to which the subprocess build method belongs
def sub_method_map_decompile(lib_folder,
                             libs,
                             global_lib_info_dict):
    logger = setup_logger()
    if not os.path.exists(pickle_dir):
        os.mkdir(pickle_dir)

    for lib in libs:
        # 适配嵌套目录：将斜杠替换为下划线，避免 pickle 目录不存在报错
        flat_lib_name = lib.replace("/", "_").replace("\\", "_")
        lib_pickle_path = os.path.join(pickle_dir, flat_lib_name).replace(".dex", ".pkl")
        try:
            if os.path.exists(lib_pickle_path):
                with open(lib_pickle_path, 'rb') as file:
                    lib_obj = pickle.load(file)
            else:
                lib_obj = ThirdLib(lib_folder + "/" + lib, logger)
                pickle.dump(lib_obj, open(lib_pickle_path, 'wb'))
        except Exception as e:
            traceback_str = traceback.format_exc()  # Get stack frame string
            logger.error("Error in sub_method_map_decompile: %s\n%s", e, traceback_str)
            continue

        # Record library decompilation information object
        global_lib_info_dict[lib] = lib_obj


# 实现子进程提前反编译所有单个库
def sub_decompile_lib(lib_folder,
                      libs,
                      global_lib_info_dict):
    logger = setup_logger()
    for lib in libs:
        if lib not in global_lib_info_dict:
            lib_obj = ThirdLib(lib_folder + "/" + lib, logger)
        else:
            lib_obj = global_lib_info_dict[lib]

        global_lib_info_dict[lib] = lib_obj


# Filter the current app class through the Bloom filter and return a collection of classes that satisfy the filter criteria
def deal_bloom_filter(lib_class_name, lib_classes_dict, app_filter):
    if len(lib_classes_dict[lib_class_name]) == 2:  # Indicates that it is currently an interface or abstract classc
        lib_class_bloom_info = lib_classes_dict[lib_class_name][1]
    else:
        lib_class_bloom_info = lib_classes_dict[lib_class_name][3]

    satisfy_classes = set()
    satisfy_count = 0

    for index in lib_class_bloom_info:

        if index not in app_filter:  # Indicates that no class with this feature exists in the current app
            return set()

        # Get the set of all classes in the app that satisfy this condition
        count = lib_class_bloom_info[index]
        if satisfy_count == 0:
            satisfy_classes = app_filter[index][count - 1]
            satisfy_count += 1
        else:
            satisfy_classes = satisfy_classes & app_filter[index][count - 1]

    return satisfy_classes


def _match_counter(count_a: Counter, count_b: Counter):
    # Check if for every element in count_a,
    # the count is less than or equal to its count in count_b
    for element in count_a:
        if count_a[element] > count_b.get(element, 0):
            return False
    return True


def is_match(pattern, string):
    return bool(pattern.match(string))


def match_with_regex_new(strings, patterns):
    n = len(patterns)
    m = len(strings)

    adj_matrix = [[is_match(pattern, string) for string in strings] for pattern in patterns]

    matching = [-1] * m

    def dfs(u, visited):
        for v in range(m):
            if adj_matrix[u][v] and not visited[v]:
                visited[v] = True
                if matching[v] == -1 or dfs(matching[v], visited):
                    matching[v] = u
                    return True
        return False

    for u in range(n):
        visited = [False] * m
        dfs(u, visited)

    return all(match != -1 for match in matching)


def match_with_regex(lst1, patterns):
    """
    Check if elements of lst1 match at least one regex from lst2.
    """
    # used = [False] * len(patterns)
    for item1 in lst1:
        found = False
        for i, pattern in enumerate(patterns):
            if pattern.match(item1):
                # used[i] = True
                found = True
                break
        if not found:
            return False
    return True


def match_fields(lst1: list, lst2: list):
    """
    Check if all fields in the first list match at least one regex from the second list.
    """
    # 计算两个列表中每个元素的出现次数
    counts1 = Counter(lst1)
    counts2 = Counter(lst2)

    # 遍历 lst1 中每个元素的计数
    for item, count_in_lst1 in counts1.items():
        # 检查 lst2 中该元素的计数是否小于 lst1 中该元素的计数
        if counts2[item] < count_in_lst1:
            return False  # 如果 lst2 中某个元素的数量不足，则不包含
    return True  # 如果所有元素在 lst2 中的数量都足够，则包含


def _iter_candidate_apk_classes(apk_classes_dict, candidate_class_names=None):
    if candidate_class_names is None:
        return apk_classes_dict.keys()
    return candidate_class_names


def _get_apk_descriptor_candidates(apk_obj, lib_method_patterns, class_kind: str):
    descriptor_index = getattr(apk_obj, "descriptor_index", None)
    if not isinstance(descriptor_index, dict):
        return None
    kind_index = descriptor_index.get(class_kind)
    if not isinstance(kind_index, dict):
        return None

    tokens = set()
    for pattern in lib_method_patterns:
        pattern_text = getattr(pattern, "pattern", pattern)
        tokens.update(_descriptor_tokens_from_signature(pattern_text))
    if not tokens:
        return None

    candidates = set()
    for token in tokens:
        candidates.update(kind_index.get(token, set()))
    candidates.update(kind_index.get(empty_descriptor_token, set()))
    return candidates


def _match_fuzzy_signature_interface(lib_class_dict, apk_classes_dict, candidate_class_names=None):
    satisfy_classes = set()

    lib_method_patterns = lib_class_dict[0]
    lib_class_desc_pattern = lib_class_dict[1]
    for apk_class_name in _iter_candidate_apk_classes(apk_classes_dict, candidate_class_names):
        if apk_class_name not in apk_classes_dict:
            continue
        apk_class_dict = apk_classes_dict[apk_class_name]
        if len(apk_class_dict) != 2:
            continue
        # apk_field_counter: Counter = apk_class_dict[4]
        apk_method_sigs = apk_class_dict[0]
        apk_class_desc = apk_class_dict[1]
        if not lib_class_desc_pattern.match(apk_class_desc):
            continue
        # the methods in apk should contain all the methods in lib
        if match_with_regex(apk_method_sigs, lib_method_patterns):
            # and _match_counter(apk_field_counter, lib_field_counter)):
            satisfy_classes.add(apk_class_name)
        else:
            pass

    return satisfy_classes


def _match_fuzzy_signature(lib_class_dict, apk_classes_dict, candidate_class_names=None):
    satisfy_classes = set()

    # lib_field_counter: Counter = lib_class_dict[5]
    lib_method_patterns = lib_class_dict[5]
    lib_field_patterns = lib_class_dict[6]
    lib_class_desc_pattern = lib_class_dict[7]
    for apk_class_name in _iter_candidate_apk_classes(apk_classes_dict, candidate_class_names):
        if apk_class_name not in apk_classes_dict:
            continue
        apk_class_dict = apk_classes_dict[apk_class_name]
        if len(apk_class_dict) == 2:
            continue
        # apk_field_counter: Counter = apk_class_dict[4]
        apk_method_sigs = apk_class_dict[4]
        apk_field_sigs = apk_class_dict[5]
        apk_class_desc = apk_class_dict[6]
        if not lib_class_desc_pattern.match(apk_class_desc):
            continue
        # the methods in apk should contain all the methods in lib
        if match_with_regex(apk_method_sigs, lib_method_patterns) and \
                match_fields(apk_field_sigs, lib_field_patterns):
            # and _match_counter(apk_field_counter, lib_field_counter)):
            satisfy_classes.add(apk_class_name)
        else:
            pass

    return satisfy_classes


# Processing to get the filter result set of each class in all classes of the apk, record it in the filter_result dictionary, and statistically filter the effect of the information
def pre_match(apk_obj, lib_obj, LOGGER):
    lib_classes_dict = lib_obj.classes_dict
    apk_classes_dict = apk_obj.classes_dict

    filter_result = {}
    for lib_class_name in lib_classes_dict:

        if len(lib_classes_dict[lib_class_name]) == 2:
            lib_method_patterns = lib_classes_dict[lib_class_name][0]
            candidates = _get_apk_descriptor_candidates(apk_obj, lib_method_patterns, "interface")
            satisfy_classes = _match_fuzzy_signature_interface(
                lib_classes_dict[lib_class_name],
                apk_classes_dict,
                candidates,
            )
        else:
            lib_method_patterns = lib_classes_dict[lib_class_name][5]
            candidates = _get_apk_descriptor_candidates(apk_obj, lib_method_patterns, "concrete")
            satisfy_classes = _match_fuzzy_signature(
                lib_classes_dict[lib_class_name],
                apk_classes_dict,
                candidates,
            )

        if len(satisfy_classes) > 0:
            filter_result[lib_class_name] = satisfy_classes

    return filter_result


# The use of inclusion to determine matches is to resist control flow randomization, insertion of invalid code, randomization of partial code positions, etc.
def match(apk_method_opcode_list, lib_method_opcode_list, opcode_dict):
    method_bloom_filter = {}
    for opcode in apk_method_opcode_list:
        method_bloom_filter[opcode_dict[opcode]] = 1

    # Then take the apk class and match it in the filter
    for opcode in lib_method_opcode_list:
        if opcode != "" and opcode_dict[opcode] not in method_bloom_filter:
            return False

    return True


def edit_distance_similarity(list1, list2):
    return 1 - Levenshtein.distance(list1, list2) / max(len(list1), len(list2))


def list_intersection(list1, list2):
    intersection = []
    temp_list2 = list2.copy()
    for item in list1:
        if item in temp_list2:
            intersection.append(item)
            temp_list2.remove(item)
    return intersection


def list_union(list1, list2):
    union = list1.copy()
    temp_list2 = list2.copy()
    for item in list1:
        if item in temp_list2:
            temp_list2.remove(item)
    union.extend(temp_list2)
    return union


def jaccard_similarity(list1 :list, list2:list):
    set1 = set(list1)
    set2 = set(list2)
    intersection = set1.intersection(set2)
    union = set1.union(set2)
    if len(union) == 0:
        return 1.0  # The empty set of identical sets returns a similarity of 1.
    similarity = len(intersection) / len(union)
    return similarity

def jaccard_similarity2(list1: list, list2: list):
    # Handle the special case where both lists are empty
    if not list1 and not list2:
        return 1.0

    # Count element occurrences in each list
    counter1 = Counter(list1)
    counter2 = Counter(list2)

    intersection_count = 0
    union_count = 0

    # Get all unique elements present in either list
    all_unique_elements = set(counter1.keys()) | set(counter2.keys())

    for element in all_unique_elements:
        count1 = counter1.get(element, 0)
        count2 = counter2.get(element, 0)

        # Intersection: sum of the minimum counts for each common element
        intersection_count += min(count1, count2)

        # Union: sum of the maximum counts for each element
        union_count += max(count1, count2)

    # If the union is empty (which should only happen if both lists were empty,
    # and we've already handled that, but as a safeguard)
    if union_count == 0:
        return 0.0
    else:
        return intersection_count / union_count


def calculate_intersection_ratio(list1: list, list2: list):
    # If list1 is empty, return 1.0 as per your requirement.
    if not list1:
        return 1.0

    # If list2 is empty, there are no elements to repeat, so the proportion is 0.
    if not list2:
        return 0.0

    # Count element occurrences in both lists
    counter1 = Counter(list1)
    counter2 = Counter(list2)

    repeated_count = 0

    # Iterate through elements in list1's counter to find overlaps with list2
    for element, count_in_list1 in counter1.items():
        count_in_list2 = counter2.get(element, 0)

        # The number of times this element from list2 can be "matched" by list1
        # is the minimum of its count in list2 and its count in list1.
        repeated_count += min(count_in_list2, count_in_list1)

    # The proportion is the total number of "repeated" elements divided by the total
    # number of elements in list2.
    return repeated_count / len(list1)


def calculate_intersection_ratio2(list1, list2):
    set1 = set(list1)
    set2 = set(list2)

    # Check if set1 is empty to avoid division by zero errors
    if len(set1) == 0:
        return 1

    intersection = set1.intersection(set2)

    ratio = len(intersection) / len(set1)

    return ratio


# Perform a coarse-grained match between an apk and a lib, get the coarse-grained similarity value, a list of all apk classes that have completed the match
def coarse_match(apk_obj, lib_obj, filter_result, LOGGER):
    # Record the matching relationships of specific methods in each coarse-grained matched class, to be used later at a fine-grained level to determine if these methods are true matches.
    # apk_class_methods_match_dict = {}
    lib_class_match_dict = {}
    lib_match_classes = set()
    abstract_lib_match_classes = set()
    abstract_apk_match_classes = set()

    lib_classes_dict = lib_obj.classes_dict
    apk_classes_dict = apk_obj.classes_dict

    for lib_class in lib_classes_dict:
        qualified_class_name_match = False

        if lib_class not in filter_result:
            continue

        class_match_dict = {}

        filter_set = filter_result[lib_class]

        if len(lib_classes_dict[lib_class]) == 2:
            for apk_class in filter_set:
                if apk_class in abstract_apk_match_classes:
                    continue
                if apk_class not in apk_classes_dict or len(apk_classes_dict[apk_class]) > 2:
                    continue
                apk_method_sigs = apk_classes_dict[apk_class][0]
                lib_method_patterns = lib_classes_dict[lib_class][0]
                apk_class_method_num = len(apk_method_sigs)
                lib_class_method_num = len(lib_method_patterns)

                if apk_class_method_num > 0 and apk_class_method_num == lib_class_method_num and \
                        match_with_regex(apk_method_sigs, lib_method_patterns):
                    LOGGER.debug("match interface %s  ->  %s", lib_class, apk_class)
                    abstract_apk_match_classes.add(apk_class)
                    abstract_lib_match_classes.add(lib_class)
                    break

            continue

        for apk_class in filter_set:
            if apk_class not in apk_classes_dict:
                continue

            if len(apk_classes_dict[apk_class]) == 1:
                continue

            if qualified_class_name_match:
                break

            # use class name to accelerate the match
            if apk_class == lib_class:
                class_match_dict.clear()
                qualified_class_name_match = True


            # Perform one-to-one matching of methods in the class, with the goal of getting all methods in the lib class that complete a one-to-one match (looking for maximum similarity matches each time)
            methods_match_dict = {}  # Used to record the relationship between the class methods in the apk and the corresponding lib class method matches, one-to-one
            methods_tomatch_dict = {}  # Used to record the relationship between class methods in the apk and their corresponding lib class method matches, one-to-many
            apk_class_methods_dict = apk_classes_dict[apk_class][3]
            lib_class_methods_dict = lib_classes_dict[lib_class][4]
            lib_match_methods = []  # Ensures that methods in the lib class are not duplicated and matched.

            # Because of the possibility of apk shrinking, the method will be less, so use the apk's method to match the lib's method.
            for apk_method in apk_class_methods_dict:
                max_method_sim = -1

                for lib_method in lib_class_methods_dict:

                    if lib_method in lib_match_methods:
                        continue

                    # Guaranteed fuzzy signature matching
                    lib_method_info = lib_class_methods_dict[lib_method]
                    apk_method_info = apk_class_methods_dict[apk_method]
                    lib_method_pattern = re.compile(lib_method_info[4])
                    apk_method_sig = apk_method_info[4]
                    if not lib_method_pattern.match(apk_method_sig):
                        second_pattern = lib_method_info[-1]
                        if type(second_pattern) is not re.Pattern:
                            continue
                        else:
                            if not second_pattern.match(apk_method_sig):
                                continue

                    # Try to match the overall MD5 value of the method
                    if apk_method_info[0] == lib_method_info[0]:
                        if apk_method in methods_match_dict:
                            lib_match_methods.remove(methods_match_dict[apk_method])
                        methods_match_dict[apk_method] = lib_method
                        lib_match_methods.append(lib_method)
                        break

                    apk_method_opcodes: list = apk_method_info[1]
                    lib_method_opcodes: list = lib_method_info[1]
                    # sim_op = edit_distance_similarity(apk_method_opcodes, lib_method_opcodes)
                    sim_op = jaccard_similarity2(apk_method_opcodes, lib_method_opcodes)

                    apk_method_strings: list = apk_method_info[2]
                    lib_method_strings: list = lib_method_info[2]
                    sim_str = jaccard_similarity2(apk_method_strings, lib_method_strings)
                    sim = (sim_op + sim_str) / 2

                    # if len(apk_method_opcodes) <= 4:
                    #     continue
                    if sim >= method_similar:
                        # print(f'{apk_method}:{len(apk_method_opcodes)} <--> {lib_method}:{len(lib_method_opcodes)}')
                        # print(f'sim:{sim} mul:{len(apk_method_opcodes)*sim}')
                        # print(f'----------------------------------')
                        if sim > max_method_sim:
                            if apk_method in methods_match_dict:
                                lib_match_methods.remove(methods_match_dict[apk_method])
                            methods_match_dict[apk_method] = lib_method
                            lib_match_methods.append(lib_method)
                            max_method_sim = sim
                        # if(apk_method[:apk_method.rfind(".")]==lib_method[:lib_method.rfind(".")]):
                        #     print(f'{apk_method}<->{lib_method} {sim}')
                    elif apk_method not in methods_match_dict:
                        # the apk should contain tpl methods opcodes
                        overlap_op_sim = calculate_intersection_ratio(lib_method_opcodes, apk_method_opcodes)
                        overlap_str_sim = calculate_intersection_ratio(lib_method_strings, apk_method_strings)
                        overlap_sim = (overlap_op_sim + overlap_str_sim) / 2

                        if overlap_sim >= method_similar:
                            if apk_method not in methods_tomatch_dict:
                                methods_tomatch_dict[apk_method] = []
                            methods_tomatch_dict[apk_method].append(lib_method)


                keys_to_remove = []

                # Iterate through the dictionary and add the keys to be deleted to the list
                for method_tomatch in methods_tomatch_dict:
                    if method_tomatch in methods_match_dict:
                        keys_to_remove.append(method_tomatch)

                # Delete these keys at the end of the traversal
                for key in keys_to_remove:
                    methods_tomatch_dict.pop(key)


            # Determine if the class matches based on the method in the apk class that completes the match
            match_methods_weight = 0
            for apk_method in methods_match_dict.keys():
                match_methods_weight += apk_class_methods_dict[apk_method][3]
            for apk_method in methods_tomatch_dict.keys():
                match_methods_weight += apk_class_methods_dict[apk_method][3]

            class_weight = apk_classes_dict[apk_class][2]
            class_sim = match_methods_weight / class_weight

            # Class coarse-grained matching if the sum of the weights of the matching methods in the apk class / total class weight > threshold
            if class_sim >= class_similar:
                lib_match_classes.add(lib_class)
                class_match_dict[apk_class] = [methods_match_dict, methods_tomatch_dict]

        # Record details of coarse-grained matches of apk classes to all lib classes
        if len(class_match_dict) != 0:
            lib_class_match_dict[lib_class] = class_match_dict

    return lib_match_classes, abstract_lib_match_classes, lib_class_match_dict


def check_method_invoke_times_and_length(method_name, lib_classes_dict):
    class_name = method_name[:method_name.rfind(".")]
    invoke_method_length_limits = [10000, 28, 16, 12, 10]
    # invoke_method_length_limits = [10000, 28, 16, 12, 10 ,10 ,10]
    if class_name not in lib_classes_dict.keys():
        return False
    # This class does not have a method that can be inlined.
    if len(lib_classes_dict[class_name]) < 5:
        return False

    # Handling the case where the method name is not in the dictionary
    if method_name not in lib_classes_dict[class_name][4].keys():
        return False
    # Indicates that the method has not been called
    if len(lib_classes_dict[class_name][4][method_name]) <= 5:
        return False
    invoke_time, invoke_method_length = lib_classes_dict[class_name][4][method_name][5]
    if invoke_time >= 5:
        return False
    else:
        # invoke_method_length = lib_classes_dict[class_name][4][method_name][3]
        return invoke_method_length <= invoke_method_length_limits[invoke_time - 1]


def check_method_access_flags(method_name, lib_classes_dict):
    class_name = method_name[:method_name.rfind(".")]
    if class_name not in lib_classes_dict.keys():
        return False
    if len(lib_classes_dict[class_name]) < 5:
        return False

    if method_name not in lib_classes_dict[class_name][4].keys():
        return False
    if len(lib_classes_dict[class_name][4][method_name]) < 5:
        return False
    # Locked on call, no inlining
    if "synchronized" in lib_classes_dict[class_name][4][method_name][4]:
        return False

    return True


def get_method_action(node, node_dict, method_action_dict, Lib_methods_string: dict, route_method_set, invoke_length,
                      lib_classes_dict, isInlined=False):
    method_name = node[:node.rfind("_")]
    node_num = int(node[node.rfind("_") + 1:])
    cur_action_seq: list = node_dict[node][0]
    callees = []
    # delete move-result in cur_action_seq
    if isInlined and node_num != 1 and len(cur_action_seq) > 0 and 10 <= cur_action_seq[0] <= 12:
        cur_action_seq = cur_action_seq[1:]

    if node.endswith("_1"):  # Indicates that the call entered a new method
        if method_name in method_action_dict:
            return method_action_dict[method_name]
        route_method_set.add(method_name)

    invoke_method_name = node_dict[node][1]
    cur_invoke_len = invoke_length

    doInline = False
    if invoke_method_name != [] and invoke_method_name not in route_method_set and invoke_method_name + "_1" in node_dict \
            and invoke_length <= 20 \
            and check_method_invoke_times_and_length(invoke_method_name, lib_classes_dict) \
            and check_method_access_flags(invoke_method_name, lib_classes_dict):
        callees.append(invoke_method_name)
        doInline = True
        invoke_length += 1
        seq,sub_callees = get_method_action(invoke_method_name + "_1", node_dict, method_action_dict, Lib_methods_string,
                                route_method_set,
                                invoke_length, lib_classes_dict)
        callees.extend(sub_callees)

        # Remove the "invoke-virtual" at the end of cur_action_seq
        cur_action_seq = cur_action_seq[:-1]
        # delete the return statement in callee
        if len(seq) > 0:
            seq_last_opcode: int = seq[-1]
            if 14 <= seq_last_opcode <= 17:
                seq = seq[:-1]

            cur_action_seq = cur_action_seq + seq

    next_node = method_name + "_" + str(node_num + 1)
    if next_node in node_dict:
        seq, sub_callees = get_method_action(next_node, node_dict, method_action_dict, Lib_methods_string, route_method_set,
                                cur_invoke_len,
                                lib_classes_dict, doInline)

        cur_action_seq = cur_action_seq + seq
        callees.extend(sub_callees)
    if doInline:
        Lib_methods_string[method_name] = Lib_methods_string[method_name] + Lib_methods_string[invoke_method_name]
    if node.endswith("_1"):
        # method_action_dict[method_name] = deal_opcode_deq(cur_action_seq)
        method_action_dict[method_name] = (cur_action_seq, callees)
        route_method_set.remove(method_name)

    return cur_action_seq, callees


def get_methods_action(method_list, lib_obj: ThirdLib, Lib_methods_string: dict):
    method_action_dict = {}
    lib_classes_dict = lib_obj.classes_dict
    for method in method_list:
        get_method_action(
            method + "_1",
            lib_obj.nodes_dict,
            method_action_dict,
            Lib_methods_string,
            set(),
            0,
            lib_classes_dict,
        )

    return method_action_dict


# Fine-grained matching
def fine_match(apk_obj, lib_obj, lib_class_match_dict, LOGGER):
    apk_classes_dict = apk_obj.classes_dict
    lib_classes_dict = lib_obj.classes_dict
    lib_pre_methods = set()

    apk_methods_action = {}
    apk_methods_string = {}
    lib_mathods_string = {}
    for lib_class in lib_obj.classes_dict:
        if len(lib_classes_dict[lib_class]) == 2:
            continue
        for lib_method in lib_obj.classes_dict[lib_class][4]:
            lib_mathods_string[lib_method] = lib_classes_dict[lib_class][4][lib_method][2]

    for lib_class in lib_class_match_dict:
        for apk_class in lib_class_match_dict[lib_class]:
            # only to match the methods in the pass the overlap filter
            for apk_method in lib_class_match_dict[lib_class][apk_class][1].keys():
                apk_methods_action[apk_method] = apk_classes_dict[apk_class][3][apk_method][1]
                apk_methods_string[apk_method] = apk_classes_dict[apk_class][3][apk_method][2]
            for lib_methods in lib_class_match_dict[lib_class][apk_class][1].values():
                lib_pre_methods.update(set(list(lib_methods)))

    LOGGER.debug("Cross-Inlining...")
    lib_methods_action = get_methods_action(lib_pre_methods, lib_obj, lib_mathods_string)
    tp = fp = tn = fn = 0


    lib_class_match_result = {}
    finish_apk_classes = []
    lib_match_methods_map = {}

    for lib_class in lib_class_match_dict:
        lib_match_methods_map[lib_class] = {}
        max_match_class_opcodes = 0
        match_apk_class = ""
        # Filter one-to-many matches from apk class to lib class to one-to-one matches
        for apk_class in lib_class_match_dict[lib_class]:
            lib_match_methods_map[lib_class][apk_class] = set()

            if apk_class in finish_apk_classes:
                continue

            cur_match_class_opcodes = 0
            for apk_method, lib_method in lib_class_match_dict[lib_class][apk_class][0].items():
                cur_match_class_opcodes += lib_classes_dict[lib_class][4][lib_method][3]


            # For the apk method that tomatches in a coarse-grained match, find the single most matching lib method
            lib_match_methods = []
            for apk_method, lib_methods in lib_class_match_dict[lib_class][apk_class][1].items():
                apk_method_opcodes: list = apk_methods_action[apk_method]
                apk_mathod_strings: list = apk_methods_string[apk_method]
                LOGGER.debug("apk_method: %s", apk_method_opcodes)
                max_method_sim = -1
                max_method_name = None
                match_lib_method = " "
                match_lib_callees = []
                match_lib_method_opcodes = []
                TP = FP = TN = FN = 0
                for lib_method in lib_methods:
                    if lib_method in lib_match_methods:
                        continue
                    lib_method_opcodes, callees = lib_methods_action[lib_method]
                    lib_method_strings: list = lib_mathods_string[lib_method]
                    # lib_method_opcodes = lib_classes_dict[lib_class][4][lib_method][1]
                    # callees = []
                    # lib_method_strings: set = lib_classes_dict[lib_class][4][lib_method][2]
                    LOGGER.debug("lib_method: %s", lib_method_opcodes)
                    # if match(apk_method_opcodes, lib_method_opcodes, opcode_dict):
                    sim_opc = jaccard_similarity(apk_method_opcodes, lib_method_opcodes)
                    sim_str = jaccard_similarity(apk_mathod_strings, lib_method_strings)

                    # if (apk_method == lib_method):
                    #     print(f'{apk_method} {lib_method} {sim}')
                    sim = 0.5 * sim_opc + 0.5 * sim_str
                    if sim >= method_similar and sim > max_method_sim:
                        if match_lib_method == " ":
                            match_lib_method = lib_method
                            match_lib_callees = callees
                            match_lib_method_opcodes = lib_method_opcodes
                            lib_match_methods.append(match_lib_method)
                            max_method_sim = sim
                            max_method_name = lib_method
                        # Indicates that methods with previous matches have been stored in lib_match_methods
                        else:
                            lib_match_methods.remove(match_lib_method)
                            match_lib_method = lib_method
                            lib_match_methods.append(match_lib_method)
                            match_lib_callees = callees
                            max_method_sim = sim
                            max_method_name = lib_method

                if match_lib_method != " ":
                    # if(apk_method==match_lib_method):
                    #     print(f'{apk_method} <---> {match_lib_method} :{max_method_sim}')
                    #     print(f'{apk_method_opcodes}')
                    #     print(f'{match_lib_method_opcodes}')
                    lib_match_methods.append(match_lib_method)
                    lib_match_methods_map[lib_class][apk_class].add(
                        (apk_method, match_lib_method, tuple(match_lib_callees)))
                    cur_match_class_opcodes += lib_classes_dict[lib_class][4][match_lib_method][3]
                    for callee in match_lib_callees:
                        callee_class = callee[:callee.rfind(".")]
                        cur_match_class_opcodes += lib_classes_dict[callee_class][4][callee][3]

            if cur_match_class_opcodes > max_match_class_opcodes:
                max_match_class_opcodes = cur_match_class_opcodes
                match_apk_class = apk_class

        if match_apk_class == "":
            continue

        # if lib_class == match_apk_class:
        #     print(f"TP@ {lib_class} <---> {match_apk_class} :{max_match_class_opcodes}")
        # elif max_match_class_opcodes > 10:
        #     print(f"FP@ {lib_class} <---> {match_apk_class} :{max_match_class_opcodes}")

        match_info = [match_apk_class, max_match_class_opcodes]
        # print(f'{lib_class} <---> {match_apk_class} :{max_match_class_opcodes}')
        # print(lib_match_methods_map[lib_class][match_apk_class])
        lib_class_match_result[lib_class] = match_info
        finish_apk_classes.append(match_apk_class)
    LOGGER.info(f'{lib_obj.lib_name} fp:{fp} fn:{fn} tp:{tp} tn:{tn}')
    return lib_class_match_result


def detect(apk_obj, lib_obj, LOGGER, return_details: bool = False):
    '''
    Detecting library information contained in an apk
    :param apk_obj: build apk object
    :param lib: library name
    :param lib_obj: The library object to build.
    :return: Dictionary to return detection results
    '''
    lib_name = getattr(lib_obj, "lib_name", "")
    if len(lib_obj.classes_dict) == 0:
        if return_details:
            return {
                "library_name": lib_name,
                "matched": False,
                "score": 0.0,
                "similarity": 0.0,
                "target_classes": [],
                "stage": "empty",
            }
        return {}

    lib_opcode_num = lib_obj.lib_opcode_num
    lib_classes_dict = lib_obj.classes_dict

    result = {}

    filter_result = pre_match(apk_obj, lib_obj, LOGGER)
    pre_match_opcodes = 0
    for lib_class in filter_result:
        # if lib_class not in filter_result[lib_class] and lib_class in apk_obj.classes_dict:
        #     print("FP lib_class: ", lib_class)
        # elif lib_class in filter_result[lib_class]:
        #     print("TP lib_class: ", lib_class)

        if len(lib_classes_dict[lib_class]) == 2:  # Description is an interface or abstract class
            pre_match_opcodes += (len(lib_classes_dict[lib_class][0]) * abstract_method_weight)
        else:
            pre_match_opcodes += lib_classes_dict[lib_class][2]
        LOGGER.debug("Pre-match lib_class: %s", lib_class)
        for apk_class in filter_result[lib_class]:
            LOGGER.debug("apk_class: %s", apk_class)
        LOGGER.debug("-------------------------------")

    # Determine if the pre-match result does not contain
    pre_match_rate = pre_match_opcodes / lib_opcode_num if lib_opcode_num > 0 else 0.0
    if pre_match_rate < lib_similar:
        LOGGER.debug("Pre-match failed library: %s, pre-match rate is: %f", lib_obj.lib_name, pre_match_rate)
        if return_details:
            return {
                "library_name": lib_name,
                "matched": False,
                "score": float(pre_match_rate),
                "similarity": float(pre_match_rate),
                "target_classes": [],
                "stage": "pre_match",
                "pre_match_rate": float(pre_match_rate),
            }
        return {}

    # avg_filter_rate += filter_rate
    # LOGGER.debug("filter_rate: %f", filter_rate)
    # LOGGER.debug("filter_effect: %f", filter_effect)

    # Perform coarse-grained matching
    lib_match_classes, abstract_lib_match_classes, lib_class_match_dict = coarse_match(apk_obj,
                                                                                                       lib_obj,
                                                                                                       filter_result,
                                                                                                       LOGGER)
    for lib_class in lib_class_match_dict:
        if len(lib_class_match_dict[lib_class]) > 1:

            LOGGER.debug("Coarse-grained matching lib_class: %s", lib_class)
            for apk_class in lib_class_match_dict[lib_class]:
                LOGGER.debug("apk_class: %s", apk_class)
                for lib_method in lib_class_match_dict[lib_class][apk_class][0]:
                    LOGGER.debug("apk class function %s → lib class function %s", lib_method,
                                 lib_class_match_dict[lib_class][apk_class][0][lib_method])
        LOGGER.debug("-------------------------------")

    # Calculate the match score of abstract classes or interfaces in the library
    abstract_match_opcodes = 0
    for abstract_class in abstract_lib_match_classes:
        abstract_match_opcodes += (len(lib_classes_dict[abstract_class][0]) * abstract_method_weight)

    # Calculate lib coarse-grained matching score
    lib_coarse_match_opcode_num = 0
    for lib_class in lib_match_classes:
        lib_coarse_match_opcode_num += lib_classes_dict[lib_class][2]
    lib_coarse_match_opcode_num += abstract_match_opcodes

    LOGGER.debug("The coarse-grained unmatched classes in the library are as follows:")
    for lib_class in lib_classes_dict:
        if lib_class not in lib_match_classes and lib_class not in abstract_lib_match_classes:
            # print("FN fine lib_class: ", lib_class)
            LOGGER.debug("lib_class: %s" % lib_class)

    lib_coarse_match_rate = lib_coarse_match_opcode_num / lib_opcode_num if lib_opcode_num > 0 else 0.0
    LOGGER.debug("Number of all opcodes in class matched by lib coarse-graining: %d", lib_coarse_match_opcode_num)
    LOGGER.debug("lib coarse-grained rate: %f", lib_coarse_match_rate)
    LOGGER.debug("Number of matched classes in library: %d", len(lib_match_classes) + len(abstract_lib_match_classes))
    LOGGER.debug("Number of all participating matched classes in the library: %d", len(lib_classes_dict))


    if lib_coarse_match_rate < lib_similar:
        LOGGER.debug("Coarse match failed library: %s, coarse match rate is: %f", lib_obj.lib_name, lib_coarse_match_rate)
        if return_details:
            return {
                "library_name": lib_name,
                "matched": False,
                "score": float(lib_coarse_match_rate),
                "similarity": float(lib_coarse_match_rate),
                "target_classes": [],
                "stage": "coarse_match",
                "pre_match_rate": float(pre_match_rate),
                "coarse_match_rate": float(lib_coarse_match_rate),
            }
        return {}

    # Perform fine-grained matching
    lib_class_match_result = fine_match(apk_obj,
                                        lib_obj,
                                        lib_class_match_dict,
                                        LOGGER)
    for lib_class in lib_class_match_result:
        LOGGER.debug("Fine-grained: library class %s → application class %s", lib_class, lib_class_match_result[lib_class][0])
    LOGGER.debug("The fine-grained unmatched classes in the library are as follows:")
    for lib_class in lib_classes_dict:
        if lib_class not in abstract_lib_match_classes and lib_class not in lib_class_match_result:
            # print("FN fine lib_class: ", lib_class)
            LOGGER.debug("lib_class: %s", lib_class)

    final_match_opcodes = 0
    for lib_class in lib_class_match_result:
        # print("lib_class: ", lib_class, lib_class_match_result[lib_class][0], lib_class_match_result[lib_class][1])
        final_match_opcodes += lib_class_match_result[lib_class][1]
    # print("sum / total num:",final_match_opcodes, lib_opcode_num)
    final_match_opcodes += abstract_match_opcodes

    # Adjust the library similarity threshold according to whether the library to be detected is a pure interface library or not
    min_lib_match = lib_similar
    if lib_obj.interface_lib:
        min_lib_match = 1.0

    final_similarity = (final_match_opcodes / lib_opcode_num) if lib_opcode_num > 0 else 0.0
    temp_list = [final_match_opcodes, lib_opcode_num, final_similarity]
    if final_similarity >= min_lib_match:
        result[lib_obj.lib_name] = temp_list

    if return_details:
        target_classes = sorted({
            str(info[0]).strip()
            for info in lib_class_match_result.values()
            if isinstance(info, (list, tuple)) and len(info) > 0 and str(info[0]).strip()
        })
        return {
            "library_name": lib_name,
            "matched": final_similarity >= min_lib_match,
            "score": float(final_similarity),
            "similarity": float(final_similarity),
            "target_classes": target_classes,
            "stage": "fine_match",
            "pre_match_rate": float(pre_match_rate),
            "coarse_match_rate": float(lib_coarse_match_rate),
            "final_match_opcodes": int(final_match_opcodes),
            "lib_opcode_num": int(lib_opcode_num),
        }
    return result



# Implementing child process detection
def sub_detect_lib(lib,
                   apk,
                   global_apk_info_dict,
                   global_finished_jar_dict,
                   global_lib_info_dict):
    # Test all versions of the same library and return a dictionary of the results (key is the jar name, value is four values)
    logger = setup_logger()
    start_lib = datetime.datetime.now()
    if lib not in global_lib_info_dict:
        logger.info("Library: %s not parsed successfully in previous step, skipped", lib)
        return
    result = detect(global_apk_info_dict[apk], global_lib_info_dict[lib], logger)
    end_lib = datetime.datetime.now()
    logger.info("Detecting libraries: %s complete, time: %d", lib, (end_lib - start_lib).seconds)

    if len(result) != 0:
        global_finished_jar_dict.update(result)


# Implementing subthreads to determine cyclic dependency libraries based on dependencies
def sub_find_loop_dependence_libs(libs, dependence_relation, loop_dependence_libs, shared_lock_loop_libs):
    DG = nx.DiGraph(list(dependence_relation))
    for lib_name in libs:
        try:
            nx.find_cycle(DG, source=lib_name)
            shared_lock_loop_libs.acquire()
            if lib_name not in loop_dependence_libs:
                loop_dependence_libs.append(lib_name)
            shared_lock_loop_libs.release()
        except Exception:
            pass


def monitor_progress(global_running_jar_list, all_libs_num):
    time_sec = 0
    while True:
        finish_num = all_libs_num - len(global_running_jar_list)
        finish_rate = int(finish_num / all_libs_num * 100)
        print('\r' + "current analysis: " + '▇' * (finish_rate // 2) + f'{finish_rate}%', end='')
        if finish_num >= all_libs_num:
            break
        time.sleep(1)
        time_sec += 1


def init_worker():
    logger = logging.getLogger()
    # Remove all handlers associated with the root logger
    handlers = logger.handlers[:]
    for handler in handlers:
        logger.removeHandler(handler)




def _load_or_build_lib_obj(lib_dex_folder: str, lib: str, logger):
    # 扁平化 pickle 名称以支持嵌套目录结构
    flat_lib_name = lib.replace("/", "_").replace("\\", "_")
    lib_pickle_path = os.path.join(pickle_dir, flat_lib_name).replace(".dex", ".pkl")
    try:
        if os.path.exists(lib_pickle_path):
            with open(lib_pickle_path, 'rb') as file:
                return pickle.load(file)
        lib_obj = ThirdLib(lib_dex_folder + "/" + lib, logger)
        pickle.dump(lib_obj, open(lib_pickle_path, 'wb'))
        return lib_obj
    except Exception as e:
        logger.error("Error loading/building lib %s: %s", lib, e)
        try:
            if os.path.exists(lib_pickle_path):
                os.remove(lib_pickle_path)
        except OSError:
            pass
        return None


def _load_pickled_lib_obj(pickle_path: str, logger):
    try:
        setattr(sys.modules.get("__main__"), "_StubThirdLib", _StubThirdLib)
        with open(pickle_path, 'rb') as file:
            return pickle.load(file)
    except Exception as e:
        logger.error("Error loading cached lib pickle %s: %s", pickle_path, e)
        return None


def _build_lib_pickle_task(args):
    lib_dex_folder, lib = args
    logger = setup_logger()
    lib_obj = _load_or_build_lib_obj(lib_dex_folder, lib, logger)
    return lib, lib_obj is not None


def _ensure_apk_descriptor_index(apk_obj) -> bool:
    if getattr(apk_obj, "descriptor_index_version", None) == descriptor_index_version:
        descriptor_index = getattr(apk_obj, "descriptor_index", None)
        if isinstance(descriptor_index, dict):
            return False
    apk_obj.build_descriptor_index()
    return True


def _apk_pickle_paths(apk_name: str) -> tuple[str, str]:
    new_path = os.path.join(apk_pickle_dir, apk_name).replace(".apk", ".pkl")
    legacy_path = os.path.join(pickle_dir, apk_name).replace(".apk", ".pkl")
    return new_path, legacy_path


def _load_or_build_apk_obj(apk_path: str, apk_name: str, logger):
    apk_pickle_path, legacy_apk_pickle_path = _apk_pickle_paths(apk_name)
    source_pickle_path = None
    if os.path.exists(apk_pickle_path):
        source_pickle_path = apk_pickle_path
    elif os.path.exists(legacy_apk_pickle_path):
        source_pickle_path = legacy_apk_pickle_path

    if source_pickle_path:
        with open(source_pickle_path, 'rb') as file:
            apk_obj = pickle.load(file)
        changed = _ensure_apk_descriptor_index(apk_obj)
        if source_pickle_path != apk_pickle_path or changed:
            pickle.dump(apk_obj, open(apk_pickle_path, 'wb'))
        return apk_obj, apk_pickle_path

    apk_obj = Apk(apk_path, logger)
    _ensure_apk_descriptor_index(apk_obj)
    pickle.dump(apk_obj, open(apk_pickle_path, 'wb'))
    return apk_obj, apk_pickle_path


_DETECT_APK_OBJ = None
_DETECT_LOGGER = None


def _init_detect_worker(apk_pickle_path: str):
    global _DETECT_APK_OBJ, _DETECT_LOGGER
    _DETECT_LOGGER = setup_logger()
    with open(apk_pickle_path, 'rb') as file:
        _DETECT_APK_OBJ = pickle.load(file)
    _ensure_apk_descriptor_index(_DETECT_APK_OBJ)


def _extract_family_from_rel_path(rel_path: str) -> str:
    norm = (rel_path or "").replace("\\", "/").strip("/")
    folder = os.path.dirname(norm)
    return folder.replace("/", ".") if folder else ""


def _extract_version_from_rel_path(rel_path: str) -> str:
    filename = os.path.basename(rel_path or "")
    stem = filename[:-4] if filename.endswith(".dex") else filename
    family = _extract_family_from_rel_path(rel_path)
    artifact = family.rsplit(".", 1)[-1] if family else ""
    if artifact:
        for separator in ("-", "_"):
            prefix = artifact + separator
            if stem.startswith(prefix):
                return stem[len(prefix):].strip()
    if "_" in stem:
        return stem.split("_", 1)[1].strip()
    return stem.strip()


_VERSION_PICKLE_PATTERN = re.compile(r"^(?P<prefix>.+?)[_-](?P<version>\d[\w.\-+]*)$")


def _infer_family_from_version_prefix(prefix: str) -> str:
    value = (prefix or "").strip()
    if "_" in value:
        left, _right = value.rsplit("_", 1)
        if "." in left:
            return left
    return value


def _extract_version_from_pickle_stem(pickle_stem: str, family: str) -> str:
    stem = (pickle_stem or "").strip()
    match = _VERSION_PICKLE_PATTERN.match(stem)
    if match:
        return match.group("version")
    prefix = family + "_"
    if stem.startswith(prefix):
        return stem[len(prefix):]
    return stem


def _version_sort_key(version: str):
    key = []
    for part in re.split(r"([0-9]+|[A-Za-z]+)", str(version or "")):
        if not part:
            continue
        if part.isdigit():
            key.append((2, int(part)))
        elif part.isalpha():
            key.append((1, part.lower()))
        else:
            key.append((0, part))
    return tuple(key)


def _match_pickle_family(pickle_stem: str, families: Set[str]) -> Optional[str]:
    base = (pickle_stem or "").strip()
    if base.endswith("_skeleton"):
        base = base[:-len("_skeleton")]
    if base in families:
        return base

    matches = [
        family
        for family in families
        if base == family
        or base.startswith(family + "_")
        or base.replace("_", ".") == family
    ]
    if not matches:
        return None
    return sorted(matches, key=len, reverse=True)[0]


def _extract_skeleton_scope_label(pickle_stem: str, family: str) -> str:
    base = (pickle_stem or "").strip()
    if base.endswith("_skeleton"):
        base = base[:-len("_skeleton")]
    prefix = family + "_"
    if base.startswith(prefix):
        return base[len(prefix):].strip("_")
    return ""


def _classify_skeleton_scope(scope_label: str) -> str:
    label = (scope_label or "").strip("_")
    if not label:
        return "library"
    if label in MODULE_SCOPE_LABELS:
        return "module"
    return "version_range"


def _make_skeleton_entry(family: str, pickle_path: str, cache_name: str) -> dict:
    stem = cache_name[:-4].strip() if cache_name.endswith(".pkl") else cache_name.strip()
    scope_label = _extract_skeleton_scope_label(stem, family)
    scope_type = _classify_skeleton_scope(scope_label)
    return {
        "family": family,
        "pickle_path": pickle_path,
        "cache_name": cache_name,
        "scope_type": scope_type,
        "scope_label": scope_label,
    }


def _index_skeleton_pickles(
    *,
    cache_dir: str,
    families: Set[str],
    logger,
) -> Dict[str, List[dict]]:
    skeletons: Dict[str, List[dict]] = {}
    if not os.path.isdir(cache_dir):
        return skeletons

    for name in sorted(os.listdir(cache_dir)):
        if not name.endswith("_skeleton.pkl"):
            continue
        stem = name[:-4].strip()
        family = _match_pickle_family(stem, families)
        if not family:
            logger.warning("[libhunter] skeleton pickle has no version family: %s", name)
            continue
        entry = _make_skeleton_entry(family, os.path.join(cache_dir, name), name)
        skeletons.setdefault(family, []).append(entry)
    return skeletons


def _index_bucket_pickles(
    *,
    cache_dir: str,
    families: Set[str],
    logger,
) -> Dict[str, Dict[str, str]]:
    buckets: Dict[str, Dict[str, str]] = {}
    if not os.path.isdir(cache_dir):
        return buckets

    for family in sorted(HEAVY_BUCKET_FAMILIES):
        if family not in families:
            continue
        family_dir = os.path.join(cache_dir, family)
        if not os.path.isdir(family_dir):
            continue
        for name in sorted(os.listdir(family_dir)):
            if not name.endswith(".pkl"):
                continue
            bucket = name[:-4].strip()
            if not bucket:
                logger.warning("[libhunter] empty bucket pickle name under %s: %s", family, name)
                continue
            buckets.setdefault(family, {})[bucket] = os.path.join(family_dir, name)
    return buckets


def _index_version_pickles(
    *,
    cache_dir: str,
    lib_groups: Dict[str, List[str]],
    logger,
) -> Dict[str, List[dict]]:
    by_family: Dict[str, Dict[str, dict]] = {}

    for family, versions in lib_groups.items():
        for rel_path in versions:
            version = _extract_version_from_rel_path(rel_path)
            by_family.setdefault(family, {})[version] = {
                "family": family,
                "version": version,
                "rel_path": rel_path,
                "pickle_path": None,
                "source": "dex",
            }

    if os.path.isdir(cache_dir):
        known_families = set(by_family.keys())
        for name in sorted(os.listdir(cache_dir)):
            if not name.endswith(".pkl") or name.endswith("_skeleton.pkl"):
                continue

            stem = name[:-4].strip()
            match = _VERSION_PICKLE_PATTERN.match(stem)
            if match:
                family = _match_pickle_family(match.group("prefix"), known_families)
                if not family:
                    family = _infer_family_from_version_prefix(match.group("prefix"))
                version = match.group("version")
            else:
                family = _match_pickle_family(stem, known_families)
                if not family:
                    continue
                version = _extract_version_from_pickle_stem(stem, family)

            by_family.setdefault(family, {})[version] = {
                "family": family,
                "version": version,
                "rel_path": by_family.get(family, {}).get(version, {}).get("rel_path"),
                "pickle_path": os.path.join(cache_dir, name),
                "source": "pickle",
            }

    return {
        family: sorted(rows.values(), key=lambda item: item.get("version", ""))
        for family, rows in by_family.items()
        if rows
    }

def _detect_one_lib_task(args):
    lib_dex_folder, lib = args
    logger = _DETECT_LOGGER if _DETECT_LOGGER is not None else setup_logger()
    if _DETECT_APK_OBJ is None:
        return None

    lib_obj = _load_or_build_lib_obj(lib_dex_folder, lib, logger)
    if lib_obj is None:
        return None

    try:
        result = detect(_DETECT_APK_OBJ, lib_obj, logger)
    except Exception as e:
        logger.error("Error in detect lib %s: %s", lib, e)
        return None
    return result if len(result) != 0 else None


def _detect_one_lib_detail_task(args):
    logger = _DETECT_LOGGER if _DETECT_LOGGER is not None else setup_logger()
    if _DETECT_APK_OBJ is None:
        return None

    if isinstance(args, dict):
        lib_dex_folder = args.get("lib_dex_folder", "")
        lib = args.get("rel_path") or ""
        family = str(args.get("family", "")).strip()
        selected_version = str(args.get("version", "")).strip()
        pickle_path = args.get("pickle_path")
        if pickle_path:
            lib_obj = _load_pickled_lib_obj(str(pickle_path), logger)
        else:
            lib_obj = _load_or_build_lib_obj(lib_dex_folder, str(lib), logger)
    else:
        lib_dex_folder, lib = args
        family = _extract_family_from_rel_path(lib)
        selected_version = _extract_version_from_rel_path(lib)
        lib_obj = _load_or_build_lib_obj(lib_dex_folder, lib, logger)

    if lib_obj is None:
        return None

    try:
        detail = detect(_DETECT_APK_OBJ, lib_obj, logger, return_details=True)
    except Exception as e:
        logger.error("Error in stage2 detect lib %s: %s", lib, e)
        return None

    if not isinstance(detail, dict):
        return None

    lib_name = str(detail.get("library_name", "")).strip() or str(getattr(lib_obj, "lib_name", "")).strip() or str(lib)
    return {
        "library_family": family,
        "selected_version": selected_version,
        "lib": lib_name,
        "similarity": float(detail.get("similarity", detail.get("score", 0.0)) or 0.0),
        "matched": bool(detail.get("matched", False)),
        "target_classes": sorted({
            str(cls).strip()
            for cls in (detail.get("target_classes", []) or [])
            if str(cls).strip()
        }),
    }


def _detect_one_skeleton_detail_task(args):
    if isinstance(args, dict):
        family = str(args.get("family", "")).strip()
        skeleton_pickle_path = str(args.get("pickle_path", "")).strip()
        cache_name = str(args.get("cache_name", "")).strip()
        scope_type = str(args.get("scope_type", "library")).strip() or "library"
        scope_label = str(args.get("scope_label", "")).strip()
    else:
        family, skeleton_pickle_path = args
        cache_name = os.path.basename(str(skeleton_pickle_path))
        scope_label = ""
        scope_type = "library"
    logger = _DETECT_LOGGER if _DETECT_LOGGER is not None else setup_logger()
    if _DETECT_APK_OBJ is None:
        return None

    lib_obj = _load_pickled_lib_obj(skeleton_pickle_path, logger)
    if lib_obj is None:
        return None

    try:
        detail = detect(_DETECT_APK_OBJ, lib_obj, logger, return_details=True)
    except Exception as e:
        logger.error("Error in stage1 skeleton detect %s: %s", skeleton_pickle_path, e)
        return None

    if not isinstance(detail, dict):
        return None

    lib_name = (
        str(detail.get("library_name", "")).strip()
        or str(getattr(lib_obj, "lib_name", "")).strip()
        or str(family)
    )
    return {
        "library_family": family,
        "selected_version": "_skeleton",
        "cache_name": cache_name,
        "scope_type": scope_type,
        "scope_label": scope_label,
        "lib": lib_name,
        "similarity": float(detail.get("similarity", detail.get("score", 0.0)) or 0.0),
        "matched": bool(detail.get("matched", False)),
        "target_classes": sorted({
            str(cls).strip()
            for cls in (detail.get("target_classes", []) or [])
            if str(cls).strip()
        }),
    }


def _detect_one_bucket_detail_task(args):
    family, bucket, bucket_pickle_path = args
    logger = _DETECT_LOGGER if _DETECT_LOGGER is not None else setup_logger()
    if _DETECT_APK_OBJ is None:
        return None

    lib_obj = _load_pickled_lib_obj(bucket_pickle_path, logger)
    if lib_obj is None:
        return None

    try:
        detail = detect(_DETECT_APK_OBJ, lib_obj, logger, return_details=True)
    except Exception as e:
        logger.error("Error in bucket detect %s: %s", bucket_pickle_path, e)
        return None

    if not isinstance(detail, dict):
        return None

    lib_name = (
        str(detail.get("library_name", "")).strip()
        or str(getattr(lib_obj, "lib_name", "")).strip()
        or f"{family}_{bucket}_bucket"
    )
    bucket_versions = [
        str(version).strip()
        for version in (getattr(lib_obj, "bucket_versions", []) or [])
        if str(version).strip()
    ]
    return {
        "library_family": family,
        "bucket": bucket,
        "bucket_versions": bucket_versions,
        "lib": lib_name,
        "similarity": float(detail.get("similarity", detail.get("score", 0.0)) or 0.0),
        "matched": bool(detail.get("matched", False)),
        "target_classes": sorted({
            str(cls).strip()
            for cls in (detail.get("target_classes", []) or [])
            if str(cls).strip()
        }),
    }


def _detect_stage1_bucket_pipeline_task(args):
    kind, payload = args
    if kind == "skeleton":
        return kind, _detect_one_skeleton_detail_task(payload)
    if kind == "bucket":
        return kind, _detect_one_bucket_detail_task(payload)
    return kind, None


def _run_detection_for_versions(
    *,
    lib_dex_folder: str,
    apk_pickle_path: str,
    versions: List[dict],
    thread_num: int,
    apk_label: str,
    logger,
) -> List[dict]:
    if not versions:
        return []

    detect_tasks = []
    seen: Set[tuple[str, str]] = set()
    for entry in versions:
        family = str(entry.get("family", "")).strip()
        version = str(entry.get("version", "")).strip()
        key = (family, version)
        if key in seen:
            continue
        seen.add(key)
        task = dict(entry)
        task["lib_dex_folder"] = lib_dex_folder
        detect_tasks.append(task)
    detect_tasks.sort(key=lambda item: (item.get("family", ""), item.get("version", "")))
    details: List[dict] = []
    try:
        with Pool(
            processes=thread_num,
            initializer=_init_detect_worker,
            initargs=(apk_pickle_path,),
        ) as pool:
            for row in tqdm(
                pool.imap_unordered(_detect_one_lib_detail_task, detect_tasks),
                total=len(detect_tasks),
                desc=f"FullScan {apk_label}",
                colour='blue',
            ):
                if row:
                    details.append(row)
    except (PermissionError, OSError, RuntimeError) as e:
        logger.warning("Pool init failed in full scan, fallback to serial mode: %s", e)
        _init_detect_worker(apk_pickle_path)
        for task in tqdm(
            detect_tasks,
            total=len(detect_tasks),
            desc=f"FullScan {apk_label} (serial)",
            colour='blue',
        ):
            row = _detect_one_lib_detail_task(task)
            if row:
                details.append(row)
    return details


def _run_detection_for_buckets(
    *,
    apk_pickle_path: str,
    buckets: Dict[str, Dict[str, str]],
    thread_num: int,
    apk_label: str,
    logger,
) -> List[dict]:
    detect_tasks = []
    for family, family_buckets in sorted(buckets.items()):
        for bucket, bucket_pickle_path in sorted(family_buckets.items()):
            detect_tasks.append((family, bucket, bucket_pickle_path))
    if not detect_tasks:
        return []

    details: List[dict] = []
    try:
        with Pool(
            processes=thread_num,
            initializer=_init_detect_worker,
            initargs=(apk_pickle_path,),
        ) as pool:
            for row in tqdm(
                pool.imap_unordered(_detect_one_bucket_detail_task, detect_tasks),
                total=len(detect_tasks),
                desc=f"Bucket {apk_label}",
                colour='magenta',
            ):
                if row:
                    details.append(row)
    except (PermissionError, OSError, RuntimeError) as e:
        logger.warning("Pool init failed in bucket scan, fallback to serial mode: %s", e)
        _init_detect_worker(apk_pickle_path)
        for task in tqdm(
            detect_tasks,
            total=len(detect_tasks),
            desc=f"Bucket {apk_label} (serial)",
            colour='magenta',
        ):
            row = _detect_one_bucket_detail_task(task)
            if row:
                details.append(row)
    return details


def _run_detection_for_skeletons(
    *,
    apk_pickle_path: str,
    skeletons: Dict[str, List[dict]],
    thread_num: int,
    apk_label: str,
    logger,
) -> List[dict]:
    if not skeletons:
        return []

    detect_tasks = sorted(
        [
            dict(entry)
            for entries in skeletons.values()
            for entry in entries
        ],
        key=_skeleton_pipeline_sort_key,
    )
    details: List[dict] = []
    try:
        with Pool(
            processes=thread_num,
            initializer=_init_detect_worker,
            initargs=(apk_pickle_path,),
        ) as pool:
            for row in tqdm(
                pool.imap_unordered(_detect_one_skeleton_detail_task, detect_tasks),
                total=len(detect_tasks),
                desc=f"Stage1 {apk_label}",
                colour='cyan',
            ):
                if row:
                    details.append(row)
    except (PermissionError, OSError, RuntimeError) as e:
        logger.warning("Pool init failed in skeleton scan, fallback to serial mode: %s", e)
        _init_detect_worker(apk_pickle_path)
        for task in tqdm(
            detect_tasks,
            total=len(detect_tasks),
            desc=f"Stage1 {apk_label} (serial)",
            colour='cyan',
        ):
            row = _detect_one_skeleton_detail_task(task)
            if row:
                details.append(row)
    return details


def _skeleton_pipeline_sort_key(item):
    if isinstance(item, dict):
        family = str(item.get("family", "")).strip()
        pickle_path = str(item.get("pickle_path", "")).strip()
    else:
        family, pickle_path = item
    try:
        size = os.path.getsize(pickle_path)
    except OSError:
        size = 0
    if family in HEAVY_BUCKET_PRIORITY:
        return (0, HEAVY_BUCKET_PRIORITY.index(family), -size, family)
    return (1, 0, -size, family)


def _run_stage1_bucket_pipeline(
    *,
    apk_pickle_path: str,
    skeletons: Dict[str, List[dict]],
    buckets: Dict[str, Dict[str, str]],
    thread_num: int,
    apk_label: str,
    logger,
) -> tuple[List[dict], List[dict], dict]:
    if not skeletons:
        return [], [], {
            "stage1_time": 0,
            "bucket_time": 0,
            "bucket_families": 0,
            "bucket_pickles": 0,
            "pipeline_time": 0,
        }

    start_time = datetime.datetime.now()
    stage1_done_at = None
    bucket_start_at = None
    bucket_done_at = None

    skeleton_tasks = [
        dict(entry)
        for entries in skeletons.values()
        for entry in entries
    ]
    skeleton_pending = deque(sorted(skeleton_tasks, key=_skeleton_pipeline_sort_key))
    bucket_pending = deque()
    active = []
    active_counts = {"skeleton": 0, "bucket": 0}
    skeleton_details: List[dict] = []
    bucket_details: List[dict] = []
    bucket_families_scheduled: Set[str] = set()
    scheduled_bucket_pickles = 0
    completed_skeletons = 0
    completed_buckets = 0

    # Keep some workers on Stage1 while it still has pending work, but let
    # matched heavy families start bucket detection without waiting for all
    # skeletons to finish.
    bucket_slots_while_stage1_runs = max(1, thread_num // 2)
    if thread_num > 1:
        bucket_slots_while_stage1_runs = min(bucket_slots_while_stage1_runs, thread_num - 1)

    def _submit(pool, kind, payload):
        active.append((pool.apply_async(_detect_stage1_bucket_pipeline_task, ((kind, payload),)), kind, payload))
        active_counts[kind] += 1

    def _submit_available(pool):
        while len(active) < thread_num:
            has_stage1_work = bool(skeleton_pending) or active_counts["skeleton"] > 0
            bucket_limit = bucket_slots_while_stage1_runs if has_stage1_work else thread_num
            if bucket_pending and active_counts["bucket"] < bucket_limit:
                _submit(pool, "bucket", bucket_pending.popleft())
            elif skeleton_pending:
                _submit(pool, "skeleton", skeleton_pending.popleft())
            elif bucket_pending:
                _submit(pool, "bucket", bucket_pending.popleft())
            else:
                break

    stage1_bar = tqdm(total=len(skeleton_tasks), desc=f"Stage1 {apk_label}", colour='cyan')
    bucket_bar = tqdm(total=0, desc=f"Bucket {apk_label}", colour='magenta')
    try:
        with Pool(
            processes=thread_num,
            initializer=_init_detect_worker,
            initargs=(apk_pickle_path,),
        ) as pool:
            _submit_available(pool)
            while active:
                ready_indexes = [index for index, (result, _kind, _payload) in enumerate(active) if result.ready()]
                if not ready_indexes:
                    time.sleep(0.1)
                    continue

                for index in reversed(ready_indexes):
                    result, kind, payload = active.pop(index)
                    active_counts[kind] -= 1
                    try:
                        result_kind, row = result.get()
                    except Exception as e:
                        logger.error("[libhunter] %s pipeline task failed: %s", kind, e)
                        result_kind, row = kind, None

                    if result_kind == "skeleton":
                        completed_skeletons += 1
                        stage1_bar.update(1)
                        if row:
                            skeleton_details.append(row)
                            family = str(row.get("library_family", "")).strip()
                            if (
                                bool(row.get("matched", False))
                                and family in HEAVY_BUCKET_FAMILIES
                                and family not in bucket_families_scheduled
                                and buckets.get(family)
                            ):
                                bucket_families_scheduled.add(family)
                                family_bucket_tasks = [
                                    (family, bucket, bucket_pickle_path)
                                    for bucket, bucket_pickle_path in sorted(buckets.get(family, {}).items())
                                ]
                                if family_bucket_tasks:
                                    if bucket_start_at is None:
                                        bucket_start_at = datetime.datetime.now()
                                    scheduled_bucket_pickles += len(family_bucket_tasks)
                                    bucket_pending.extend(family_bucket_tasks)
                                    bucket_bar.total += len(family_bucket_tasks)
                                    bucket_bar.refresh()
                        if completed_skeletons == len(skeleton_tasks) and stage1_done_at is None:
                            stage1_done_at = datetime.datetime.now()
                    elif result_kind == "bucket":
                        completed_buckets += 1
                        bucket_bar.update(1)
                        if row:
                            bucket_details.append(row)
                        if scheduled_bucket_pickles and completed_buckets == scheduled_bucket_pickles:
                            bucket_done_at = datetime.datetime.now()

                _submit_available(pool)
    except (PermissionError, OSError, RuntimeError) as e:
        logger.warning("Pool init failed in stage1/bucket pipeline, fallback to serial mode: %s", e)
        _init_detect_worker(apk_pickle_path)
        for task in sorted(skeleton_tasks, key=_skeleton_pipeline_sort_key):
            row = _detect_one_skeleton_detail_task(task)
            completed_skeletons += 1
            stage1_bar.update(1)
            if row:
                skeleton_details.append(row)
                family = str(row.get("library_family", "")).strip()
                if (
                    bool(row.get("matched", False))
                    and family in HEAVY_BUCKET_FAMILIES
                    and family not in bucket_families_scheduled
                    and buckets.get(family)
                ):
                    bucket_families_scheduled.add(family)
                    if bucket_start_at is None:
                        bucket_start_at = datetime.datetime.now()
                    family_bucket_tasks = [
                        (family, bucket, bucket_pickle_path)
                        for bucket, bucket_pickle_path in sorted(buckets.get(family, {}).items())
                    ]
                    scheduled_bucket_pickles += len(family_bucket_tasks)
                    bucket_bar.total += len(family_bucket_tasks)
                    bucket_bar.refresh()
                    for bucket_task in family_bucket_tasks:
                        bucket_row = _detect_one_bucket_detail_task(bucket_task)
                        completed_buckets += 1
                        bucket_bar.update(1)
                        if bucket_row:
                            bucket_details.append(bucket_row)
        stage1_done_at = datetime.datetime.now()
        if scheduled_bucket_pickles:
            bucket_done_at = datetime.datetime.now()
    finally:
        stage1_bar.close()
        bucket_bar.close()

    end_time = datetime.datetime.now()
    if stage1_done_at is None:
        stage1_done_at = end_time
    if scheduled_bucket_pickles and bucket_done_at is None:
        bucket_done_at = end_time

    stats = {
        "stage1_time": int((stage1_done_at - start_time).total_seconds()),
        "bucket_time": int((bucket_done_at - bucket_start_at).total_seconds()) if bucket_start_at and bucket_done_at else 0,
        "bucket_families": len(bucket_families_scheduled),
        "bucket_pickles": scheduled_bucket_pickles,
        "pipeline_time": int((end_time - start_time).total_seconds()),
    }
    return skeleton_details, bucket_details, stats


def _extract_candidate_families(skeleton_details: List[dict]) -> List[str]:
    candidates = sorted({
        str(row.get("library_family", "")).strip()
        for row in skeleton_details
        if bool(row.get("matched", False)) and str(row.get("library_family", "")).strip()
    })
    return candidates


def _extract_candidate_scopes(skeleton_details: List[dict]) -> List[dict]:
    scopes: list[dict] = []
    seen: set[tuple[str, str, str, str]] = set()
    for row in skeleton_details:
        if not bool(row.get("matched", False)):
            continue
        family = str(row.get("library_family", "")).strip()
        if not family:
            continue
        scope_type = str(row.get("scope_type", "library")).strip() or "library"
        scope_label = str(row.get("scope_label", "")).strip()
        cache_name = str(row.get("cache_name", "")).strip()
        key = (family, scope_type, scope_label, cache_name)
        if key in seen:
            continue
        seen.add(key)
        scopes.append({
            "family": family,
            "scope_type": scope_type,
            "scope_label": scope_label,
            "cache_name": cache_name,
            "similarity": float(row.get("similarity", 0.0) or 0.0),
        })
    scopes.sort(key=lambda item: (
        item.get("family", ""),
        item.get("scope_type", ""),
        item.get("scope_label", ""),
        item.get("cache_name", ""),
    ))
    return scopes


def _version_major(version: str) -> str:
    match = re.search(r"\d+", str(version or ""))
    return match.group(0) if match else ""


def _version_numbers(version: str) -> list[int]:
    return [int(value) for value in re.findall(r"\d+", str(version or ""))]


def _version_matches_scope_label(version: str, scope_label: str) -> bool:
    label = (scope_label or "").strip("_").lower()
    if not label:
        return True

    numbers = _version_numbers(version)
    if not numbers:
        return False

    major_match = re.fullmatch(r"(\d+)x(?:_android)?", label)
    if major_match:
        return numbers[0] == int(major_match.group(1))

    android_match = re.fullmatch(r"android_(\d+)_(\d+)", label)
    if android_match and len(numbers) >= 2:
        return numbers[0] == int(android_match.group(1)) and numbers[1] == int(android_match.group(2))

    plus_match = re.fullmatch(r"(\d+)_(\d+)_plus", label)
    if plus_match and len(numbers) >= 2:
        major = int(plus_match.group(1))
        minor = int(plus_match.group(2))
        return numbers[0] == major and numbers[1] >= minor

    range_match = re.fullmatch(r"(\d+)_(\d+)_to_(\d+)_(\d+)", label)
    if range_match and len(numbers) >= 2:
        start = (int(range_match.group(1)), int(range_match.group(2)))
        end = (int(range_match.group(3)), int(range_match.group(4)))
        current = (numbers[0], numbers[1])
        return start <= current <= end

    exact_major_minor = re.fullmatch(r"(\d+)_(\d+)", label)
    if exact_major_minor and len(numbers) >= 2:
        return numbers[0] == int(exact_major_minor.group(1)) and numbers[1] == int(exact_major_minor.group(2))

    exact_major_minor_patch = re.fullmatch(r"(\d+)_(\d+)_(\d+)", label)
    if exact_major_minor_patch and len(numbers) >= 3:
        return (
            numbers[0] == int(exact_major_minor_patch.group(1))
            and numbers[1] == int(exact_major_minor_patch.group(2))
            and numbers[2] == int(exact_major_minor_patch.group(3))
        )

    early_late_labels = {
        "early_mid",
        "late",
    }
    if label in early_late_labels:
        return True

    return False


def _select_versions_for_scope(scope: dict, version_index: Dict[str, List[dict]]) -> List[dict]:
    family = str(scope.get("family", "")).strip()
    scope_type = str(scope.get("scope_type", "library")).strip() or "library"
    scope_label = str(scope.get("scope_label", "")).strip()
    family_versions = version_index.get(family, [])

    if scope_type in {"library", "module"}:
        return list(family_versions)
    if scope_type != "version_range":
        return list(family_versions)

    matched = [
        entry
        for entry in family_versions
        if _version_matches_scope_label(str(entry.get("version", "")), scope_label)
    ]
    return matched or list(family_versions)


def _aggregate_best_by_family(version_details: List[dict]) -> List[dict]:
    by_family: Dict[str, List[dict]] = {}
    for row in version_details:
        family = str(row.get("library_family", "")).strip()
        if not family:
            continue
        by_family.setdefault(family, []).append(row)

    detections: List[dict] = []
    for rows in by_family.values():
        max_similarity = max(float(item.get("similarity", 0.0)) for item in rows)
        tied_rows = [
            item
            for item in rows
            if float(item.get("similarity", 0.0)) == max_similarity
        ]
        tied_rows.sort(key=lambda item: _version_sort_key(str(item.get("selected_version", ""))))
        best = tied_rows[(len(tied_rows) - 1) // 2]
        if bool(best.get("matched", False)):
            detections.append({
                "lib": best.get("lib", ""),
                "similarity": float(best.get("similarity", 0.0)),
                "target_classes": list(best.get("target_classes", [])),
            })

    detections.sort(key=lambda item: item["similarity"], reverse=True)
    return detections


def _select_best_bucket_by_family(bucket_details: List[dict]) -> Dict[str, dict]:
    best_by_family: Dict[str, dict] = {}
    for row in bucket_details:
        if not bool(row.get("matched", False)):
            continue
        family = str(row.get("library_family", "")).strip()
        if not family:
            continue
        current = best_by_family.get(family)
        if current is None or float(row.get("similarity", 0.0)) > float(current.get("similarity", 0.0)):
            best_by_family[family] = row
    return best_by_family


def _write_libhunter_reports(
    *,
    output_folder: str,
    apk_name: str,
    detections: List[dict],
    apk_time_seconds: int,
) -> None:
    txt_path = os.path.join(output_folder, apk_name + ".txt")
    with open(txt_path, "w", encoding="utf-8") as result:
        for det in detections:
            result.write("lib: " + str(det.get("lib", "")) + "\n")
            result.write("similarity: " + str(det.get("similarity", 0.0)) + "\n")
            target_classes = list(det.get("target_classes", []))
            if target_classes:
                result.write("Class Names/Packages: [" + ", ".join(target_classes) + "]\n")
            result.write("\n")
        result.write("time: " + str(apk_time_seconds) + "s")

    json_path = os.path.join(output_folder, apk_name + ".json")
    payload = {
        "apk": apk_name,
        "detections": detections,
        "time_seconds": apk_time_seconds,
    }
    with open(json_path, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, ensure_ascii=False, indent=2)


def _search_libs_in_app_multiprocess(lib_dex_folder=None,
                                     apk_folder=None,
                                     output_folder='outputs',
                                     processes=None):
    """LibHunter full-scan pipeline in stable multiprocessing mode."""
    to_analysze_apks = os.listdir(apk_folder)
    print("num of apk to analyze: ", len(to_analysze_apks))
    LOGGER = setup_logger()

    thread_num = processes if processes is not None else max_thread_num
    thread_num = max(1, int(thread_num))
    LOGGER.info("Analyzing maximum number of cpu used: %d", thread_num)
    LOGGER.info("Multiprocess stable mode enabled (no Manager shared dict)")

    LOGGER.debug("Starting to extract all library information...")
    time_start = datetime.datetime.now()

    lib_groups = build_lib_groups(lib_dex_folder)
    version_index = _index_version_pickles(
        cache_dir=pickle_dir,
        lib_groups=lib_groups,
        logger=LOGGER,
    )
    skeleton_pickles = _index_skeleton_pickles(
        cache_dir=skeleton_pickle_dir,
        families=set(version_index.keys()),
        logger=LOGGER,
    )
    bucket_pickles = _index_bucket_pickles(
        cache_dir=bucket_pickle_dir,
        families=set(version_index.keys()),
        logger=LOGGER,
    )
    libs_list = [lib for versions in lib_groups.values() for lib in versions]
    libs = list(libs_list)
    random.shuffle(libs)

    should_prebuild_all_versions = not skeleton_pickles or len(to_analysze_apks) == 0
    decompile_thread_num = min(thread_num, len(libs)) if len(libs) > 0 else 1
    if len(libs) > 0 and should_prebuild_all_versions:
        tasks = [(lib_dex_folder, lib) for lib in libs]
        try:
            with Pool(processes=decompile_thread_num, initializer=init_worker) as pool:
                for _ in pool.imap_unordered(_build_lib_pickle_task, tasks):
                    pass
        except (PermissionError, OSError, RuntimeError) as e:
            LOGGER.warning("Pool init failed in prebuild stage, fallback to serial mode: %s", e)
            for task in tasks:
                _build_lib_pickle_task(task)
    elif len(libs) > 0:
        LOGGER.info("[libhunter] skeleton mode enabled; version pickles load on demand in stage2")

    print("All TPL information extracted ...")
    time_end = datetime.datetime.now()
    LOGGER.debug("All libraries extracted (multiprocess stable), time: %d", (time_end - time_start).seconds)

    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    all_libs_num = len(libs_list)
    LOGGER.info("The number of libraries analyzed this time is: %d", all_libs_num)
    LOGGER.info(
        "[libhunter] version families=%d skeleton families=%d skeleton pickles=%d bucket families=%d",
        len(version_index),
        len(skeleton_pickles),
        sum(len(entries) for entries in skeleton_pickles.values()),
        len(bucket_pickles),
    )

    for apk in os.listdir(apk_folder):
        print("start analyzing: ", apk)
        LOGGER.info("Starting analysis: %s", apk)
        apk_time_start = datetime.datetime.now()

        try:
            apk_obj, apk_pickle_path = _load_or_build_apk_obj(
                apk_folder + "/" + apk,
                apk,
                LOGGER,
            )
        except Exception as e:
            LOGGER.error("Error in decompile apk: %s", e)
            continue

        candidate_versions: List[dict] = []
        candidate_families: List[str] = []
        if skeleton_pickles:
            skeleton_details, bucket_details, pipeline_stats = _run_stage1_bucket_pipeline(
                apk_pickle_path=apk_pickle_path,
                skeletons=skeleton_pickles,
                buckets=bucket_pickles,
                thread_num=thread_num,
                apk_label=apk,
                logger=LOGGER,
            )
            candidate_families = _extract_candidate_families(skeleton_details)
            LOGGER.info(
                "[libhunter] %s stage1_skeletons=%d candidate_families=%d stage1_time=%ss pipeline_time=%ss",
                apk,
                sum(len(entries) for entries in skeleton_pickles.values()),
                len(candidate_families),
                pipeline_stats.get("stage1_time", 0),
                pipeline_stats.get("pipeline_time", 0),
            )
            if not candidate_families:
                LOGGER.info("[libhunter] %s no stage1 candidates; skip stage2 version scan", apk)
                apk_time_end = datetime.datetime.now()
                apk_time = (apk_time_end - apk_time_start).seconds
                _write_libhunter_reports(
                    output_folder=output_folder,
                    apk_name=apk,
                    detections=[],
                    apk_time_seconds=apk_time,
                )
                LOGGER.info("Current apk analysis time: %d (in seconds)", apk_time)
                continue

            candidate_scopes = _extract_candidate_scopes(skeleton_details)
            version_lookup: Dict[str, Dict[str, dict]] = {
                family: {
                    str(entry.get("version", "")).strip(): entry
                    for entry in entries
                    if str(entry.get("version", "")).strip()
                }
                for family, entries in version_index.items()
            }
            seen_versions: Set[tuple[str, str]] = set()

            def _add_candidate_version(version_entry: dict) -> None:
                key = (
                    str(version_entry.get("family", "")).strip(),
                    str(version_entry.get("version", "")).strip(),
                )
                if key in seen_versions:
                    return
                seen_versions.add(key)
                candidate_versions.append(version_entry)

            heavy_candidates = [
                family
                for family in candidate_families
                if family in HEAVY_BUCKET_FAMILIES
            ]
            bucket_candidates = {
                family: bucket_pickles.get(family, {})
                for family in heavy_candidates
                if bucket_pickles.get(family)
            }
            best_buckets: Dict[str, dict] = _select_best_bucket_by_family(bucket_details)
            if bucket_candidates:
                LOGGER.info(
                    "[libhunter] %s bucket_families=%d bucket_pickles=%d bucket_matches=%d bucket_time=%ss",
                    apk,
                    pipeline_stats.get("bucket_families", 0),
                    pipeline_stats.get("bucket_pickles", 0),
                    len(best_buckets),
                    pipeline_stats.get("bucket_time", 0),
                )

            for family in heavy_candidates:
                if family not in bucket_pickles:
                    LOGGER.warning("[libhunter] %s heavy family has no bucket pickles: %s", apk, family)
                elif family not in best_buckets:
                    LOGGER.info("[libhunter] %s no bucket matched for %s; skip family versions", apk, family)

            for family in candidate_families:
                if family in HEAVY_BUCKET_FAMILIES:
                    best_bucket = best_buckets.get(family)
                    if not best_bucket:
                        continue
                    missing_versions = []
                    for version in best_bucket.get("bucket_versions", []):
                        version_entry = version_lookup.get(family, {}).get(str(version).strip())
                        if version_entry:
                            _add_candidate_version(version_entry)
                        else:
                            missing_versions.append(str(version).strip())
                    if missing_versions:
                        LOGGER.warning(
                            "[libhunter] %s bucket %s/%s has missing version pickles: %s",
                            apk,
                            family,
                            best_bucket.get("bucket", ""),
                            ", ".join(missing_versions),
                        )
                    LOGGER.info(
                        "[libhunter] %s bucket selected family=%s bucket=%s similarity=%.6f versions=%d",
                        apk,
                        family,
                        best_bucket.get("bucket", ""),
                        float(best_bucket.get("similarity", 0.0)),
                        len(best_bucket.get("bucket_versions", [])),
                    )
                    continue

                family_scopes = [
                    scope
                    for scope in candidate_scopes
                    if str(scope.get("family", "")).strip() == family
                ]
                if not family_scopes:
                    for version_entry in version_index.get(family, []):
                        _add_candidate_version(version_entry)
                    continue

                before_count = len(candidate_versions)
                for scope in family_scopes:
                    selected_versions = _select_versions_for_scope(scope, version_index)
                    for version_entry in selected_versions:
                        _add_candidate_version(version_entry)
                    LOGGER.info(
                        "[libhunter] %s scope selected family=%s cache=%s scope=%s/%s similarity=%.6f versions=%d",
                        apk,
                        family,
                        scope.get("cache_name", ""),
                        scope.get("scope_type", ""),
                        scope.get("scope_label", ""),
                        float(scope.get("similarity", 0.0)),
                        len(selected_versions),
                    )
                LOGGER.info(
                    "[libhunter] %s family=%s scoped candidate versions added=%d",
                    apk,
                    family,
                    len(candidate_versions) - before_count,
                )
        else:
            LOGGER.warning(
                "[libhunter] no skeleton pickles found in %s; fallback to full version scan",
                skeleton_pickle_dir,
            )
            candidate_versions = [
                entry
                for rows in version_index.values()
                for entry in rows
            ]

        if not candidate_versions:
            LOGGER.warning("[libhunter] no candidate versions found under %s", lib_dex_folder)
            apk_time_end = datetime.datetime.now()
            apk_time = (apk_time_end - apk_time_start).seconds
            _write_libhunter_reports(
                output_folder=output_folder,
                apk_name=apk,
                detections=[],
                apk_time_seconds=apk_time,
            )
            continue

        scan_start = datetime.datetime.now()
        version_details = _run_detection_for_versions(
            lib_dex_folder=lib_dex_folder,
            apk_pickle_path=apk_pickle_path,
            versions=candidate_versions,
            thread_num=thread_num,
            apk_label=apk,
            logger=LOGGER,
        )
        scan_time = (datetime.datetime.now() - scan_start).seconds
        detections = _aggregate_best_by_family(version_details)

        LOGGER.info(
            "[libhunter] %s candidate_families=%d candidate_versions=%d detections=%d detect_time=%ss",
            apk,
            len(candidate_families) if skeleton_pickles else len(version_index),
            len(candidate_versions),
            len(detections),
            scan_time,
        )

        apk_time_end = datetime.datetime.now()
        apk_time = (apk_time_end - apk_time_start).seconds
        _write_libhunter_reports(
            output_folder=output_folder,
            apk_name=apk,
            detections=detections,
            apk_time_seconds=apk_time,
        )
        LOGGER.info("Current apk analysis time: %d (in seconds)", apk_time)


def search_libs_in_app(lib_dex_folder=None,
                       apk_folder=None,
                       output_folder='outputs',
                       processes=None):
    return _search_libs_in_app_multiprocess(
        lib_dex_folder=lib_dex_folder,
        apk_folder=apk_folder,
        output_folder=output_folder,
        processes=processes,
    )


def sub_detect_apk(apk,
                   lib_obj,
                   apk_folder,
                   global_result_dict):
    apk_obj = Apk(apk_folder + "/" + apk)
    result = detect(apk_obj, lib_obj)

    if len(result) != 0:
        global_result_dict[apk] = str(result[lib_obj.lib_name][2])


def search_lib_in_app(lib_dex_folder=None,
                      apk_folder=None,
                      output_folder='outputs',
                      processes=None):
    LOGGER = setup_logger()
    # Setting the number of cpu's analyzed
    thread_num = processes if processes != None else max_thread_num
    LOGGER.info("Analyzing the number of cpu used: %d", thread_num)

    LOGGER.debug("Starting to extract library information...")
    time_start = datetime.datetime.now()

    lib_path = ""
    for lib in os.listdir(lib_dex_folder):
        lib_path = lib_dex_folder + "/" + lib
    lib_obj = ThirdLib(lib_path)

    time_end = datetime.datetime.now()
    LOGGER.debug("Library extraction complete, time: %d", (time_end - time_start).seconds)

    global_apk_list = multiprocessing.Manager().list()
    for apk in os.listdir(apk_folder):
        global_apk_list.append(apk)
    global_result_dict = multiprocessing.Manager().dict()
    share_lock_apk = multiprocessing.Manager().Lock()
    share_lock_result = multiprocessing.Manager().Lock()

    print("Start detection ...")
    processes_list_detect = []
    for i in range(1, thread_num + 1):
        process_name = str(i)
        thread = multiprocessing.Process(target=sub_detect_apk, args=(process_name,
                                                                      lib_obj,
                                                                      apk_folder,
                                                                      global_apk_list,
                                                                      global_result_dict,
                                                                      share_lock_apk,
                                                                      share_lock_result))
        processes_list_detect.append(thread)

    for thread in processes_list_detect:
        thread.start()

    # The master process periodically detects the number of libraries currently analyzed and displays them in a percentage progress bar
    time_sec = 0
    all_apks_num = len(os.listdir(apk_folder))
    LOGGER.info("The number of apks analyzed this time is: %d", all_apks_num)
    time.sleep(1)
    finish_num = all_apks_num - len(global_apk_list)
    while finish_num < all_apks_num:
        finish_rate = int(finish_num / all_apks_num * 100)
        print('\r' + "current analysis: " + '▇' * (int(finish_rate / 2)) + str(finish_rate) + '%', end='')
        time.sleep(1)
        time_sec += 1
        finish_num = all_apks_num - len(global_apk_list)
    print('\r' + "current analysis: " + '▇' * (int(finish_num / all_apks_num * 100 / 2)) + str(
        int(finish_num / all_apks_num * 100)) + '%', end='')
    print("")

    for thread in processes_list_detect:
        thread.join()

    with open(output_folder + "/results.txt", "w", encoding="utf-8") as result:
        result.write("apk name library name similarity score\n")
        for k in sorted(global_result_dict.keys()):
            result.write(k + "   " + lib_obj.lib_name + "   " + global_result_dict[k] + '\n')

    # Output apk analysis duration
    time_end = datetime.datetime.now()
    LOGGER.info("Detection duration: %d (in seconds)", (time_end - time_start).seconds)
