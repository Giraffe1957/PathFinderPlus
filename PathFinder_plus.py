#!/usr/bin/env python -u
"""
Path_Finder Plus ( a complete reimagination of earlier Pathfinder code to address incomplete route identification )
-----------------------------------------------------------------------------------------------------------------------
                         Copyright: J Randy Ford 2019-2020 -- JRandyFord@hotmail.com
                         Developed using Anaconda Python 3.9 & PyCharm Community Edition
-----------------------------------------------------------------------------------------------------------------------
Abundant Appreciation to Randy Ellison (Framatome Inc) for beta testing, debugging assistance and code validation
-----------------------------------------------------------------------------------------------------------------------
Source Code credit to:
    stackoverflow.com/questions/11218477/how-can-i-use-pickle-to-save-a-dict
    stackoverflow.com/questions/952914/how-to-make-a-flat-list-out-of-list-of-lists/952952#952952
    stackoverflow.com/questions/3207219/how-do-i-list-all-files-of-a-directory
    code.tutsplus.com/tutorials/counting-word-frequency-in-a-file-using-python--cms-25965  by Abder-Rahman Ali
    stackoverflow.com/questions/17747330/correct-way-to-check-for-empty-or-missing-file-in-python
    geeksforgeeks.org/find-paths-given-source-destination/  by Neelam Yadav
-----------------------------------------------------------------------------------------------------------------------
THIS SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, TITLE AND NON-INFRINGEMENT.  IN NO EVENT SHALL THE
COPYRIGHT HOLDER OR ANYONE DISTRIBUTING THE SOFTWARE BE LIABLE FOR ANY DAMAGES OR OTHER LIABILITY, WHETHER IN CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
THIS SOFTWARE, ADAPTIONS OR ENHANCEMENTS, IN PART OR IN ENTIRETY, CANNOT BE COMMERCIALIZED WITHOUT THE AUTHORS CONSENT.
-----------------------------------------------------------------------------------------------------------------------

Generates the internal paths that represent complete target sets.  Evaluates routes using breaching methods, breaching
times, & barrier materials for adversary movement through all interior routes until a complete Target Set is reached
as determined by accessing the physical locations of sufficient Target Set Elements to complete a Target Set.

The output is SGI when actual Target Set data is included in TSets+.txt and/or actual breach data is in Breaches.csv.
Add a line to setup.txt that includes the phrase 'Safeguards = True' and the run log headers will automatically adjust.

Required Input files:
    AON.csv - Contains node related information (ID, description, material, breach method)
    ABN.csv - Contains nodal connection information (node from, node to, travel distance)
    Breaches.csv - Contains breach consumable resources and timing for all Technique/Material combinations used
    TSets+.txt - Contains boolean logic using locations (node IDs) from AON.csv to define a Target Set
        ALL Target Sets must start and end with () or it will cause errors
        Logic defined using + , and _ logic operators and () grouping operators
            + means AND (in any order)
            _ means AND THEN (in this order)
            , means OR
            EXAMPLE: A and either B or C is written A+(B,C)
    Setup.txt - Contains user selectable values: (one or more of the following entries on separate lines)
        client = [Name] to set client name in output files
        Safeguards = [True/False] to set SGI headers on reports
        adv_speed = [#] to set adversary travel speed inside the plant (in ft/sec)
        max_time = [#] to set the maximum time until adversaries are assumed to be neutralized (in sec)
        max_consumables = [#] to set the maximum weight of consumable supplies available to adversaries (in lbs)
        max_weight = [#] to set the maximum weight of consumable + non-consumable supplies available (in lbs)
        ascend_fatigue = [#.#] to set additional time in sec for each foot of vertical rise
        descend_fatigue = [#.#] to set additional time in sec for each foot of vertical descent
        cutoff_fastest = [#] restrict analysis to the [#] fastest routes combined with cutoff_lightest
        cutoff_lightest = [#] restrict analysis to the [#] lightest routes combined with cutoff_fastest
        backwards_compatible = [True/False] to set whether to run SEES PathFinder Ver 2 software compatible output files
        reserved_processors = [#] Number of processors to be withheld during Multiprocessing Operations
"""
import multiprocessing
from multiprocessing import Process
from threading import Thread
import collections
import itertools
import os
import os.path
from os import path
import glob
import sys
import time
import pickle
import copy


def generate_paths(all_nodes, tsenodes):
    """
    Create segments by walking node connections until either: the path gets revisits a used node (loop), the path
    includes a complete target set element location (valid path), or there are no more nodes available to go to.
    """
    #
    'Variables used during recursion (Step 1) - Shared with Path_Helper'
    global g                    # graph for recursive analysis
    global n_evals              # Counter for number of identified loops (used in recursion reports)
    global n_valid              # Counter for number of valid paths between Target Set Elements
    global n_recursion          # Recursion level variable (used in recursion reports)
    global reset_to_base_path   # Variable during recursion to reset path when reached end of loop or dead end
    #
    'Static Shared data'
    global ABN                  # Dict of ABN travel distance [node0-node1 string as key, distance in ft]
    global AON                  # Dict of AON breaches [node, methodID/time_sec/non-consumable_weight/consumable_weight]
    global node_id              # list of nodes - used to equate node ID with a number for regression routine
    global node_consum
    global node_time
    global delta_H              # Dict of ABN travel elevation change [node0-node1 string as key, vertical dist in ft]
    global breach_techniques    # Dict of data strings for matl:technique combinations
    global breachtoolweight     # Dict of string of tool weights used in non-Consumable tool calculations
    global breachdelay          # Dict of breach times by node
    global existing_paths       # Cumulative list of paths leading to valid Target Sets
    global segments             # List of connections between nodes 'node:node'
    global eval_segments        # Dictionary of List of connections to be evaluated key = 'node:node'  value = [paths]
    global segment_paths        # Dictionary of List of connections between nodes key = 'node:node'  value = [paths]
    global segment_pathdata     # Dictionary of segments (key) and associated times & resources (value as list)
    global progress             # Text ID to indicate current step to aid in output formatting
    global fastest              # Segments sorted by shortest time (time, key, path)
    global lightest             # Segments sorted by fewest consumable resources (consumables, key, path)
    global client               # Client name for reports
    global route_depth          # How deep into route to compare for route analysis
    global n_reserved           # Number of CPU processor threads to reserve for other work during multiprocessing
    #
    'Constants & Status Indicators set at loading'
    global version              # Software version used in reports (text)
    global max_time             # Maximum time allowed for adversary action before neutralization (sec)
    global max_consumables      # Maximum allowed weight of consumable supplies (lbm)
    global max_weight           # Maximum allowed weight of all supplies (lbm)
    global adv_speed            # Adversary speed (ft/sec)
    global ascend_fatigue       # Additional time required when going up to account for fatigue (sec/ft rise)
    global descend_fatigue      # Additional time required when going up to account for fatigue (sec/ft rise)
    global cutoff_fastest       # How many routes between A & B will be tested (1=fastest only, 0= all, n= n fastest)
    global cutoff_lightest      # How many routes between A & B will be tested (1=lightest only, 0= all, n= n lightest)
    global TSet_logic           # Cumulative list of Target Set logic strings from TSets+.txt
    global TSet_targets         # List of Nodes that are used in Target Set logic from TSets+.txt
    global Safeguards_Data      # Boolean to indicate if data files have actual safeguards information headers
    global backwards_compatible  # Boolean to indicate if to print Path_ files for Version 2.x compatibility
    global header               # Header used in output files
    global last_update          # counter used to limit screen updates
    global choke                # points expected to be in paths (defended), other are also listed in "focus.txt"
    #
    'File & logs opened once and used in various routines'
    global segments_out         # Valid Target segments output file
    global details              # Valid Target path output file with details on time/resources
    global log                  # Run logging file used in all routines
    global outfile              # Output file for each Step (open unique file at start of step)
    #
    for f in glob.glob("working_path*.txt"):
        os.remove(f)
    manager = multiprocessing.Manager()
    step1_log = manager.list()
    overalltimein = time.time()
    load_began = time.time()
    log = open('Log.txt', 'a')
    details = open('Detailed_Results.txt', 'w')
    details.close()
    details = open('Detailed_Results.txt', 'a')
    print("Checking ABN.csv for to ensure to & from nodes exist in model.")
    node_list = []
    i = 0
    for key in node_id:
        node_list.append(key)
        print(i, key)
        i += 1
    for key in ABN:
        var = key.split("-")
        ABN_from = var[0]
        ABN_to = var[1]
        if ABN_from not in node_list:
            print("ERROR:", ABN_from, "is not in the list of valid nodes")
        if ABN_to not in node_list:
            print("ERROR:", ABN_to, "is not in the list of valid nodes")
    header = "# ------------------------------------------------------------------------------- \n"
    existing_paths = []
    fastest = []
    lightest = []
    speed = []
    weight = []
    segments = []
    segment_paths = {}
    segment_pathdata = {}
    eval_segments = {}
    already_scanned = []
    last_update = 0
    startnode = "start"
    log.writelines("------------------------------------------------------------------------------------------ \n")
    log.writelines("Input Parameters:\n")
    log.writelines("    Adversary Speed: " + str(adv_speed) + " ft/sec \n")
    log.writelines("    Maximum Time Allowed: " + str(max_time) + "\n")
    log.writelines("    Maximum Consumable Supplied Allowed: " + str(max_consumables) + "\n")
    log.writelines("    Maximum Total Supplies Allowed: " + str(max_weight) + "\n")
    log.writelines("    Ascent Fatigue Factor: " + str(ascend_fatigue) + " sec/ft rise \n")
    log.writelines("    Descent Fatigue Factor: " + str(descend_fatigue) + " sec/ft descent \n")
    log.writelines("    Cutoff: Fastest " + str(cutoff_fastest) + " routes  \n")
    log.writelines("    Cutoff: Lightest " + str(cutoff_lightest) + " routes  \n")
    log.writelines("\n")
    '-------------------------------------------------------------------------------------------------------------'
    'Step 0 - Attempt to reload existing segment information                                                      '
    '-------------------------------------------------------------------------------------------------------------'
    skip1b = False
    file1 = False
    file2 = False
    file3 = False
    file4 = True
    print('')
    print("Step 0: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Reloading stored node network files & checking for any new nodes added to Target Sets.")
    if path.exists('segment_paths.pickle'):
        file1 = True
        print('    Loading segment_paths pickle...')
        segment_paths = load_pickle("segment_paths")
        for key in segment_paths:
            already_scanned.append(key)
    if path.exists('segment_pathdata.pickle'):
        file2 = True
        segment_pathdata = load_pickle("segment_pathdata")
        print('    Loading segment_pathdata pickle...')
    if path.exists('eval_segments.pickle'):
        file3 = True
        eval_segments = load_pickle("eval_segments")
        print('    Loading eval_segments pickle...')
    if segment_paths:
        print('    Scanning segment_pathdata for completed evaluations')
        for key in segment_paths:
            already_scanned.append(key)
    print('    Loading complete')
    x_paths = segment_paths.keys()
    progress = "Step0"
    load_ended = time.time()
    '-------------------------------------------------------------------------------------------------------------'
    ' Step 1 - Initialize logs, files, and prepare to run analysis                                                '
    '-------------------------------------------------------------------------------------------------------------'
    for f in glob.glob("Path_*.txt"):
        os.remove(f)
    if os.path.exists("tset_logic.txt"):
        os.remove("tset_logic.txt")
    timein_part1 = time.time()
    log.writelines("------------------------------------------------------------------------------------------ \n")
    log.writelines("\n")
    log.writelines("Begin Calculations.....\n")
    log.writelines("\n")
    log.writelines("Step 0: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines("Load data from files \n")
    step_summary(load_began, load_ended, "0", "nodes", len(x_paths))
    print("")
    log.writelines("\n")
    log.writelines("Step 1: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines('Identify Segments from Start to each Target Set Element via Recursive Analysis \n')
    print("Step 1: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print('Identify Segments from Start to each Target Set Element via Recursive Analysis')
    print('    Please be patient... this may take a while...')
    reset_to_base_path = False
    n_evals = 0
    n_recursion = 0
    n_valid = 0
    # File Clean up - Erase any previous contents of Dictionary and Step#,txt files before starting new run
    invalid = open('Invalid_Paths.txt', 'w')
    if Safeguards_Data:
        invalid.writelines("----------------------------------------------------------------------------------------\n")
        invalid.writelines("                   ---> SAFEGUARDS INFORMATION  (10 CFR 73.21) <---                     \n")
        invalid.writelines(" This information is protected from unauthorized release as SAFEGUARDS INFORMATION.     \n")
        invalid.writelines("Violation of Sect 147 of the Atomic Energy Act is subject to CIVIL & CRIMINAL Penalties \n")
        invalid.writelines("----------------------------------------------------------------------------------------\n")
    invalid.writelines("------------------------------------------------------------------------------------------  \n")
    invalid.writelines("  PathFinder+ " + version + " - Copyright J Randy Ford 2019-2020 - all rights reserved      \n")
    invalid.writelines("  Analysis of " + client + " Run started at " + time.strftime("%H:%M:%S %a %b %d, %Y") + "  \n")
    invalid.writelines("------------------------------------------------------------------------------------------  \n")
    invalid.writelines("  File contains paths that exceeded allowable time, consumables, or total weights allowed   \n")
    invalid.writelines("  Time < " + str(max_time) + "     Consumables < " + str(max_consumables))
    invalid.writelines("     Total weight < " + str(max_weight) + "\n")
    invalid.writelines("------------------------------------------------------------------------------------------  \n")
    invalid.close()
    outfile = open('Step1.txt', 'w')
    outfile.close()
    outfile = open('Step2.txt', 'w')
    outfile.close()
    outfile = open('Step3.txt', 'w')
    outfile.close()
    outfile = open('Step4.txt', 'w')
    outfile.close()
    outfile = open('Step5.txt', 'w')
    outfile.close()
    cur_path = []
    cur_path.append(startnode)
    details.writelines(header)
    details.writelines("# Pathfinder+ " + version + "\n")
    details.writelines("# " + time.strftime("%H:%M %a %b %d, %Y") + " \n")
    details.writelines(header)
    details.writelines("# Input Parameters:\n")
    details.writelines("#     Adversary Speed: " + str(adv_speed) + " ft/sec \n")
    details.writelines("#     Maximum Time Allowed: " + str(max_time) + "\n")
    details.writelines("#     Maximum Consumable Supplied Allowed: " + str(max_consumables) + "\n")
    details.writelines("#     Maximum Total Supplies Allowed: " + str(max_weight) + "\n")
    details.writelines("#     Ascent Fatigue Factor: " + str(ascend_fatigue) + " sec/ft rise \n")
    details.writelines("#     Descent Fatigue Factor: " + str(descend_fatigue) + " sec/ft rise \n")
    details.writelines("#     Cutoff: Fastest " + str(cutoff_fastest) + " routes  \n")
    details.writelines("#     Cutoff: Lightest " + str(cutoff_lightest) + " routes  \n")
    details.writelines(header)
    details.writelines('# How to read Step 3 output:   \n')
    details.writelines('# Output is in form of a counter plus a string of events (Travel - Breach - Travel...).')
    details.writelines('  Dash number dash is a travel segment with the number being the travel time in seconds \n')
    details.writelines('# AAA[xxx,yyy#] is a node/barrier with AAA being the barrier id, xxx being the breach time')
    details.writelines(' in seconds and yyy# being the pounds of consumable supplies required to breach. \n')
    details.writelines(header)
    details.writelines("# Target Sets: \n")
    i = 0
    for item in TSet_logic:
        i += 1
        details.writelines("#     " + str(i) + " - " + item + "\n")
    progress = "Step1"
    outfile = open('Step1.txt', 'a')
    step1_log.append("-----------------------------------------------------------------------------------\n")
    step1_log.append("                                  STEP 1                                           \n")
    step1_log.append("-----------------------------------------------------------------------------------\n")
    paths_out = open('Valid_Paths.txt', 'w')
    if path.exists('segments.txt'):
        segments_out = open('Segments.txt', 'a')
    else:
        segments_out = open('Segments.txt', 'w')
        if Safeguards_Data:
            segments_out.writelines("# -----------------------------------------------------------------------------\n")
            segments_out.writelines("#            ---> SAFEGUARDS INFORMATION  (10 CFR 73.21) <---                  \n")
            segments_out.writelines("#         This information is protected from unauthorized release.             \n")
            segments_out.writelines("#     Violation of Section 147 of the Atomic Energy Act is subject to          \n")
            segments_out.writelines("#                      CIVIL & CRIMINAL Penalties.                             \n")
        segments_out.writelines("# -----------------------------------------------------------------------------\n")
        segments_out.writelines("#  PathFinder+ " + version + " - Copyright J Randy Ford 2020 - all rights reserved \n")
        segments_out.writelines("#  Analysis of " + client + " \n")
        segments_out.writelines("# -----------------------------------------------------------------------------\n")
        segments_out.writelines("#  This file contains paths between points of interest regardless of resources \n")
        segments_out.writelines("# -----------------------------------------------------------------------------\n")
    if Safeguards_Data:
        paths_out.writelines("--------------------------------------------------------------------------------------\n")
        paths_out.writelines("                  ---> SAFEGUARDS INFORMATION  (10 CFR 73.21) <---                    \n")
        paths_out.writelines(" This information is protected from unauthorized release as SAFEGUARDS INFORMATION.   \n")
        paths_out.writelines("           Violation of Section 147 of the Atomic Energy Act is subject to            \n")
        paths_out.writelines("                           CIVIL & CRIMINAL Penalties.                                \n")
    paths_out.writelines("------------------------------------------------------------------------------------------\n")
    paths_out.writelines("  PathFinder+ " + version + " - Copyright J Randy Ford 2019-2020 - all rights reserved    \n")
    paths_out.writelines("  Analysis of " + client + " Run started at " + time.strftime("%H:%M:%S %a %b %d, %Y") + "\n")
    paths_out.writelines("------------------------------------------------------------------------------------------\n")
    paths_out.writelines("  File contains paths that are within allowable time, consumables, and total weights      \n")
    paths_out.writelines("  Time < " + str(max_time) + "     Consumables < " + str(max_consumables))
    paths_out.writelines("     Total weight < " + str(max_weight) + "\n")
    paths_out.writelines("------------------------------------------------------------------------------------------\n")
    paths_out.close()
    load_g_from_file()
    '-------------------------------------------------------------------------------------------------------------'
    ' Step 1A - Identify Segments from Start to each Target Set Element via Recursive Analysis                    '
    ' This step runs all possible routes using depth-wise recursive calls and identifies all paths between points '
    ' of interest (start locations and nodes appearing in TsSet logic).  This is used later to assemble potential '
    ' routes to a complete Target Set. Clean up file from last run...                                             '
    '-------------------------------------------------------------------------------------------------------------'
    # create list of connections to be processed from target sets
    print("    Evaluating Target Set Logic to identify what connections are required")
    needed_connections = []
    for node1 in TSet_targets:
        needed_connections.append("start:" + node1)     # PA to each TSE
        for node2 in TSet_targets:
            if node1 != node2:
                needed_connections.append(node1 + ":" + node2)      # Between TSEs
    print("    Creating connection data file")
    queue = []
    working = manager.list()
    ready4dict = manager.list()
    n_processors = os.cpu_count() - n_reserved
    current_directory = os.getcwd()
    # ========================================================================
    print("    Checking for pre-existing Path_*.txt files in Paths_Files subdirectory...")
    # Source: stackoverflow.com/questions/3207219/how-do-i-list-all-files-of-a-directory
    existing_path_files = os.listdir(current_directory + "\\Path_Files\\")
    for existingfilename in existing_path_files:
        if "PathData_" in existingfilename:
            fullfilename = current_directory + "\\Path_Files\\" + existingfilename
            # If file has data, add to ready4dict list otherwise skip it
            # Source: stackoverflow.com/questions/17747330/correct-way-to-check-for-empty-or-missing-file-in-python
            k_start = existingfilename.find("PathData_") + 9
            k_end = existingfilename.find(".txt")
            k = existingfilename[k_start:k_end]
            k = k.replace("_", ":")
            needed_connections.remove(k)
            ready4dict.append(fullfilename)
    # ========================================================================
    print("        ", len(ready4dict), "files already exist...")
    print("    Generating queue for evaluations...")
    step1_log.append("    Generating queue for evaluations...")
    for this_set in needed_connections:
        if this_set not in already_scanned:
            queue.append(this_set)        # Add file to queue of files pending creation
            step1_log.append("    " + time.strftime("%H:%M:%S") + " " + this_set + " added to queue\n")
        else:
            step1_log.append("    " + time.strftime("%H:%M:%S") + " " + this_set + " is already in dictionary\n")
    core_thread = os.getpid()
    print("    Processing queues -----> Main Thread ID", core_thread, "   Number of processors utilized=", n_processors)
    step1_log.append("    Processing queues ------  Number of processors utilized=" + str(n_processors))
    while queue or working:
        for my_segment in queue:
            file4 = False      # Files changes, pickle is no longer up-to-date - recreate new one
            if len(working) < (n_processors - 1):
                print("        Status at", time.strftime("%H:%M:%S"), "  waiting=", len(queue), "  working=",
                      len(working), "  ready4dict=", len(ready4dict), " -- Spawning analysis for", my_segment)
                f_paths = current_directory + "\\Path_Files\\Paths_" + my_segment.replace(":", "_") + ".txt"
                f_pathdata = current_directory + "\\Path_Files\\PathData_" + my_segment.replace(":", "_") + ".txt"
                working.append(f_pathdata)
                step1_log.append("    " + time.strftime("%H:%M:%S") + " Finding paths for " + my_segment + "\n")
                dash = my_segment.find(":")
                k1 = my_segment[:dash]
                k2 = my_segment[dash + 1:]
                if k1 in node_id and k2 in node_id:
                    datapack = {}
                    datapack['paths_filename'] = f_paths
                    datapack['pathdata_filename'] = f_pathdata
                    datapack['start'] = node_id.index(k1)
                    datapack['dest'] = node_id.index(k2)
                    datapack['g'] = copy.deepcopy(g)
                    datapack['node_id'] = copy.deepcopy(node_id)
                    datapack['node_consum'] = copy.deepcopy(node_consum)
                    datapack['node_time'] = copy.deepcopy(node_time)
                    datapack['node_tools'] = copy.deepcopy(node_tools)
                    datapack['max_time'] = max_time
                    datapack['max_consumables'] = max_consumables
                    datapack['max_weight'] = max_weight
                    task = Process(target=print_all_paths, args=(datapack, working, ready4dict, step1_log,))
                    task.start()
                    queue.remove(my_segment)
                else:
                    # Error Handling
                    if k1 not in node_id:
                        print(k1 + " is not in node_id - skipping \n")
                        step1_log.append(k1 + " is not in node_id - skipping \n")
                    if k2 not in node_id:
                        print(k2 + " is not in node_id - skipping \n")
                        step1_log.append(k2 + " is not in node_id - skipping \n")
    print("    All paths from PA to a Target Set Element (TSE) or from TSE to TSE in files")
    step1_log.append("    All paths from PA to a Target Set Element (TSE) or from TSE to TSE in files")
    log.writelines("All paths from PA to a Target Set Element (TSE) or from TSE to TSE in files\n")
    # Retain all_nodes[] and tsenodes[] data for later use - clear other lists for better memory management
    if not file1 or not file2 or not file3 or not file4:
        '--------------------------------------------------------------------------------------------------------------'
        ' Step 1B - Reduce from ALL possible paths for segment to a reasonable bounding set (segment_paths dictionary))'
        ' This step reduces run time by eliminating less fruitful paths from consideration                             '
        '--------------------------------------------------------------------------------------------------------------'
        dictionary_updated = False
        combo = []
        log.writelines("\n")
        log.writelines("Step 1B: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
        log.writelines("Reduce from ALL possible paths in Step 2 to a reasonable bounding set of pathways \n")
        print(" ")
        print("Step 1B: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
        print("Reduce from ALL possible paths in Step 1A to a reasonable bounding set of pathways")
        if cutoff_fastest > 0:
            log.writelines("    Limited to " + str(cutoff_fastest) + " fastest \n")
            print("    Limited to " + str(cutoff_fastest) + " fastest")
        if cutoff_lightest > 0:
            log.writelines("    Limited to " + str(cutoff_lightest) + " with the least consumable resources \n")
            print("    Limited to " + str(cutoff_lightest) + " with the least consumable resources")
        n_processed = 0
        to_process = []
        # os.chdir("/Path_Files")
        for file in glob.glob("Path_Files//PathData_*.txt"):
            to_process.append(file)
        for filename in to_process:
            cutoff_time = float(999999)
            cutoff_consum = float(999999)
            fastest = []
            lightest = []
            with open(filename) as f:
                print("\r    Processing ", filename, "                             ", end="")
                content = f.readlines()
                for x_line in content:
                    working_line = x_line.split(":")
                    mission = working_line[0].rstrip()
                    if "start-PA-" in mission:
                        mission = mission.replace("start-PA-", "start-")
                    nodes = mission.split("-")
                    if nodes[-1] == "":
                        del nodes[-1]
                    mission_data = working_line[1]
                    mission_data = mission_data.replace("[", "")
                    mission_data = mission_data.replace("],", "")
                    mission_data = mission_data.replace("\n,", "")
                    data_list = mission_data.split(",")
                    this_line_time = data_list[0]
                    this_line_consum = data_list[1]
                    if float(this_line_time) < cutoff_time:
                        if len(fastest) >= cutoff_fastest:
                            removed = fastest.pop()  # IF list is at max, remove last item before appending
                            cutoff_time = float(this_line_time)
                        fastest.append(x_line)
                    if float(this_line_consum) < cutoff_consum:
                        if len(lightest) >= cutoff_lightest:
                            removed = lightest.pop()  # IF list is at max, remove last item before appending
                            cutoff_consum = float(this_line_consum)
                        lightest.append(x_line)
            # Combine fastest & lightest
            seg_key = filename.replace("Path_Files\\PathData_", "")
            seg_key = seg_key.replace(".txt", "")
            seg_key = seg_key.replace("_", ":")
            mission_key = seg_key.replace(":", "-")
            combo = copy.deepcopy(fastest)
            for x_line in lightest:
                if x_line not in combo:
                    combo.append(x_line)
            mission_list = []
            eval = []
            for x_line in combo:
                working_line = x_line.split(":")
                mission = working_line[0].rstrip()
                mission_list.append(mission)
                mission_data = working_line[1]
                mission_data = mission_data.replace("[", "")
                mission_data = mission_data.replace("],", "")
                mission_data = mission_data.replace("\n", "")
                data_list = mission_data.split(",")
                segment_pathdata[mission] = data_list
                data_string = list2string(mission, data_list)
                eval.append(data_string)
            segment_paths[seg_key] = copy.deepcopy(mission_list)
            eval_segments[mission_key] = copy.deepcopy(eval)
            dictionary_updated = True
        for line in step1_log:
            outfile.writelines(line + "\n")
        print(
            "\r        All input files processed                                                                      ")
        if dictionary_updated:
            # Generate separate threads to save pickle files to avoid file corruption during early program stops
            print("    Dictionary was changed, Saving Dictionaries...")
            step1_log.append("    Dictionary was changed, Saving Dictionaries...")
            a = Thread(target=save_pathdata_pickle())
            a.start()
            a.join()
            b = Thread(target=save_paths_pickle())
            b.start()
            b.join()
            c = Thread(target=save_eval_pickle())
            c.start()
            c.join()
            print("    Dictionaries saved (pickled)")
            step1_log.append("    Dictionaries saved (pickled)")
    cur_path.clear()
    step_summary(timein_part1, time.time(), "1", "nodal connections", len(needed_connections))
    outfile.close()
    log.close()  # Force log close to write contents
    '--------------------------------------------------------------------------------------------------------------'
    ' Step 2 - Link segments to create mission meeting Target Set logic                                            '
    ' This step assembles segments from the Target Set logic into missions (TSE_node:TSE_node:TSE_node:...)        '
    '--------------------------------------------------------------------------------------------------------------'
    outfile = open('Step2.txt', 'a')
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    outfile.writelines("                                  STEP 2                                           \n")
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    progress = "Step2"
    log = open('Log.txt', 'a')      # Reopen log after writing to file
    timein_part2 = time.time()
    print(" ")
    print("Step 2: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Link route segments to create mission meeting Target Set logic")
    log.writelines("\n")
    log.writelines("Step 2: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines("Link route segments to create mission meeting Target Set logic \n")
    print("    Evaluating Segment Addition to Produce Complete Target Set")
    missions = []
    n_processed = 0
    with open("TSets+.txt", 'r') as txt_file:
        mission_list = txt_file.readlines()
        for line in mission_list:
            if line[0] != "#":
                new_mission_paths = deconstruct(line.strip("\n"))
                for item in new_mission_paths:
                    if "::" in item:
                        item = item.replace("::", ":")
                    if "+" in item:
                        item = item.replace("+", "")
                    if "(" in item:
                        item = item.replace("(", "")
                    if ")" in item:
                        item = item.replace(")", "")
                    if item not in missions:
                        missions.append(item + " (TSet= " + line.strip("\n") + ")")
                        n_processed += 1
                        print("        [" + str(n_processed) + "] " + item + " (TSet= " + line.strip("\n") + ")")
    missions.sort()
    details.writelines("# The above logic is converted into the following mission perturbations...\n")
    for entry in missions:
        details.writelines("#     " + entry + "\n")
    step_summary(timein_part2, time.time(), "2", "target set missions", n_processed)
    outfile.close()
    log.close()     # Force log close to write contents
    '----------------------------------------------------------------------------------------------------------------'
    ' Step 3 -  Generating combinations of the reduced number of paths between desired TSEs                          '
    ' This step generates all possible routes for missions based on combinations of reduced set of segments          '
    '----------------------------------------------------------------------------------------------------------------'
    timein_part3 = time.time()
    outfile = open('Step3.txt', 'a')
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    outfile.writelines("                                  STEP 3                                           \n")
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    paths_out = open('Valid_Paths.txt', 'a')
    progress = "Step3"
    print(" ")
    print("Step 3: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Using short list of paths between waypoints from Step 1 and mission waypoints from in Step 2")
    print("Generate all combinations of paths between waypoints for each mission")
    log = open('Log.txt', 'a')      # Reopen log after writing to file
    log.writelines("\n")
    log.writelines("Step 3: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines("Using short list of paths between waypoints from Step 1 and mission waypoints from in Step 2 \n")
    log.writelines("Generate all combinations of paths between waypoints for each mission \n")
    # take missions (node:node:node) and substitute possible path lists from segment_paths
    route_list = []
    route_list_options = []
    path_options = []               # missions = list of A-> B string of TSEs to&from TSet from list of lists
    counter = 0
    for item in missions:      # tset_paths = single A -> B string from list of options...
        counter += 1
        outfile.writelines("    " + time.strftime("%H:%M:%S") + " TSet Path = start:" + item + "\n")
        route_list_options.clear()
        last_node = "start"
        tset_loc = item.find("(")
        tset_path = item[0:tset_loc - 1]
        tset_path_nodes = tset_path.split(":")
        for node in tset_path_nodes:            # individual nodes from mission string (nodes connected by :)
            if node == "" or node == " " or node is None:
                break
            this_key = last_node + "-" + node
            path_options = eval_segments.get(this_key, [])
            outfile.writelines("        " + this_key + " with #paths= " + str(len(path_options)) + "\n")
            route_list_options.append(path_options)
            last_node = node
        # Store solution for tset_path, reset path_options to [], and continue
        route_list.append(route_list_options.copy())
    counter = len(route_list)
    step_summary(timein_part3, time.time(), "3", "missions", counter)
    outfile.close()
    log.close()
    print('')
    '----------------------------------------------------------------------------------------------------------------'
    ' Step 4 -  Evaluates combinations of paths generated in last step                                               '
    ' This step evaluates all combinations of routes from node:node and checks required resources vs max resources   '
    ' Those results are logged as either a VALID path in Valid_Paths.txt or INVALID path in Invalid_Paths.txt        '
    '----------------------------------------------------------------------------------------------------------------'
    timein_part4 = time.time()
    outfile = open('Step4.txt', 'a')
    focus = open('Focus.txt', 'w')
    focus.writelines("=========================================================================\n")
    focus.writelines(" Paths that did not contain expected choke points  \n")
    focus.writelines("   --> ")
    for expected in choke:
        focus.writelines(expected.strip() + " ")
    focus.writelines(" \n")
    focus.writelines(" Focus on resolving the following paths \n")
    focus.writelines("=========================================================================\n")
    print("Step 4: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Evaluating resources and timing for paths from Step 3 ")
    log = open('Log.txt', 'a')      # Reopen log after writing to file
    log.writelines("\n")
    log.writelines("Step 4: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines("Evaluating resources and timing for paths from Step 3 \n")
    log.writelines("    See Valid_Paths.txt for successful adversary routes \n")
    log.writelines("    See Invalid_Paths.txt for routes that did not meet success conditions \n")
    scenarios = []
    mission_id = []
    mission_count = 0
    for this_mission in route_list:
        total_missions = len(route_list)
        mission_count += 1
        details.writelines("    " + time.strftime("%H:%M:%S") + " Mission = " + missions[mission_count - 1] + "\n")
        print("    " + time.strftime("%H:%M:%S") + " [" + str(mission_count) + "/" + str(total_missions) +
              "] Processing Mission = " + missions[mission_count - 1])
        scenario_perms = perm(this_mission, max_time, max_consumables, max_weight)
        for list_x in scenario_perms:
            scenarios.append(list_x)
            mission_id.append(missions[mission_count - 1])
    outfile.writelines(" \n")
    outfile.writelines(" \n")
    outfile.writelines("======================================================================\n")
    outfile.writelines(" All possible valid permutations are: (i.e., max limits not exceeded)\n")
    outfile.writelines("======================================================================\n")
    outfile.writelines(" Counter   a= time in sec    b= lbs Consumables    c= lbs total weight\n")
    outfile.writelines("000000000 [aaaaa,bbb,ccc] <d,d,d,...>   d= lbs of each tool in toolbox\n")
    paths_out.writelines(" \n")
    paths_out.writelines(" \n")
    paths_out.writelines("======================================================================\n")
    paths_out.writelines(" All possible valid permutations are: (i.e., max limits not exceeded)\n")
    paths_out.writelines("======================================================================\n")
    paths_out.writelines(" Counter   a= time in sec    b= lbs Consumables    c= lbs total weight\n")
    paths_out.writelines("000000000 [aaaaa,bbb,ccc] <d,d,d,...>   d= lbs of each tool in toolbox\n")
    counter = 0
    list_count = 0
    for list_x in scenarios:
        tset_name = missions[list_count]
        list_count += 1
        for item in list_x:
            outfile.writelines(str(counter).zfill(9) + " " + item + "\n")
            paths_out.writelines(str(counter).zfill(9) + " " + item + "\n")
            # Create detailed string from string (after ">")
            string_start = item.find(">,") + 2
            working = item[string_start:].strip()
            working_nodes = working.split("-")
            last_node = ""
            tmp = ""
            route = ""
            for node in working_nodes:
                key = last_node + "-" + node
                if last_node != "":
                    if key == 'start-PA':       # start is PA so all distances are zero
                        move_dist = 0
                        d = 0
                    else:
                        move_dist = int(round(float(ABN[key])))
                        d = int(round(float(delta_H[key])))
                    if d > 0:
                        vertical = d * ascend_fatigue
                    else:
                        vertical = d * descend_fatigue
                    move_time = int((move_dist/adv_speed + vertical) + 0.051)
                    if node in route:
                        breach_time = 0         # Already has been breached, set time/resources to zero
                        breach_weight = 0
                    else:
                        breach_time = node_time[node]       # First time, breach required
                        breach_weight = node_consum[node]
                    tmp += str(move_time) + "-"
                    tmp += node + "[" + str(breach_time) + "," + str(breach_weight) + "#]-"
                last_node = node
                route += node + "-"
            details.write(str(counter + 1).zfill(9) + "  " + tmp + "-->Mission= " + tset_name + "\n")
            put_in_focus = True
            for expected in choke:
                if expected.strip() in tmp:
                    put_in_focus = False
            if put_in_focus:
                focus.writelines(tmp + "\n")
            counter += 1
    step_summary(timein_part4, time.time(), "4", "permutations", counter)
    paths_out.close()       # close paths_out so it can be used in Step 6 as input in freq analysis
    outfile.close()
    focus.close()
    '----------------------------------------------------------------------------------------------------------------'
    ' Step 5 - Wrap-Up: Analyze how often a node appears in valid paths, create reports, and create stats            '
    ' This step generates reports and performs certain frequency analyses to help identify which nodes could most    '
    ' beneficially affect future configuration changes.                                                              '
    '----------------------------------------------------------------------------------------------------------------'
    outfile = open('Step5.txt', 'a')
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    outfile.writelines("                                  STEP 5                                           \n")
    outfile.writelines("-----------------------------------------------------------------------------------\n")
    log = open('Log.txt', 'a')      # Reopen log after writing to file
    paths_in = open('Valid_Paths.txt', 'r')
    progress = "Step5"
    print(" ")
    print("Step 5: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Performing reporting and data analysis")
    log = open('Log.txt', 'a')      # Reopen log after writing to file
    log.writelines("\n")
    log.writelines("Step 5: " + time.strftime("%H:%M:%S %a %b %d, %Y") + " \n")
    log.writelines("Performing reporting and data analysis \n")
    log.writelines("    Running node frequency analysis - how often does each node appear in paths... \n")
    print("    Running node frequency analysis - how often does each node appear in paths...")
    print("    Looking for Node Occurrences..." + time.strftime("%H:%M:%S %a %b %d, %Y"))
    'Frequency Code Credit: StackOverflow.com - Abder-Rahman Ali 1Jun2016'
    occurrences = {}
    TSet_list = []
    tset_results = {}
    with open('Valid_Paths.txt', "r") as freq_in:
        for line in freq_in:
            if line.find("#") < 0:      # skip lines with a comment character
                x1 = line.find(">")
                TSet_list.append(line[x1 + 1:])
                strip_to = line.find("]") + 2
                path_nocounter = line[strip_to:]
                nodes = path_nocounter.rstrip('\n').split("-")
                for entry in nodes:
                    if entry in occurrences:
                        occurrences[entry] += 1
                    else:
                        occurrences[entry] = 1
    log.writelines("        Frequency sorted by node id -> Freq_by_Node.txt\n")
    print("        Sorted by NodeID..." + time.strftime("%H:%M:%S %a %b %d, %Y"))
    with open('Freq_by_Node.txt', "w") as freq_bynode:
        freq_by_value = []
        for node in all_nodes:
            if node in occurrences:
                freq_by_value.append(str(occurrences[node]).rjust(12) + " - " + node)
                freq_bynode.writelines(node + " - " + str(occurrences[node]) + "\n")
            else:
                freq_bynode.writelines(node + " - " + str(0) + "\n")
    log.writelines("        Frequency sorted by # occurrences -> Freq_by_Value.txt \n")
    print("        Sorted by Value..." + time.strftime("%H:%M:%S %a %b %d, %Y"))
    freq_by_value.sort(reverse=True)
    with open('Freq_by_Value.txt', "w") as freq_byval:
        for line in freq_by_value:
            freq_byval.writelines(line + "\n")
    for key, value in sorted(tset_results.items()):
        log.writelines("        Target Set " + str(key) + ": " + str(value) + "\n")
    segments_out.close()
    if backwards_compatible:
        log.writelines("\n")
        log.writelines("-----------------------------------------------------------------------------------\n")
        log.writelines(" Backwards Compatibility - files also in original PathFinder Ver 2 software format \n")
        log.writelines("-----------------------------------------------------------------------------------\n")
        log.writelines("    Old PathFinder Ver 2 file format - path files by point of entry\n")
        log.writelines("        Sorting Valid Paths by point of entry -> Path_[Node].txt\n")
        print("    Maintaining Version 2 backwards compatibility - path files by point of entry")
        print("        Sorting Valid Paths by point of entry -> dictionary  " + time.strftime("%H:%M:%S"))
        ignore = ['Start', "start", 'pa', 'Pa', 'PA']
        retro_list = []
        entrypoints = []
        pathList = []
        temp_list = []
        k = 0
        kounter = 0
        with open('Segments.txt', "r") as segments_in:
            for line in segments_in:
                if line.find("#") < 0:  # run lines without a comment character
                    # remove leader and space dash space separator - assumes this sequence is in all lines
                    leader = line.find(" - ") + 3
                    my_seg = line[leader:]
                    pathlist = my_seg.split("-")
                    for p in pathlist:
                        if p not in ignore:
                            entry_node = p
                            k = pathlist.index(entry_node)
                            lf = entry_node.find('\n')  # If you strip \n too soon, you do not match pathlist
                            if lf > 0:  # You want to keep the \n for the txt output file
                                entry_node = entry_node.rstrip('\n')
                            retro_list = pathlist[k:]
                            retro_line = '-'.join(retro_list)
                            if entry_node not in entrypoints:
                                print("        Found Entry Point = " + entry_node)
                                entrypoints.append(entry_node)
                            temp_list.append(retro_line)
                            break
        segments_in.close()
        print("        Sorting lines by entry point...")
        temp_list.sort()
        print("        Sorting complete")
        last_entry = ""
        ver2_file = open('Paths_.txt', "w")
        ver2_file.writelines("# Paths_***.txt are the paths associated with each entry point......")
        ver2_file.writelines('# This creates the files to maintain compatibility with the original')
        ver2_file.writelines('# PathFinder used to support SEES software (by author for Framatome)')
        for line in temp_list:
            entry_list = line.split("-")
            if entry_list[0] != last_entry:
                last_entry = entry_list[0]
                lf = last_entry.find('\n')
                if lf > 0:
                    last_entry = last_entry.rstrip('\n')
                my_filename = "Paths_" + last_entry + ".txt"
                ver2_file.close()
                ver2_file = open(my_filename, "w")
                print("        Printing to " + my_filename)
                kounter = 0
            kounter += 1
            outline = "[" + str(kounter) + "] " + line
            ver2_file.writelines(outline)
        print("        Backwards compatible files created")
    overallelapsed = time.time() - overalltimein
    et_hr = int(overallelapsed/3600)
    et_min = int((overallelapsed - int(et_hr) * 3600) / 60)
    et_sec = int((overallelapsed - int(et_hr) * 3600 - int(et_min) * 60))
    et_millisec = int((overallelapsed - int(et_hr) * 3600 - int(et_min) * 60 - int(et_sec))*1000)
    print(" ")
    print("-------------------------------------------------------------------------------")
    print("Pathfinder+ " + version + "  " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print("Complete in " + str(et_hr) + ":" + str(et_min).zfill(2) + ":" + str(et_sec).zfill(2) + "."
          + str(et_millisec).zfill(3))
    print("-------------------------------------------------------------------------------")
    log.writelines(" \n")
    log.writelines(header)
    log.writelines("Pathfinder+ " + version + "  " + time.strftime("%H:%M:%S %a %b %d, %Y") + "\n")
    log.write("Complete in " + str(et_hr) + ":" + str(et_min).zfill(2) + ":" + str(et_sec).zfill(2))
    log.writelines("." + str(et_millisec).zfill(3) + "\n")
    log.writelines(header)
    progress = "Finished"
    print("Finished: " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    log.writelines("Finished: " + time.strftime("%H:%M:%S %a %b %d, %Y") + "\n")
    paths_in.close()
    if os.path.exists("Path_.txt"):
        os.remove("Path_.txt")
    outfile.close()
    log.close()


def resource_details(fullpath):
    """
    Analyzes the resources required at each node along path and returns a total resource demand
    """
    global AON
    global max_time
    global max_consumables
    global max_weight
    global segment_paths
    global segment_pathdata
    total_time = 0
    total_consum = 0
    path_string = "-".join(fullpath)
    path_string = path_string.strip()
    default_tools = "0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0"
    total_tools = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    for item in fullpath:
        if item != fullpath[0]:
            var = AON.setdefault(item, default_tools).split(',')
            breach_time = int(var[0])
            total_time += float(breach_time)
            total_consum += float(var[1])
            for i in range(2, 21):
                if int(var[i]) > total_tools[i - 2]:
                    total_tools[i - 2] = var[i]
    total_nonconsum = total_consum
    for tool in total_tools:
        total_nonconsum += float(tool)
    tool_weights = "<" + ",".join(str(x) for x in total_tools) + ">"
    if total_time > max_time or total_consum > max_consumables or total_nonconsum > max_weight:
        resource_string = "invalid"
    else:
        segment_pathdata[path_string] = [total_time, total_consum, total_nonconsum, tool_weights]
        resource_string = "valid"
    details.writelines(resource_string + "\n")
    return resource_string


def deconstruct(line):
    """
    Takes missions from TSets+.txt and converts into TSE to TSE pathways (node:node:node:...)
    """
    global outfile
    to_process = []
    processed = []
    to_process.append(line)
    outfile.writelines("\n")
    outfile.writelines("============================================================================================\n")
    outfile.writelines("Converting logic below into mission paths:\n")
    outfile.writelines(line + "\n")
    outfile.writelines("============================================================================================\n")
    while len(to_process) > 0:
        dbug = len(to_process)
        outfile.writelines("\n")
        if dbug == 1 or dbug == 0:
            if to_process[0] == '':
                print("        No more lines to process")
                break
        mission = to_process[0]
        max_depth = paren_depth(mission)
        current_depth = max_depth
        if max_depth == 0:
            outfile.writelines("        Saving: " + mission + "\n")
            if mission[-1] != ":":
                mission += ":"
            processed.append(mission)
            current_depth = 0
            outfile.writelines("        Complete: " + mission + "\n")
        while current_depth == max_depth:
            n_depth = 0
            for j in range(len(mission)):
                if mission[j] == "(":
                    n_depth += 1
                    if n_depth == max_depth:
                        pre_mission = mission[0:j]
                        mission_fragment = mission[j+1:]
                        r_paren = mission_fragment.find(")")
                        post_mission = mission_fragment[r_paren + 1:]
                        mission_fragment = mission_fragment[:r_paren]
                        outfile.writelines("    Mission = " + mission + "  parenthesis level=[" + str(n_depth) + "] \n")
                        outfile.writelines("    Parsing: (" + mission_fragment + ") \n")
                        new_missions = parse_mission(mission_fragment)
                        for item in new_missions:
                            new_string = pre_mission + item + post_mission
                            if "::" in new_string:
                                new_string = new_string.replace("::", ":")
                            to_process.append(new_string)
                            outfile.writelines("    " + new_string + "\n")
                        current_depth = 0  # Changed to_process list, restart
                        print("\r        " + f"{len(to_process):,}" + " missions generated", end="")
                        break
                if mission[j] == ")":
                    n_depth -= 1
            new_to_process = to_process[1:]
            to_process = new_to_process.copy()
            current_depth -= 1      # Entire line processed, go up one depth
    outfile.write("    " + f"{len(processed):,}" + " missions generated")
    outfile.write("    Saving strings for ")
    for item in processed:
        outfile.write(" " + item)
    outfile.writelines("\n")
    outfile.writelines("--------------------------------------------------------------------------------------------\n")
    return processed


def listdepth(l):
    """
    Determines the 'deepness' of lists in lists
    """
    if isinstance(l, list):
        return 1 + max(listdepth(item) for item in l)
    else:
        return 0


def paren_depth(line):
    """
    Determines the 'deepness' of embedded parentheticals () of a given string
    """
    n_depth = 0
    max_depth = 0
    for i in range(len(line)):
        if line[i] == "(":
            n_depth += 1
        if line[i] == ")":
            n_depth -= 1
        if n_depth > max_depth:
            max_depth = n_depth
    return max_depth


def parse_mission(mission_fragment):
    """
    Takes the logic string (using + - _ ) and converts to number of path strings according to logic
    """
    # Note node names CANNOT have + , or _ in name
    actions = []
    path_strings = []
    # Break string into separate actions based operators
    #   THEN (_)  Replace _ with nodeA:nodeB:nodeC... string and single string in list
    #   AND (+)   Replace + with all combinations of nodeA,nodeB,nodeC... in list
    #   OR (-)    Replace , with each node... as individual items in list
    if "+" in mission_fragment:
        actions = mission_fragment.split("+")
        options = []
        permutations = list(itertools.permutations(actions))
        for combo in permutations:
            perm_string = ""
            for node in combo:
                if node[-1] == ":":
                    perm_string += node
                else:
                    perm_string += node + ":"
            options.append(perm_string)
        path_strings.append(options)
    elif "_" in mission_fragment:
        actions = mission_fragment.split("_")
        mystring = ""
        for step in actions:
            if step[-1] == ":":
                mystring += step
            else:
                mystring += step + ":"
        path_strings.append(mystring)
    elif "," in mission_fragment:
        actions = mission_fragment.split(",")
        for step in actions:
            if step[-1] == ":":
                path_strings.append(step + ":")
            else:
                path_strings.append(step + ":")
    else:
        path_strings.append(mission_fragment)
    while listdepth(path_strings) > 1:
        # if list of lists occur, flatten them to single list of items
        # Credit: https://stackoverflow.com/questions/952914/how-to-make-a-flat-list-out-of-list-of-lists/952952#952952
        merged = list(itertools.chain(*path_strings))
        path_strings = merged.copy()
    return path_strings


def get_all_nodes(filename):
    """
    Read data from ABN.csv file and get available nodes from the file
    These are direction dependent, data for A->B may differ from data for B->A
        [0] is the "from" node (the origin of movement)
        [1] is the "to" node (the destination)
        [2] is the distance from node0 to node1
        [3] is the vertical height change in feet
   """
    global log
    global ABN
    global delta_H
    logentry = []
    logentry.append("\n")
    logentry.append("------------------------------------------------------------------------------------------ \n")
    logentry.append("Connection data: \n")
    logentry.append("From Node - To Node = Distance \n")
    all_nodes = collections.OrderedDict()
    with open(filename, 'r') as inputfh:
        lines = inputfh.readlines()
    for line in lines:
        line = line.strip()
        if line[0] == '#':
            continue
        var = line.split(',')
        if var[0] not in all_nodes:
            all_nodes[var[0]] = collections.OrderedDict()
        if var[1] not in all_nodes[var[0]]:
            all_nodes[var[0]][var[1]] = {}
        # Unique From:To key for Dictionary value var[2]
        c_id = var[0] + "-" + var[1]
        c_val = var[2]
        h_val = var[3]
        logentry.append("  " + c_id + " = " + c_val + " feet \n")
        if c_id not in ABN and c_id != "-" and c_id is not None:
            ABN[c_id] = float(c_val)
            delta_H[c_id] = float(h_val)
    for line in logentry:
        log.writelines(line)
    return all_nodes


def get_all_breaches(BreachFilename, AONfilename):
    """
    Read data from file breaches.csv and get breach technique parameters:
        [0] Material (Conc_30)
        [1] Time to complete breach (270 sec)
        [2] Weight of consumable materials (35 lbs)
        [3-22] Weight of each non-consumable item identified in header (0,0,0... lbs)
    Read data from AON file and get available nodes from the file
        [0] is the Node ID (F08)'
        [1] Node Description (ICS C Divisional Pool South Wall)'
        [2] Node Material (Conc_90) - matches to Breaches File'
        [3] is the material-specific breaching method wights (E10,C10,,,,)
    """
    global log
    global breach_techniques
    global node_id
    global node_consum
    global node_time
    global node_tools
    breach_techniques = {}
    node_time = {}
    node_tools = {}
    node_consum = {}
    node_id = ['start']
    node_time['start'] = 0
    node_consum['start'] = 0
    node_tools['start'] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    logentry = []
    logentry.append("\n")
    logentry.append("------------------------------------------------------------------------------------------ \n")
    logentry.append("Available Breach Methods for each node: (Many be more than one method/node) \n")
    logentry.append("Node, Breach Time, Consumable lb, Non-Consumable Tool Methods lbs (1 -> n) \n")
    with open(BreachFilename, 'r') as inputfh:
        lines = inputfh.readlines()
    for line in lines:
        val = []
        val = line.split(",")
        my_key = val[0]
        if my_key != "#" and my_key != "":
            my_value = ",".join(val[1:23])
            breach_techniques[my_key] = my_value
    with open(AONfilename, 'r') as inputfh:
        lines = inputfh.readlines()
    for line in lines:
        line = line.strip()
        var = []
        var = line.split(",")
        if line[0] != '#':
            id = var[0]
            id = id.strip()
            node_id.append(id)
            matl = var[2]
            my_key = matl
            technique = breach_techniques[my_key].split(",")
            node_time[id] = int(technique[0])                  # time to perform breach in seconds
            node_consum[id] = int(technique[1])                # resource consumed in pounds
            tool = []
            for i in range(2, 22):
                tool.append(int(technique[i]))
            node_tools[id] = tool                  # stores weights of tools in pounds as a list = tool[0-19]
    return


def check_for_tsets(node_string):
    i = 0
    if node_string.find("#") < 0:           # Process if string does not have #
        node_string = node_string.replace('\n', '')
        node_string = node_string.replace('(', '( ')
        node_string = node_string.replace(')', ' )')
        node_string = node_string.replace('[', '( ')
        node_string = node_string.replace(']', ' )')
        node_string = node_string.replace('{', '( ')
        node_string = node_string.replace('}', ' )')
        nodes = node_string.split(" ")
        logic_string = ""
        for item in nodes:
            if "(" in item:
                this_item = " ( "
            elif ")" in item:
                this_item = " ) "
            elif "," in item:
                this_item = " or "
            elif "+" in item:
                this_item = " and "
            else:
                'This is the node ID, so add " in cur_path" to generate the boolean logic string'
                this_item = '"' + item + '" in cur_path '
                if item not in TSet_targets:
                    TSet_targets.append(item)
            logic_string = logic_string + this_item
        TSet_logic.append(logic_string)
        log.writelines("    Target Set " + str(i) + " - " + node_string)
        i += 1
    return


def get_nodes_in_logic(filename):
    """
    Extract nodes from Target Set Logic
    """
    global log
    global TSet_logic
    global TSet_targets
    TSet_logic = []
    TSet_targets = []
    nodes = collections.OrderedDict()
    nodes = []
    i = 0
    log.writelines("\n")
    log.writelines("------------------------------------------------------------------------------------------ \n")
    log.writelines("Target Set Logic & Associated nodes: \n")
    if not os.path.exists(filename):
        log.writelines("ERROR: no TSET Logic file \n")
        print('ERROR: no TSET Logic file')
        sys.exit(1)
    with open(filename, 'r') as fh:
        lines = fh.readlines()
        for line in lines:
            if line.find("#") < 0:
                log.writelines("    Target Set " + str(i) + " - " + line)
                i += 1
                logic = line.strip("\n")
                TSet_logic.append(logic)
                nodelist = list(logic)
                these_nodes = []
                working = ""
                for my_char in nodelist:
                    if my_char not in "()":
                        if my_char in "+_,":
                            my_char = " "
                        working += my_char
                if " " in working:
                    these_nodes = working.split(" ")
                else:
                    these_nodes.append(working)
                for node in these_nodes:
                    if node not in TSet_targets and node != "" and node != " ":
                        TSet_targets.append(node)
    log.writelines("\n")
    log.writelines("\n")
    TSet_targets.sort()
    return TSet_targets


def last_occurrence(node, path):
    """
    Finds last occurrence of node in a list of nodes
    """
    foundit = 0
    i_loop = 0
    for checknode in path:
        if checknode == node:
            foundit = i_loop
        i_loop += 1
    result = foundit
    return result


def step_summary(start_time, end_time, step, description, value):
    """
    Writes end of step work summary to log, details, and screen
    """
    global header
    elapsed = end_time - start_time
    et_hr = int(elapsed / 3600)
    et_min = int((elapsed - int(et_hr) * 3600) / 60)
    et_sec = int((elapsed - int(et_hr) * 3600 - int(et_min) * 60))
    if elapsed > 3600:
        tmp0 = str(et_hr) + ":" + str(et_min).zfill(2) + ":" + str(et_sec).zfill(2)
    elif elapsed > 60:
        tmp0 = str(et_min).zfill(2) + ":" + str(et_sec).zfill(2)
    else:
        tmp0 = "{:.3f}".format(elapsed) + " seconds"
    tmp1 = "Step " + step + " - " + str(f"{value:,d}") + " " + description + " processed in "
    print("    " + tmp1 + tmp0)
    log.writelines("    " + tmp1 + tmp0 + "\n")
    details.writelines(header)
    details.writelines("#    " + tmp1 + tmp0 + "\n")
    details.writelines(header)
    return


def perm(scenario, t, c, nc):
    """
    Takes strings from a list of lists and returns a list of all permutations of those strings in the list (in order of
    appearance in the original list of lists). Creates list of all paths through waypoints in one scenario (A:B:C:D...)
    """
    invalid = open('Invalid_Paths.txt', 'a')
    result = scenario.copy()
    n = len(result)         # set initial value for number of lists in list of lists
    # If one of the segments list is empty (no valid paths), then end with results = null set
    for x in range(0, n):
        my_segment = result[x]
        if not my_segment:     # If segment list is empty
            result = []
            return result
    if result[-1][0] == "":     # If last line in list is a blank set, delete it
        del result[-1]
    new_list = []           # initialize new_list
    while n > 1:            # as long as there are at least two list remaining, continue
        list1 = result[-1]  # extract the last list in the list of lists
        list2 = result[-2]  # extract the next to last list in the list of lists
        values1 = []
        values2 = []
        for item2 in list2:         # loop through all items in the last two lists to generate permutations
            for item1 in list1:     # keep list 2 in outer loop to keep order earlier -> later in scenario
                valid = True
                # time & resources
                r_limit = item1.find("]")
                parse1 = item1[1:r_limit]
                values1 = parse1.split(",")
                r_limit = item2.find("]")
                parse2 = item2[1:r_limit]
                values2 = parse2.split(",")
                new_ET = float(values1[0]) + float(values2[0])
                new_consum = float(values1[1]) + float(values2[1])
                new_nonconsum = float(values1[2]) + float(values2[2])
                new_values = "[" + "{:.0f}".format(new_ET).zfill(5) + "," \
                             + "{:.0f}".format(new_consum).zfill(3) + "," \
                             + "{:.0f}".format(new_nonconsum).zfill(3) + "] "
                if new_ET > t or new_consum > c or new_nonconsum > nc:       # check to see if path meets max limits
                    valid = False
                # Tool weights
                l1_limit = item1.rfind("<")
                r1_limit = item1.find(">")
                tools1 = item1[l1_limit + 1:r1_limit]
                toolvalues1 = tools1.split(",")
                l2_limit = item2.rfind("<")
                r2_limit = item2.find(">")
                tools2 = item2[l2_limit + 1:r2_limit]
                toolvalues2 = tools2.split(",")
                for i in range(0, len(toolvalues1) - 1):
                    if int(toolvalues1[i]) > int(toolvalues2[i]):
                        toolvalues2[i] = toolvalues1[i]
                new_toolstring = "<" + ",".join(str(x) for x in toolvalues2) + ">"
                # combined path
                ls1_limit = item1.rfind(">") + 1
                path1 = item1[ls1_limit:]
                l_limit = path1.find("-")
                path1 = path1[l_limit:]     # strip off the first node since it is repeated in both strings
                ls2_limit = item2.rfind(">") + 1
                path2 = item2[ls2_limit:]
                new_items = path2 + path1    # create a new string by adding the current item2 and item1
                test_string = new_values + new_toolstring + new_items
                if valid:
                    new_list.append(new_values + new_toolstring + new_items)
                else:
                    invalid.writelines(new_values + new_toolstring + new_items + "\n")
            # Need to return and get two new lists to combine
        if len(result) > 1:                 # if not the last list then
            result[-2] = new_list.copy()    # after the loops are complete, assign the new list to the next to last list
            del result[-1]                  # and delete the last list (list of lists is now one list shorter)
            new_list.clear()                # then finally clear the working list for the next trip
        n = len(result)         # reset the number of list in the list of lists and check while n > 1 for completion
    invalid.close()
    return result


def save_eval_pickle():
    # Code Source: stackoverflow.com/questions/11218477/how-can-i-use-pickle-to-save-a-dict
    with open('eval_segments.pickle', 'wb') as handle:
        pickle.dump(eval_segments, handle, protocol=pickle.HIGHEST_PROTOCOL)
    return


def save_paths_pickle():
    # Code Source: stackoverflow.com/questions/11218477/how-can-i-use-pickle-to-save-a-dict
    with open('segment_paths.pickle', 'wb') as handle:
        pickle.dump(segment_paths, handle, protocol=pickle.HIGHEST_PROTOCOL)
    return


def save_pathdata_pickle():
    # Code Source: stackoverflow.com/questions/11218477/how-can-i-use-pickle-to-save-a-dict
    with open('segment_pathdata.pickle', 'wb') as handle:
        pickle.dump(segment_pathdata, handle, protocol=pickle.HIGHEST_PROTOCOL)
    return


def load_pickle(filename):
    # Code Source: stackoverflow.com/questions/11218477/how-can-i-use-pickle-to-save-a-dict
    unpickle_filename = filename + '.pickle'
    if path.exists(unpickle_filename):
        with open(unpickle_filename, 'rb') as handle:
            unserialized_data = pickle.load(handle)
    else:
        print(unpickle_filename + " does not exist - loaded nothing")
        unserialized_data = {}
    return unserialized_data


def load_g_from_file():
    # Code Source: geeksforgeeks.org/find-paths-given-source-destination/  by Neelam Yadav
    global g
    global ABN
    global node_id
    global node_number
    node_number = {}
    g = {}
    i = 0
    for node in node_id:
        node_number[node] = i
        g[i] = []
        i += 1
    for k, v in ABN.items():
        dash = k.find("-")
        k1 = k[:dash]
        k2 = k[dash+1:]
        x1 = node_number[k1]
        x2 = node_number[k2]
        if x1 in g:
            g_list = g[x1]
        else:
            g_list = []
        g_list.append(x2)
        g[x1] = g_list


def print_all_paths(datapack, working, ready4dict, step1_log):
    s = datapack['start']
    d = datapack['dest']
    segment_paths = {}
    segment_pathdata = {}
    paths_file = datapack['paths_filename']
    pathdata_file = datapack['pathdata_filename']
    node_id = datapack['node_id']
    visited = {}
    for i in range(0, len(node_id)):
        visited[i] = False
    path = []
    depth = 0
    segment_paths, segment_pathdata = print_all_paths_util(s, d, visited, path, depth, segment_paths, segment_pathdata,
                                                           datapack, step1_log)
    total_paths = 0
    for k in segment_paths:
        total_paths += len(segment_paths[k])
    total_pathdata = len(segment_pathdata)
    if total_paths != total_pathdata:
        print("ERROR:  total_paths=" + str(total_paths) + "   total_pathdata=" + str(total_pathdata))
        step1_log.append("ERROR:  total_paths=" + str(total_paths) + "   total_pathdata=" + str(total_pathdata))
    start_node = node_id[s]
    dest_node = node_id[d]
    this_key = start_node + ":" + dest_node
    if this_key in segment_paths and segment_paths[this_key] == []:
        print('       ' + this_key + ' added to dictionary with paths but no valid solutions')
        step1_log.append('       '+ this_key + ' added to dictionary with paths but no valid solutions')
    if this_key not in segment_paths:  # Add key and null set to show key was evaluated
        nullset = []
        segment_paths[this_key] = nullset
    c = Thread(target=save_this_data(this_key, paths_file, segment_pathdata, pathdata_file, ready4dict, working, step1_log))
    c.start()
    c.join()


def save_this_data(this_key, paths_file, segment_pathdata, pathdata_file, ready4dict, working, step1_log):
    # ========================================================================
    # Create working file name - this name used until file is complete, then replace with final name
    # These files are opened/reloaded to dictionary when they exist when restarting an interrupted run
    # Incomplete files cause crashes when trying to open/read so use temp file until file is complete
    f0 = this_key.replace(":", "-")
    f1 = "working_pathdata_" + f0 + ".txt"
    f_pathdata = open(f1, "w")
    for key, value in segment_pathdata.items():
        value_string = ""
        for item in value:
            value_string += str(item) + ", "
        data_string = key + " : " + value_string
        f_pathdata.writelines(data_string + "\n")
    f_pathdata.close()
    print("        Finalizing", paths_file)
    ready4dict.append(pathdata_file)
    working.remove(pathdata_file)
    os.rename(f1, pathdata_file)


def print_all_paths_util(u, d, visited, path, depth, segment_paths, segment_pathdata, datapack, step1_log):
    g = datapack['g']
    node_id = datapack['node_id']
    node_time = datapack['node_time']
    node_tools = datapack['node_tools']
    node_consum = datapack['node_consum']
    max_consumables = datapack['max_consumables']
    max_time = datapack['max_time']
    max_weight = datapack['max_weight']
    depth += 1
    visited[u] = True
    path.append(u)
    my_path = ""
    my_list = []
    nullset = []
    if u == d:  # If current vertex is same as destination, then print current path[]
        start_node = node_id[path[0]]
        dest_node = node_id[path[-1]]
        this_key = start_node + ":" + dest_node
        total_consum = 0
        total_time = 0
        total_weight = 0
        new_tools = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        for item in path:
            item_id = node_id[item].strip()
            if len(my_path) > 1:
                my_path += "-" + item_id
            else:
                my_path = item_id
            total_consum += node_consum[item_id]
            total_time += node_time[item_id]
            old_tools = node_tools[item_id]
            total_weight = total_consum
            for i in range(0, 19):
                if old_tools[i] > new_tools[i]:
                    new_tools[i] = old_tools[i]
                total_weight += new_tools[i]
        # check resources
        if this_key not in segment_paths:  # Add key and null set to show key was evaluated
            segment_paths[this_key] = nullset
        if total_consum <= max_consumables and total_time <= max_time and total_weight <= max_weight:
            # if it exists then else default
            working_segs = segment_paths.get(this_key, [])
            working_segs.append(my_path)
            segment_paths[this_key] = working_segs  # Update existing set or nullset with new path
            my_list.clear()
            my_list.append(total_time)
            my_list.append(total_consum)
            my_list.append(total_weight)
            my_list.append(new_tools)
            segment_pathdata[my_path] = my_list
            tool_string = "["
            for i in new_tools:
                tool_string += str(i) + ","
            tool_string += "]"
    else:  # If the current vertex is not the destination  Recurse all the vertices adjacent to this vertex
        for i in g[u]:
            if not visited[i]:
                segment_paths, segment_pathdata = print_all_paths_util(i, d, visited, path, depth, segment_paths,
                                                                       segment_pathdata, datapack, step1_log)
    path.pop()
    depth -= 1
    visited[u] = False
    return segment_paths, segment_pathdata


def build_pickles(f, paths, pathdata, ready4dict, step1_log):
    global segments
    if os.path.isfile(f):
        seg_name_start = f.rfind("\\")
        seg_name_end = f.rfind(".")
        this_seg = f[seg_name_start + 1:seg_name_end]
        this_seg = this_seg.replace("Paths_", "")
        this_seg = this_seg.replace("_", ":")
        f_paths = f
        f_pathdata = f.replace("Paths_", "PathData_")
        paths_file = open(f_paths, "r")
        pathdata_file = open(f_pathdata, "r")
        this_list = []
        data_list = []
        tool_list = []
        for line in paths_file:
            line = line.replace("\n", "")
            this_list.append(line)
        path_index = []
        print("           ", time.strftime("%H:%M:%S"), "Appending Segments for", len(this_list), "items")
        for item in this_list:
            if item not in segments:
                n = len(segments)       # n will be segments next index number - saves time vs adding then looking it up
                segments.append(item.strip())
            else:
                n = segments.index(item)
                print("               ", time.strftime("%H:%M:%S"), "already in list, index=", n)
            path_index.append(n)
        key = this_seg.strip()
        paths[key] = copy.deepcopy(path_index)
        this_list.clear()
        path_index.clear()
        for line in pathdata_file:
            line = line.replace("\n", "")
            my_var = line.split(":")
            this_path = my_var[0].strip()
            key = segments.index(this_path)
            data_string = my_var[1]
            data_string = data_string.replace("[", "")
            data_string = data_string.replace("]", "")
            data_var = data_string.split(",")
            data_list.clear()
            data_list.append(int(data_var[0]))
            data_list.append(int(data_var[1]))
            data_list.append(int(data_var[2]))
            tool_list.clear()
            for m in range(3, 23):
                tool_list.append(int(data_var[m]))
            data_list.append(tool_list)
            pathdata[key] = copy.deepcopy(data_list)
        ready4dict.remove(f)
        total_paths = 0
        for k in paths:
            total_paths += len(paths[k])
        total_pathdata = len(pathdata)
        if total_paths != total_pathdata:
            print("ERROR:  total_paths=" + str(total_paths) + "   total_pathdata=" + str(total_pathdata))
            step1_log.append("ERROR:  total_paths=" + str(total_paths) + "   total_pathdata=" + str(total_pathdata))
    else:
        print("ERROR:", f, 'does not exist')
    print("           ", time.strftime("%H:%M:%S"), " Pickles complete for", f)
    return paths, pathdata


def list2string(this_path, this_data):
    t = int(this_data[0])
    c = int(this_data[1])
    nc = int(this_data[2])
    data_string = "[" + str(t).zfill(5) + "," + str(c).zfill(3) + "," + str(nc).zfill(3) + "], <"
    for i in range(3, 22):
        w = int(this_data[i])
        data_string += str(w).zfill(3) + ","
    w = int(this_data[22])
    data_string += str(w).zfill(3) + ">, "
    data_string += this_path
    return data_string

def string2list(this_string):
    this_string.replace("[", "")
    this_string.replace("<", "")
    this_string.replace("]", "")
    my_data = this_string.split(">,")
    data_list = []
    this_path = my_data[1]
    temp = my_data[0].split(",")
    for x in temp:
        data_list.append(int(x))
    return this_path, data_list


def main():
    """
    Main control point for evaluating target set paths
    """
    global log
    global version
    global AON
    global ABN
    global delta_H
    global breach_techniques
    global TSets
    global Safeguards_Data
    global adv_speed
    global max_time
    global max_consumables
    global max_weight
    global ascend_fatigue
    global descend_fatigue
    global cutoff
    global backwards_compatible
    global cutoff_fastest
    global cutoff_lightest
    global client
    global route_depth
    global n_reserved
    global choke
    AON = collections.OrderedDict()
    ABN = collections.OrderedDict()
    delta_H = collections.OrderedDict()
    breach_techniques = collections.OrderedDict()
    # ===================================================================================
    # Open Setup.txt and read parameters from input parameters...
    # Defaults:
    Safeguards_Data = False
    client = "PathFinder+ Testing"
    adv_speed = 11
    max_time = 2222
    max_consumables = 333
    max_weight = 444
    ascend_fatigue = 0.5
    descend_fatigue = 0.05
    cutoff_fastest = 6
    cutoff_lightest = 7
    backwards_compatible = False
    route_depth = 10
    with open('Setup.txt') as f:
        lines = [line.rstrip() for line in f]
    for line in lines:
        var = line.split('=')
        if "safeguards = " in line or "Safeguards = " in line:
            if var[1].lower().strip() == "true" or var[1].lower().strip() == "yes":
                Safeguards_Data = True
            else:
                Safeguards_Data = False
        if "client = " in line:
            client = var[1]
        if "adv_speed = " in line:
            adv_speed = int(var[1])
        if "max_time = " in line:
            max_time = int(var[1])
        if "max_consumables = " in line:
            max_consumables = int(var[1])
        if "max_weight = " in line:
            max_weight = int(var[1])
        if "ascend_fatigue = " in line:
            ascend_fatigue = float(var[1])
        if "descend_fatigue = " in line:
            descend_fatigue = float(var[1])
        if "cutoff_fastest = " in line:
            cutoff_fastest = int(var[1])
        if "cutoff_lightest = " in line:
            cutoff_lightest = int(var[1])
        if "route_depth = " in line:
            route_depth = int(var[1])
        if "choke_points = " in line:
            choke = []
            temp = var[1]
            choke = temp.split(",")
        if "reserved_processors = " in line:
            n_reserved = int(var[1])
        if "backwards_compatible = " in line or "Backwards_compatible = " in line or "Backwards_Compatible = " in line:
            if var[1].lower().strip() == "true" or var[1].lower().strip() == "yes":
                backwards_compatible = True
            else:
                backwards_compatible = False
    # ================================================================================================================
    # Revision History:
    #     Version 1.0.1 - Nov 30, 2020 - Reimagination of Original Pathfinder to address incomplete route identification
    #     Version 1.1.0 - Dec 16, 2020 - Multiprocessor support added to Step 1, merged Class Graph into main code,
    #                                    and improved whitespace stripping to avoid string errors
    #     Version 1.1.1 - Dec 31, 2020 - Added stop/restart capability unintentionally omitted when converting Ver 1.0.1
    #     Version 1.1.2 - Jan 18, 2020 - Rewrote to reduce memory requirements for very large networks
    #     Version 1.1.3 - Jan 28, 2020 - Rewrote to fix error introduced in 1.1.2 when changed data format from string
    # ================================================================================================================
    version = "Version 1.1.3"
    release_date = "Jan 28, 2020"
    author = "Copyright J.Randy Ford"
    #      00000000011111111112222222222333333333344444444445555555555666666666677777777778888888888999999999900000
    #      12345678901234567890123456789012345678901234567890123456789012345678901234567890123456789012345678901234
    print("=======================================================================================================")
    print("                                                                                                       ")
    print("         PPPPP    AAAA   TTTTTTT  H    H  FFFFF  III  N     N  DDDDD    EEEEE  RRRRR                   ")
    print("         P    P  A    A     T     H    H  F       I   NN    N  D    D   E      R    R      ++          ")
    print("         P    P  A    A     T     H    H  F       I   NN    N  D     D  E      R    R      ++          ")
    print("         PPPPP   A    A     T     HHHHHH  FFFFF   I   N N   N  D     D  EEEE   RRRRR    ++++++++       ")
    print("         P       AAAAAA     T     H    H  F       I   N  N  N  D     D  E      R R      ++++++++       ")
    print("         P       A    A     T     H    H  F       I   N   N N  D     D  E      R  R        ++          ")
    print("         P       A    A     T     H    H  F       I   N    NN  D    D   E      R   R       ++          ")
    print("         P       A    A     T     H    H  F      III  N     N  DDDDD    EEEEE  R    R                  ")
    print("                                                                                                       ")
    line_length = 104
    spacer_length = int((line_length - len(version) - len(release_date) - len(author) - 5)/2)
    spacer = " " * spacer_length
    print(spacer + version + " " + release_date + "     " + author)
    mytext = "Evaluation of " + client.strip() + " target set paths and required timing/resources"
    spacer_length = int((line_length-len(mytext))/2)
    spacer = " " * spacer_length
    print(spacer + mytext)
    print("=======================================================================================================")
    print("  ")
    log = open('Log.txt', 'w')
    if Safeguards_Data:
        log.writelines("------------------------------------------------------------------------------------------- \n")
        log.writelines("                      ---> SAFEGUARDS INFORMATION  (10 CFR 73.21) <---                      \n")
        log.writelines("Information in this file is protected from unauthorized release as SAFEGUARDS INFORMATION.  \n")
        log.writelines("Violation of Section 147 of the Atomic Energy Act is subject to CIVIL and CRIMINAL Penalties\n")
        print("------------------------------------------------------------------------------------------- ")
        print("                      ---> SAFEGUARDS INFORMATION  (10 CFR 73.21) <---                      ")
        print("Information in this file is protected from unauthorized release as SAFEGUARDS INFORMATION.  ")
        print("Violation of Section 147 of the Atomic Energy Act is subject to CIVIL and CRIMINAL Penalties")
        print("------------------------------------------------------------------------------------------- ")
    else:
        log.writelines("------------------------------------------------------------------------------------------ \n")
        log.writelines("<><><><><><><><><><><><><><><><><><><>< ATTENTION: ><><><><><><><><><><><><><><><><><><><> \n")
        log.writelines("This is a development/demo version ONLY.  The Target Set locations used are NOT valid.  \n")
        log.writelines("The Target Set Elements and the actual location will be updated in the SGI Version.     \n")
        log.writelines("Likewise, input parameters are NOT actual values and will be updated in the SGI Version.\n")
        log.writelines("To activate SGI Headers - Enter Safeguards = True on line in setup.txt file.            \n")
    log.writelines("Date: " + time.strftime("%a %b %d, %Y") + "   User must properly mark & store this document.\n")
    log.writelines("------------------------------------------------------------------------------------------  \n")
    log.writelines("    PathFinder+ " + version + " - Copyright J Randy Ford 2019-2020 - all rights reserved    \n")
    log.writelines("    Analysis of " + client + "     Run started at " + time.strftime("%H:%M:%S %a %b %d, %Y") + "\n")
    log.writelines("------------------------------------------------------------------------------------------  \n")
    log.close()
    log = open('Log.txt', 'a')
    print(" ")
    print("Run started at " + time.strftime("%H:%M:%S %a %b %d, %Y"))
    print(" ")
    all_nodes = get_all_nodes('ABN.csv')
    get_all_breaches('Breaches.csv', 'AON.csv')
    tsenodes = get_nodes_in_logic('TSets+.txt')
    generate_paths(all_nodes, tsenodes)
    # ========================================================================
    # ToDo: Future Enhancement Ideas
    # ------------------------------------------------------------------
    # Make Step 2 interruptable - stop & restart due to potential length of processing time
    # ------------------------------------------------------------------------
    # Change Data Storage from Dict of string lists to Dict of Dict to see if improves speed by not having to process
    # strings each time segment is accessed
    # ------------------------------------------------------------------------
    # Focus needed_connections to only ones in logic not all nodes in logic.  Could cause future logic changes
    # to have to recalulate connections but would save some up-front calculations
    # ------------------------------------------------------------------
    # Validity - Get basis time from pickle file, Compare Date of AON/ABN to basis time using os.path.getmtime(path)
    # Delete pickles and Path_Files if AON or ABN have been updated since pickle and rebuild.
    # ------------------------------------------------------------------
    # Determine if tsenodes is used and if it can be removed
    # ========================================================================


if __name__ == "__main__":
    progdesc = '''Program to find internal paths that constitutes a complete target set.'''
    main()
