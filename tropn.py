#! /usr/bin/env python
# -*- coding: utf-8 -*-

# TROPN (Timed Resource Oriented Petri Nets) library for SNAKES
# Author: Claudio Morales D, claudio.morales@usach.cl, Github: cmoralesd
# Version 1.1, 06-2020
# License: cc-by-sa

import snakes.plugins
from snakes.data import MultiSet
from snakes.nets import Marking
from snakes import ConstraintError

@snakes.plugins.plugin("snakes.nets")
def extend (module) :
    class Transition (module.Transition) :
        def __init__ (self, name, guard=None, **args) :
            self.time = None
            self.min_time = args.pop("min_time", 0.0)
            self.max_time = args.pop("max_time", None)
            self.wait = args.pop("wait", 0)
            module.Transition.__init__(self, name, guard, **args)
        def enabled (self, binding, **args) :
            if args.pop("untimed", False) :
                return module.Transition.enabled(self, binding)
            elif self.time is None :
                return False
            elif self.max_time is None :
                return (self.min_time <= self.time) and module.Transition.enabled(self, binding)
            else :
                return (self.min_time <= self.time <= self.max_time) and module.Transition.enabled(self, binding)
    class Place (module.Place) :
        def __init__ (self, name, tokens=[], check=None, **args) :
            self.post = {}
            self.pre = {}
            self.bound = args.pop("bound", 0)
            self.wait = args.pop("wait", 0)
            module.Place.__init__(self, name, tokens, check, **args)
        def reset (self, tokens) :
            module.Place.reset(self, tokens)
            for name in self.post :
                trans = self.net.transition(name)
                if len(trans.modes()) > 0 :
                    trans.time = 0.0
                else :
                    trans.time = None
        def empty (self) :
            module.Place.empty(self)
            for name in self.post :
                self.net.transition(name).time = None
        def _post_enabled (self) :
            return dict((name, self.net.transition(name).time is not None)
                        for name in self.post)
        def add (self, tokens) :
            enabled = self._post_enabled()
            module.Place.add(self, tokens)
            for name in self.post :
                if not enabled[name] :
                    trans = self.net.transition(name)
                    if len(trans.modes()) > 0 :
                        trans.time = 0.0
        def remove (self, tokens) :
            enabled = self._post_enabled()
            module.Place.remove(self, tokens)
            for name in self.post :
                if enabled[name] :
                    trans = self.net.transition(name)
                    if len(trans.modes()) == 0 :
                        trans.time = None
    class PetriNet (module.PetriNet) :
        def __init__ (self, name, **args) :
            self.delays = args.pop("delays", {})
            module.PetriNet.__init__(self, name)
    return Transition, Place, PetriNet

class NetState:
    def __init__(self, marking, waiting, process):

        self.marking = marking # PetriNet Marking()
        self.waiting = waiting # dict like {transition_name:{wait, removed_tokens, reserved_tokens}}
        self.process = process # dict like {place_name:wait, processing_token}

    def __getitem__(self, marking):
        return self.marking

    def __getitem__(self, waiting):
        return self.waiting

    def __getitem__(self, process):
        return self.process

def states_are_equal(self, other):
        if self.marking != other.marking:
            # markings are not equals
            return False
        elif self.waiting.keys() != other.waiting.keys():
            # waiting keys are not equals
            return False
        elif self.process.keys() != other.process.keys():
            # process keys are not equals
            return False
        else:
            # check for elements:
            return not (any([self.waiting[key]['removed']!=other.waiting[key]['removed'] for key in self.waiting])
                        or any([self.waiting[key]['reserved']!=other.waiting[key]['reserved'] for key in self.waiting])
                        or any([self.process[key]['token']!=other.process[key]['token'] for key in self.process]))

def set_state(net, state):
    #set marking
    net.set_marking(state.marking)
    #set waiting time in transitions
    for t in net.transition():
        if t.name in state.waiting:
            t.wait = state.waiting[t.name]['wait']
        else:
            t.wait = 0
    #set process time in places
    for p in net.place():
        if p.name in state.process:
            p.wait = state.process[p.name]['wait']
        else:
            p.wait = 0
    return net
        
def marking_as_list(n, m):
# n: petri net
# m: marking
    u = [] # marking as a list
    for p in sorted(n.place()):
        if p.name in m:
            u.append([p.name,p.tokens])
        else:
            u.append([p.name,''])
    return u

def wait_time(n,tokenName, nodeName):
    wt = n.delays
    if tokenName in wt:
        if nodeName in wt[tokenName]:
            return wt[tokenName][nodeName]
        else:
            return 0
    else:
        return 0
    
def process(token):
    if '_' not in token:
        token = token+'_1'
    else:
        processID = int(token[-1]) + 1
        token = token[:len(token)-1]+str(processID)
    return token

def full_marking(s):
    m = s.marking
    r = Marking({})
    w = []
    for key in s.waiting.keys():
        for place in s.waiting[key]['removed'].keys():
            m = m + Marking({place+str('_r'):s.waiting[key]['removed'][place]})
    for key in s.process.keys():
        w.append({key+'_r':MultiSet(s.process[key]['token'])})
    for i in w:
        r = r + Marking(i)     
    return m+r

def next_state(n, current_state):
    m = current_state.marking
    waiting_for_firing = current_state.waiting
    place_in_process = current_state.process 
    # update waiting time for transitions
    for tname in waiting_for_firing:
        if n.transition(tname).wait>0:
            n.transition(tname).wait-=1
    # update waiting time for places in process
    to_remove = []
    for pname in place_in_process:
        if n.place(pname).wait>0:
            n.place(pname).wait-=1
        if n.place(pname).wait==0:
            # processing finished
            n.place(pname).remove('processing')
            n.place(pname).add(place_in_process[pname])
            to_remove.append(pname)
    for item in to_remove:
        place_in_process.pop(item)    
    # fire all enabled transitions
    for t in n.transition():
        m = n.get_marking()
        for s in t.modes():
            # check if waiting is needed
            token = token_in_process(s)
            wt = wait_time(n,token,t.name)
            if wt==0 and is_output_enabled(n,t.name) and (t.name not in waiting_for_firing):
            #no waiting is needed, fire at first round
                prev_tokens = {}
                for p in t.output():
                    prev_tokens.update({p[0].name:p[0].tokens.copy()})
                # no wait time, fire transition!
                t.fire(s) # <--- transition fires
                for p in t.output():
                    received = p[0].tokens - prev_tokens[p[0].name]
                    if p[0].tokens - prev_tokens[p[0].name] != {}:
                        # init process in place
                        # TO DO: enable multiple tokens on aoutput
                        token = received.items()[0]
                        wt = wait_time(n,token,p[0].name)
                        p[0].remove(received.items()[0])
                        p[0].wait = wt
                        p[0].add('processing')
                        place_in_process.update({p[0].name:token})
                break
            if wt>0 and is_output_enabled(n,t.name) and (t.name not in waiting_for_firing):
            #start wait time and reserve tokens
                t.wait = wt
                remove, reserve = reserveTokens(n,t,s)
                waiting_for_firing.update({t.name:{'removed':remove,'reserved':reserve,'s':s}})
                n.set_marking(m-remove+reserve)
                break
        if (t.name in waiting_for_firing) and t.wait==0:
        #wait time ended, restore reserved tokens and fire
            removed = waiting_for_firing[t.name]['removed']
            reserved = waiting_for_firing[t.name]['reserved']
            s = waiting_for_firing[t.name]['s']
            n.set_marking(m+removed-reserved)
            prev_tokens = {}
            for p in t.output():
                 prev_tokens.update({p[0].name:p[0].tokens.copy()})
            # fire transition!
            t.fire(s) # <--- transition fires
            for p in t.output():
                received = p[0].tokens - prev_tokens[p[0].name]
                if p[0].tokens - prev_tokens[p[0].name] != {}:
                    # init process in place
                    # TO DO: enable multiple tokens on aoutput
                    token = received.items()[0]
                    wt = wait_time(n,token,p[0].name)
                    p[0].remove(received.items()[0])
                    p[0].wait = wt
                    p[0].add('processing')
                    place_in_process.update({p[0].name:token})
            waiting_for_firing.pop(t.name)
    return NetState(m, waiting_for_firing, place_in_process)

def reserveTokens(n,t,s):
    #returns markings needed to reserve and remove tokens
    if t.activated(s):
        removeTokens = {}
        reserveTokens = {}
        for item in s.items():
            for inputPlace in t.input():
                if item[1] in inputPlace[0]:
                    removeTokens.update({inputPlace[0].name:MultiSet([item[1]])})

        for outputPlace in t.output():
            reserveTokens.update({outputPlace[0].name:MultiSet(['reserved'])})
        return Marking(removeTokens), Marking(reserveTokens)
    else:
        return Marking({}), Marking({})
    
def token_in_process(s):
    #Token name in substitution must be 2-char long and start with "X", i.e. "X1"
    for item in s.items():
        if 'X' in item[1]:
            token = item[1]
            return token

def is_output_enabled(net, t_name):
    enabled = True
    input_transitions = [t[0] for t in net.transition(t_name).input()]
    for item in net.transition(t_name).output():
        p = item[0]
        if p.bound == 0:
            # infinite capacity
            pass
        elif p in input_transitions:
            # place is self feed
            pass
        elif (len(p.tokens) == p.bound) and (p not in input_transitions):
            # place is full
            enabled = False
        else:
            # place is able to receive a token
            pass
    return enabled

def find_next_steps(n, current_state):
    # returns: new_state
    #          [a list of tuples (transition, substitution)]
    #          the number of epochs used to process
    waiting = current_state.waiting.copy()
    process = current_state.process.copy()
    set_state(n, current_state)
    next_steps = []
    epoch = 0
    search_again = True
    
    while search_again:
        nothing_done = True
        # update waiting time for transitions
        for tname in waiting:
            if waiting[tname]['wait']>0:
                waiting[tname]['wait']-=1
                nothing_done = False
            if waiting[tname]['wait']==0:
                # wait time ended, transition can fire
                pass
            n.transition(tname).wait = waiting[tname]['wait']
        
        # update waiting time for places
        to_remove = []
        for pname in process:
            if process[pname]['wait']>0:
                process[pname]['wait']-=1
                nothing_done = False
            if process[pname]['wait']==0:
                n.place(pname).remove('processing')
                n.place(pname).add(process[pname]['token'])
                to_remove.append(pname)
            n.place(pname).wait = process[pname]['wait']
        # remove ending processes from process list
        for item in to_remove:
            process.pop(item)
        
       
        
        #now search for enabled transitions
        for t in n.transition():
            m = n.get_marking()
            if t.name in waiting and t.wait==0:
                nothing_done = False
                # t ended waiting time
                removed = waiting[t.name]['removed']
                reserved = waiting[t.name]['reserved']
                s = waiting[t.name]['s']
                n.set_marking(m+removed-reserved)
                prev_tokens = {}
                for p in t.output():
                    prev_tokens.update({p[0].name:p[0].tokens.copy()})
                t.fire(s) # <--- transition fires
                for p in t.output():
                    received = p[0].tokens - prev_tokens[p[0].name]
                    if p[0].tokens - prev_tokens[p[0].name] != {}:
                        # init process in place
                        # TO DO: enable multiple tokens on aoutput
                        token = received.items()[0]
                        wt = wait_time(n,token,p[0].name)
                        p[0].remove(received.items()[0])
                        p[0].wait = wt
                        p[0].add('processing')
                        process.update({p[0].name:{'wait':wt,'token':token}})
                waiting.pop(t.name)
            
            for s in t.modes():
                if s in t.modes():
                    nothing_done = False
                    # check if waiting is needed
                    token = token_in_process(s)
                    wt = wait_time(n,token,t.name)
                    if wt==0 and is_output_enabled(n,t.name) and (t.name not in waiting):
                        #no waiting is needed, fire at first round
                        if (t.name,s) not in next_steps:
                            next_steps.append((t.name,s))

                    if wt>0 and is_output_enabled(n,t.name) and (t.name not in waiting):
                        #enabled with waiting time
                        if (t.name,s) not in next_steps:
                            next_steps.append((t.name,s))
        
        if nothing_done == False:
            epoch += 1
        
        if len(next_steps)>0 or (waiting=={} and process=={}):
            search_again = False
            return NetState(n.get_marking(), waiting, process), next_steps, epoch
        
        
        #--> next epoch, search again
        
def fire(n, state, tname, s):
    set_state(n, state)
    waiting = state.waiting.copy()
    process = state.process.copy()
    t = n.transition(tname)
    if t.enabled(s):
        token = token_in_process(s)
        wt = wait_time(n,token,tname)
        if wt==0:
            # fire immediately
            prev_tokens = {}
            for p in t.output():
                prev_tokens.update({p[0].name:p[0].tokens.copy()})
            t.fire(s) # <--- transition fires
            for p in t.output():
                received = p[0].tokens - prev_tokens[p[0].name]
                if p[0].tokens - prev_tokens[p[0].name] != {}:
                    # this is a process place, init process
                    # TO DO: enable multiple tokens in output places
                    token = received.items()[0]
                    wt = wait_time(n,token,p[0].name)
                    p[0].remove(received.items()[0])
                    p[0].wait = wt
                    p[0].add('processing')
                    process.update({p[0].name:{'wait':p[0].wait,'token':token}})
        else:
            #start wait time and reserve tokens
            t.wait = wt
            removeTokens = {}
            reserveTokens = {}
            for item in s.items():
                for inputPlace in t.input():
                    if item[1] in inputPlace[0]:
                        removeTokens.update({inputPlace[0].name:MultiSet([item[1]])})

            for outputPlace in t.output():
                reserveTokens.update({outputPlace[0].name:MultiSet(['reserved'])})
                
            remove = Marking(removeTokens)
            reserve = Marking(reserveTokens)
            waiting.update({t.name:{'wait':t.wait,'removed':remove,'reserved':reserve,'s':s}})
            n.set_marking(state.marking-remove+reserve)

    return NetState(n.get_marking(), waiting, process)

def time_feasible_reachability_tree(n, s0):
    #reachability tree
    markings = [] # list of all different markings
    todo = [] # list of pending to process states (NetState kind)
    tree = []  # list of all timed branches [init_marking, next_marking, transition, substitution, epoch]
    branching = []
    live = True
    todo.append(s0)   #init states from current
    
    # init reachability tree
    while live:
        # new search
        done = [] # list of processed states
        next_states = [] # list of new states found
        branches = []
        for current_state in todo:
            done.append(current_state)
            new_optimal_found = False
            if branching == []:
                # first branch added
                branches.append([[full_marking(current_state), full_marking(current_state), None, None, 0, 0]])
                current_branch =  branches[0]
            else:
                for i in range(len(branching)):
                    branch = branching[i]
                    if branch[-1][1] == full_marking(current_state):
                        current_branch = branch
                        current_branch_index = i
                        break
            # searching new markings
            if full_marking(current_state) not in markings:
                markings.append(full_marking(current_state))
                # new marking added
                # evolve current state and find next steps
                new_state, next_steps, e = find_next_steps(n, current_state)
                # searching for timed updated marking
                if full_marking(new_state) != full_marking(current_state):
                    arc = [full_marking(current_state), full_marking(new_state), None, None, e]
                    tree.append(arc)
                    this_arc = [full_marking(current_state), full_marking(new_state), None, None, e, current_branch[-1][5]+e]
                    current_branch.append(this_arc)
                    if full_marking(new_state) not in markings:
                        markings.append(full_marking(new_state))
                        # new marking added to list
                    else:
                        # evolved marking already in list
                        for previous_branch_index in range(len(branching)):
                            try:
                                previous_branch = branching[previous_branch_index]
                            except:
                                break
                            for previous_arc in previous_branch:
                                if previous_arc[0] == full_marking(new_state):
                                    # state found in other branch
                                    if previous_arc[5] < this_arc[5]:
                                        if previous_branch_index != current_branch_index:
                                            # current branch is unfeasible, deleting
                                            new_optimal_found = True
                                            branching.pop(current_branch_index)
                                    elif previous_arc[5] == this_arc[5]:
                                        # this route is as better than other
                                        # this kept, other is removed
                                        branching.pop(previous_branch_index)
                                    else:
                                        # this is the better route
                                        # this kept, other is removed
                                        branching.pop(previous_branch_index)
                                
                                if len(next_steps)==0 and previous_arc[1]==full_marking(new_state):
                                    #  final state found in other branch
                                    if previous_arc[5] < this_arc[5]:
                                        # a better route exists
                                        if previous_branch_index != current_branch_index:
                                            # current branch is unfeasible, deleting
                                            new_optimal_found = True
                                            branching.pop(current_branch_index)
                                    elif previous_arc[5] == this_arc[5]:
                                        #  this route is as better than other
                                        # this kept, other is removed
                                        branching.pop(previous_branch_index)
                                    else:
                                        # this is the better route
                                        # this kept, other is removed
                                        branching.pop(previous_branch_index)

                                                 
                if new_optimal_found:
                    continue
                    
                # next steps follow        
                for i in range(len(next_steps)):
                    step = next_steps[i]
                    # firing enabled transition
                    next_state = (fire(n, new_state, step[0], step[1]))
                    arc = [full_marking(new_state), full_marking(next_state), step[0], step[1], 0]
                    if arc not in tree:
                        # new transition arc added to reachability tree
                        tree.append(arc)
                    if full_marking(next_state) not in markings:
                        # new state to unfold
                        next_states.append(next_state)
                        
                    if i == 0:
                        if len(next_steps)>1:
                            copy_branch = [arc for arc in current_branch]
                        # adding 1 arc to current branch
                        arc = [full_marking(new_state), full_marking(next_state), step[0], step[1], 0,current_branch[-1][5]]
                        current_branch.append(arc)
                    else:
                        new_branch = [arc for arc in copy_branch]
                        # adding 1 arc to new branch
                        arc = [full_marking(new_state), full_marking(next_state), step[0], step[1],0, current_branch[-1][5]]
                        new_branch.append(arc)
                        branches.append(new_branch)
        
        for state in done:
            todo.pop(todo.index(state))
        
        # states"to do"
        for state in next_states:
            todo.append(state)
        
        for branch in branches:
            # new branch added
            branching.append(branch)
        
        if todo == []:
            live = False
                  
    steps = 0        
    index = 0
    branching.pop(0)
    for branch in branching:
        #branch.remove(branch[0])
        if len(branch) > steps:
            index = branching.index(branch)
            steps = len(branch)
    return markings, tree, branching[index]