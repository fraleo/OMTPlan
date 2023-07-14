#!/usr/bin/env python
"""
    Problem generator for the plant-watering domain.
"""
import argparse
import os
import random
import math
import sys

def get_instance_name(size, run, num_plants, num_agents):
    return 'instance_{}_{}_{}_{}'.format(size, num_plants, num_agents, run)


def parse_arguments():
    parser = argparse.ArgumentParser(description='Generate ext-plant-watering problem instances.')
    parser.add_argument("--max", default=20, help='Maximum grid size', type=int)
    parser.add_argument("--min",required=False, default=4,type=int)
    parser.add_argument("--num-agents",required=True, default=1,type=int)
    parser.add_argument("--output-dir", required=True, help='Output dir where the generated problems will be placed')
    parser.add_argument("--min-num-plants",required=True, default=None,type=int)
    parser.add_argument("--max-num-plants",required=True, default=None,type=int)
    parser.add_argument("--max-each-plant",required=False, default=10,type=int)
    parser.add_argument("--runs",required=False, default=1,type=int)
    args = parser.parse_args()

    assert args.max >= 4
    return args

class Instance():
    def __init__(self, name):
        self.name = name
        self.init = []
        self.goals = []
        self.objects = []

    def add_init(self, init):
        self.init.append(init)

    def add_goal(self, goal):
        self.goals.append(goal)

    def add_object(self, obj, t):
        self.objects.append((obj,t))

    # output the PDDL instance
    def print(self):
        s = ""
        s += f"(define (problem {self.name})\n"
        s += "(:domain ext-plant-watering)\n"
        s += "(:objects\n"
        for o,t in self.objects:
            s += f"\t{o} - {t}\n"
        s += ")\n"
        s += "(:init\n"
        for i in self.init:
            s += f"\t{i}\n"
        s += ")\n"
        s += "(:goal\n"
        s += "(and\n"
        for g in self.goals:
            s += f"\t{g}\n"
        s += ")))\n"
        return s

class MetricPDDLPrinter():

    def __init__(self, problem):
        self.problem = problem
        self.instance = Instance(problem.name)
        self.positions = []
        self.connections = []
        self.add_objects()
        self.add_init()
        self.add_goals()

    def add_objects(self):
        for o, t in self.problem.objects.items():
            self.instance.add_object(o, t)

    def add_init(self):
        self.instance.add_init("(= (maxx) {0})".format(self.problem.size))
        self.instance.add_init("(= (minx) 1)")
        self.instance.add_init("(= (maxy) {0})".format(self.problem.size))
        self.instance.add_init("(= (miny) 1)")
        self.instance.add_init("(= (total_poured) 0)")
        self.instance.add_init("(= (total_loaded) 0)")
        self.instance.add_init("(= (water_reserve) {0})".format(int(self.problem.water_capacity * 1.1)))

        counter = 0
        for o, t in self.problem.objects.items():
            if t == "agent":
                self.instance.add_init(f"(= (carrying {o}) 0)")
                self.instance.add_init(f"(= (max_carry {o}) 5)")
                #self.instance.add_init(f"(= (x {o}) {self.problem.agent_pos[counter][0]})")
                #self.instance.add_init(f"(= (y {o}) {self.problem.agent_pos[counter][1]})")
                counter += 1

        for o in self.problem.plants:
            self.instance.add_init("(= (poured {}) 0)".format(o))

        for elem, pos in self.problem.positions.items():
            self.instance.add_init("(= (x {0}) {1})".format(elem, pos[0]))
            self.instance.add_init("(= (y {0}) {1})".format(elem, pos[1]))

    def add_goals(self):
        for p in self.problem.plants:
            self.instance.add_goal("(= (poured {}) {})".format(p, self.problem.goal[p]))
        self.instance.add_goal("(= (total_poured) (total_loaded))")

    def get_domain_name(self):
        if self.constrained : return 'mt-' + self.problem.domain + '-constrained'
        return 'mt-' + self.problem.domain


class Problem(object):
    def __init__(self, name, domain, size, num_plants, num_agents, max_each_plant,num_taps=1):
        self.name = name
        self.domain = domain
        self.size = size
        self.num_agents = num_agents
        self.objects = {}  # Object-to-type map
        self.positions = {}  # Object-to-position map
        self.goal = {}  # The amount of pouring for each plant
        self.plants = []
        self.agent_pos = []
        self.water_capacity = 0

        # the set of all possible grid positions from where we will sample from.
        self.all_positions = []
        for i in range(1, self.size + 1):
            for j in range(1, self.size + 1):
                self.all_positions.append((i, j))

        # create plants: give them names and watering amount
        for i in range(1, num_plants + 1):
            plant_name = "plant{}".format(i)
            self.plants.append(plant_name)
            self.objects[plant_name] = "plant"
            self.goal[plant_name] = random.randint(1, max_each_plant)
            self.water_capacity += self.goal[plant_name]

        # create taps: give them name
        for i in range(1, num_taps + 1):
            self.objects["tap{}".format(i)] = "tap"

        # create agents: give them name
        for i in range(1, num_agents + 1):
            self.objects["agent{}".format(i)] = "agent"

        # define some extra constants
        self.total_loaded = 0
        self.total_poured = 0

        # Set random positions to plants, tap and agents
        positions = random.sample(self.all_positions, len(self.objects) + num_agents)  # We account for the agent position
        for i in range(1, num_agents + 1):
            self.agent_pos.append(positions[i])

        for i, o in enumerate(self.objects.keys(), num_agents):  # skip the first random position, assigned to the agent
            self.positions[o] = positions[i]


def Main():
    args = parse_arguments()
    base_dir = os.path.realpath(args.output_dir)
    random.seed( 383921 )
    if not os.path.exists( base_dir ) :
        print("Creating directory {0}".format(base_dir))
        os.makedirs( base_dir )

    for size in range(args.min, args.max + 1, 1):
        for num_plants in range(args.min_num_plants, args.max_num_plants + 1, 2):
            if size > 20 and size % 10 != 0 : continue
            for run in range(1, args.runs+1):
                name = get_instance_name(size, run, num_plants, args.num_agents)
                problem = Problem(name=name, domain="ext-plant-watering",
                                  size=size, max_each_plant = args.max_each_plant, num_plants= num_plants, num_agents=args.num_agents)
                pp = MetricPDDLPrinter(problem)  # The PDDL2.1 + state constraints versions
                with open(os.path.join(base_dir, name + ".pddl") , 'w') as f:
                    f.write(pp.instance.print())

if __name__ == "__main__":
    Main()
