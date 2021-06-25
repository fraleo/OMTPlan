import sys
import random
import numpy as np

max_priority = 3
min_priority = 1



def domainGenerator(nd,nl):


    domain = "(define (domain security-clearance)\n\n"

    req = "\t(:requirements :strips :typing :negative-preconditions :fluents)\n\n"
    
    ## Define ground predicates
    
    gp = []

    for d in range(1,nd):
        for l in range(1,nl):
            gp.append("\t\t(clear_d{}_l{})".format(d,l))

    predicates = "\t(:predicates \n{}\n\t)\n\n".format("\n ".join(gp))

    ## Define functions

    gc = []

    gp = []

    for d in range(1,nd):
        gc.append("\t\t(cost_d{})".format(d))
        gp.append("\t\t(priority_d{})".format(d))
    gp.append("\t\t(high)")
    gp.append("\t\t(low)")

    functions =  "\t(:functions \n{}\n\t)\n\n".format("\n ".join(gc + gp))

    ## Define actions

    ga = []


    


    for d in range(1,nd):
        ## Increase priority

        a = "\t(:action increase_priority_d{}\n".format(d)
        a = a +"\t\t:parameters ( )\n"

        pre = ["(< (priority_d{}) (high))".format(d)]
        eff = ["(increase (priority_d{}) 1)".format(d)]
        eff.append("(increase (cost_d{}) (priority_d{}) )".format(d ,d))
##        eff.append("(increase (cost_d{}) (high))".format(d))
        
        a = a + "\t\t:precondition (and {} )\n".format(" ".join(pre))

        a = a + "\t\t:effect (and {})\n".format(" ".join(eff))

        a = a + "\t)\n\n"

        ga.append(a)



        ## Authorize all 

        a = "\t(:action authorize_all_d{}\n".format(d)
        a = a +"\t\t:parameters ( )\n"

        pre = []
        eff = []

        pre.append("(>= (priority_d{}) (high))".format(d))


        for l in range(1,nl):
            pre.append("(not (clear_d{}_l{}))".format(d,l))
            eff.append("(clear_d{}_l{})".format(d,l))

        eff.append("(increase (cost_d{}) {})".format(d,  nl-1))
        
        a = a + "\t\t:precondition (and {} )\n".format(" ".join(pre))

        a = a + "\t\t:effect (and {})\n".format(" ".join(eff))

        a = a + "\t)\n\n"

        ga.append(a)
        
        for l in range(1,nl):
            a = "\t(:action authorize_d{}_l{}\n".format(d,l)
            a = a +"\t\t:parameters ( )\n"
            a = a + "\t\t:precondition (and (not (clear_d{}_l{})))\n".format(d,l)
            
            eff = ["(clear_d{}_l{})".format(d,l)]

            for j in range(1,   l):

                eff.append("(not (clear_d{}_l{}))".format(d,j))

            eff.append("(increase (cost_d{}) {})".format(d, l))
            
            a = a + "\t\t:effect (and {})\n".format(" ".join(eff))
            a = a + "\t)\n\n"
            ga.append(a)
        

    actions = "".join(ga)
    

    return domain + req  + predicates + functions + actions  + ")"

def problemGenerator(nd, nl):

   
    pb = "(define (problem security-clearance-{}-{})\n\n\t(:domain security-clearance)\n\n".format(nd-1,nl-1)

    ip = []

    ic = []


    for d in range(1,nd):
        for l in range(1,nl):
            ip.append("\t\t(not (clear_d{}_l{}) )".format(d,l))

        ic.append("\t\t(= (cost_d{}) 0)".format(d))
        ic.append("\t\t(= (priority_d{}) 1)".format(d))
        ic.append("\t\t(= (high) 3)")
        ic.append("\t\t(= (low) 1)")


    init = "\t(:init\n {}\n{}\n\t)\n\n".format("\n ".join(ip), "\n ".join(ic))

    ip = []

    for d in range(1,nd):
        for l in range(1,nl):
            ip.append("\t\t(clear_d{}_l{} )".format(d,l))


    goal = "\t(:goal (and\n {})\n\t)\n\n".format("\n ".join(ip))

    
    m  = ' (cost_d{})'.format(1)
    if nd > 2:
        for k in reversed(range(1,nd-1)):
            m = '(+ (cost_d{}) {})'.format(k+1, m)

    metric = "\t(:metric minimize {})\n\n".format(m)


    return pb + init + goal + metric + ")"

def main():
    import os

    nd = int(sys.argv[1]) 
    nl = int(sys.argv[2]) 

    directory = 'sec_clear_{}_{}-linear'.format(nd,nl)

    if not os.path.exists(directory):
        os.makedirs(directory)
        os.makedirs(directory+'/instances')

   
    domain = domainGenerator(nd+1,nl+1)
    pb = problemGenerator(nd+1,nl+1)

    fo = open(directory+'/domain.pddl', 'w+')
    fo.write(domain) 
    fo.close()

    fo = open(directory+'/instances/prob_{}_{}.pddl'.format(nd,nl), 'w+')
    fo.write(pb)
    fo.close() 


    
            
    

if __name__==  '__main__':
    main()
