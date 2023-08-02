; IPC5 Domain: Pathways ComplexPreferences
; Authors: Yannis Dimopoulos, Alfonso Gerevini and Alessandro Saetti 

(define (domain Pathways-Metric) 
;(:requirements :typing :fluents)  

(:types level molecule - object
	simple complex - molecule) 

(:predicates (association-reaction ?x1 ?x2 - molecule ?x3 - complex)
	     (catalyzed-association-reaction ?x1 ?x2 - molecule ?x3 - complex)
             (catalyzed-self-association-reaction ?x1 - molecule ?x3 - complex)
	     (synthesis-reaction ?x1 ?x2 - molecule)
             (possible ?x - molecule) 
	     (chosen ?x - simple))

(:functions (available ?x - molecule)
	    (duration-association-reaction ?x1 ?x2 - molecule ?x3 - complex)
	    (duration-catalyzed-association-reaction ?x1 ?x2 - molecule ?x3 - complex)
	    (duration-catalyzed-self-association-reaction ?x1 - molecule ?x3 - complex)
	    (duration-synthesis-reaction ?x1 ?x2 - molecule)
	    (need-for-association ?x1 ?x2 - molecule ?x3 - complex)
	    (need-for-catalyzed-association ?x1 ?x2 - molecule ?x3 - complex)
            (need-for-catalyzed-self-association ?x1 - molecule ?x3 - complex)
	    (need-for-synthesis ?x1 ?x2 - molecule)
	    (prod-by-association ?x1 ?x2 - molecule ?x3 - complex)
	    (prod-by-catalyzed-association ?x1 ?x2 - molecule ?x3 - complex)
            (prod-by-catalyzed-self-association ?x1 - molecule ?x3 - complex)
	    (prod-by-synthesis ?x1 ?x2 - molecule)
	    (num-subs))

(:action choose
 :parameters (?x - simple)
 :precondition (and (possible ?x) )
 :effect  (and 
	    (chosen ?x) 
	    (not (possible ?x)) 
	    (increase (num-subs) 1)
	  )
)

(:action initialize
 :parameters (?x - simple)
 :precondition (and (chosen ?x))
 :effect (and  (increase (available ?x) 1))
)

(:action associate
 :parameters (?x1 ?x2 - molecule ?x3 - complex)
 :precondition (and (>= (available ?x1) (need-for-association ?x1 ?x2 ?x3)) 
		 (>= (available ?x2) (need-for-association ?x2 ?x1 ?x3))
		 (association-reaction ?x1  ?x2  ?x3))
 :effect (and (decrease (available ?x1) (need-for-association ?x1 ?x2 ?x3))
	      (decrease (available ?x2) (need-for-association ?x2 ?x1 ?x3))
	      (increase (available ?x3) (prod-by-association ?x1 ?x2 ?x3))))

(:action associate-with-catalyze
 :parameters (?x1 ?x2 - molecule ?x3 - complex)
 :precondition (and (>= (available ?x1) (need-for-catalyzed-association ?x1 ?x2 ?x3))
		 (>= (available ?x2) (need-for-catalyzed-association ?x2 ?x1 ?x3))
		 (catalyzed-association-reaction ?x1 ?x2 ?x3))
 :effect (and (decrease (available ?x1) (need-for-catalyzed-association ?x1 ?x2 ?x3))
	      ;(decrease (available ?x2) (need-for-catalyzed-association ?x2 ?x1 ?x3))
	      ;(increase (available ?x2) (need-for-catalyzed-association ?x2 ?x1 ?x3))
	      (increase (available ?x3) (prod-by-catalyzed-association ?x1 ?x2 ?x3))))

(:action self-associate-with-catalyze
 :parameters (?x1 - molecule ?x3 - complex)
 :precondition (and (>= (available ?x1) (need-for-catalyzed-self-association ?x1 ?x3))
                 (catalyzed-self-association-reaction ?x1 ?x3))
 :effect (and (decrease (available ?x1) (need-for-catalyzed-self-association ?x1 ?x3))
              (increase (available ?x3) (prod-by-catalyzed-self-association ?x1 ?x3))))

(:action synthesize
 :parameters (?x1 ?x2 - molecule)
 :precondition (and (>= (available ?x1) (need-for-synthesis ?x1 ?x2))
		 (synthesis-reaction ?x1 ?x2))
 :effect (and 
	      ;(decrease (available ?x1) (need-for-synthesis ?x1 ?x2))
	      ;(increase (available ?x1) (need-for-synthesis ?x1 ?x2))
	      (increase (available ?x2) (prod-by-synthesis ?x1 ?x2))))
)

