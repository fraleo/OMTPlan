(define (domain security-clearance)

	(:requirements :strips :typing :negative-preconditions :fluents)

	(:predicates 
		(clear_d1_l1)
 		(clear_d1_l2)
 		(clear_d1_l3)
 		(clear_d1_l4)
 		(clear_d2_l1)
 		(clear_d2_l2)
 		(clear_d2_l3)
 		(clear_d2_l4)
 		(clear_d3_l1)
 		(clear_d3_l2)
 		(clear_d3_l3)
 		(clear_d3_l4)
 		(clear_d4_l1)
 		(clear_d4_l2)
 		(clear_d4_l3)
 		(clear_d4_l4)
	)

	(:functions 
		(cost_d1)
 		(cost_d2)
 		(cost_d3)
 		(cost_d4)
 		(priority_d1)
 		(priority_d2)
 		(priority_d3)
 		(priority_d4)
 		(high)
 		(low)
	)

	(:action increase_priority_d1
		:parameters ( )
		:precondition (and (< (priority_d1) (high)) )
		:effect (and (increase (priority_d1) 1) (increase (cost_d1) (priority_d1) ))
	)

	(:action authorize_all_d1
		:parameters ( )
		:precondition (and (>= (priority_d1) (high)) (not (clear_d1_l1)) (not (clear_d1_l2)) (not (clear_d1_l3)) (not (clear_d1_l4)) )
		:effect (and (clear_d1_l1) (clear_d1_l2) (clear_d1_l3) (clear_d1_l4) (increase (cost_d1) 4))
	)

	(:action authorize_d1_l1
		:parameters ( )
		:precondition (and (not (clear_d1_l1)))
		:effect (and (clear_d1_l1) (increase (cost_d1) 1))
	)

	(:action authorize_d1_l2
		:parameters ( )
		:precondition (and (not (clear_d1_l2)))
		:effect (and (clear_d1_l2) (not (clear_d1_l1)) (increase (cost_d1) 2))
	)

	(:action authorize_d1_l3
		:parameters ( )
		:precondition (and (not (clear_d1_l3)))
		:effect (and (clear_d1_l3) (not (clear_d1_l1)) (not (clear_d1_l2)) (increase (cost_d1) 3))
	)

	(:action authorize_d1_l4
		:parameters ( )
		:precondition (and (not (clear_d1_l4)))
		:effect (and (clear_d1_l4) (not (clear_d1_l1)) (not (clear_d1_l2)) (not (clear_d1_l3)) (increase (cost_d1) 4))
	)

	(:action increase_priority_d2
		:parameters ( )
		:precondition (and (< (priority_d2) (high)) )
		:effect (and (increase (priority_d2) 1) (increase (cost_d2) (priority_d2) ))
	)

	(:action authorize_all_d2
		:parameters ( )
		:precondition (and (>= (priority_d2) (high)) (not (clear_d2_l1)) (not (clear_d2_l2)) (not (clear_d2_l3)) (not (clear_d2_l4)) )
		:effect (and (clear_d2_l1) (clear_d2_l2) (clear_d2_l3) (clear_d2_l4) (increase (cost_d2) 4))
	)

	(:action authorize_d2_l1
		:parameters ( )
		:precondition (and (not (clear_d2_l1)))
		:effect (and (clear_d2_l1) (increase (cost_d2) 1))
	)

	(:action authorize_d2_l2
		:parameters ( )
		:precondition (and (not (clear_d2_l2)))
		:effect (and (clear_d2_l2) (not (clear_d2_l1)) (increase (cost_d2) 2))
	)

	(:action authorize_d2_l3
		:parameters ( )
		:precondition (and (not (clear_d2_l3)))
		:effect (and (clear_d2_l3) (not (clear_d2_l1)) (not (clear_d2_l2)) (increase (cost_d2) 3))
	)

	(:action authorize_d2_l4
		:parameters ( )
		:precondition (and (not (clear_d2_l4)))
		:effect (and (clear_d2_l4) (not (clear_d2_l1)) (not (clear_d2_l2)) (not (clear_d2_l3)) (increase (cost_d2) 4))
	)

	(:action increase_priority_d3
		:parameters ( )
		:precondition (and (< (priority_d3) (high)) )
		:effect (and (increase (priority_d3) 1) (increase (cost_d3) (priority_d3) ))
	)

	(:action authorize_all_d3
		:parameters ( )
		:precondition (and (>= (priority_d3) (high)) (not (clear_d3_l1)) (not (clear_d3_l2)) (not (clear_d3_l3)) (not (clear_d3_l4)) )
		:effect (and (clear_d3_l1) (clear_d3_l2) (clear_d3_l3) (clear_d3_l4) (increase (cost_d3) 4))
	)

	(:action authorize_d3_l1
		:parameters ( )
		:precondition (and (not (clear_d3_l1)))
		:effect (and (clear_d3_l1) (increase (cost_d3) 1))
	)

	(:action authorize_d3_l2
		:parameters ( )
		:precondition (and (not (clear_d3_l2)))
		:effect (and (clear_d3_l2) (not (clear_d3_l1)) (increase (cost_d3) 2))
	)

	(:action authorize_d3_l3
		:parameters ( )
		:precondition (and (not (clear_d3_l3)))
		:effect (and (clear_d3_l3) (not (clear_d3_l1)) (not (clear_d3_l2)) (increase (cost_d3) 3))
	)

	(:action authorize_d3_l4
		:parameters ( )
		:precondition (and (not (clear_d3_l4)))
		:effect (and (clear_d3_l4) (not (clear_d3_l1)) (not (clear_d3_l2)) (not (clear_d3_l3)) (increase (cost_d3) 4))
	)

	(:action increase_priority_d4
		:parameters ( )
		:precondition (and (< (priority_d4) (high)) )
		:effect (and (increase (priority_d4) 1) (increase (cost_d4) (priority_d4) ))
	)

	(:action authorize_all_d4
		:parameters ( )
		:precondition (and (>= (priority_d4) (high)) (not (clear_d4_l1)) (not (clear_d4_l2)) (not (clear_d4_l3)) (not (clear_d4_l4)) )
		:effect (and (clear_d4_l1) (clear_d4_l2) (clear_d4_l3) (clear_d4_l4) (increase (cost_d4) 4))
	)

	(:action authorize_d4_l1
		:parameters ( )
		:precondition (and (not (clear_d4_l1)))
		:effect (and (clear_d4_l1) (increase (cost_d4) 1))
	)

	(:action authorize_d4_l2
		:parameters ( )
		:precondition (and (not (clear_d4_l2)))
		:effect (and (clear_d4_l2) (not (clear_d4_l1)) (increase (cost_d4) 2))
	)

	(:action authorize_d4_l3
		:parameters ( )
		:precondition (and (not (clear_d4_l3)))
		:effect (and (clear_d4_l3) (not (clear_d4_l1)) (not (clear_d4_l2)) (increase (cost_d4) 3))
	)

	(:action authorize_d4_l4
		:parameters ( )
		:precondition (and (not (clear_d4_l4)))
		:effect (and (clear_d4_l4) (not (clear_d4_l1)) (not (clear_d4_l2)) (not (clear_d4_l3)) (increase (cost_d4) 4))
	)

)