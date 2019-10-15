(define (problem security-clearance-2-4)

	(:domain security-clearance)

	(:init
 		(not (clear_d1_l1) )
 		(not (clear_d1_l2) )
 		(not (clear_d1_l3) )
 		(not (clear_d1_l4) )
 		(not (clear_d2_l1) )
 		(not (clear_d2_l2) )
 		(not (clear_d2_l3) )
 		(not (clear_d2_l4) )
		(= (cost_d1) 0)
 		(= (priority_d1) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d2) 0)
 		(= (priority_d2) 1)
 		(= (high) 2)
 		(= (low) 1)
	)

	(:goal (and
 		(clear_d1_l1 )
 		(clear_d1_l2 )
 		(clear_d1_l3 )
 		(clear_d1_l4 )
 		(clear_d2_l1 )
 		(clear_d2_l2 )
 		(clear_d2_l3 )
 		(clear_d2_l4 ))
	)

	(:metric minimize (+ (cost_d2)  (cost_d1)))

)