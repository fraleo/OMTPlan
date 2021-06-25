;; boat can accelerate/decelerate to move more/less in a single action
;; the maximal speed is implicitly limited by the area:
;;     a too large speed will make the area unreachable

(define (domain sailing_ln)
    (:types boat - object person - object)
    (:predicates 
        (saved ?t - person)
	(dummy)
    )
    (:functions
        (x ?b - boat)
        (y ?b - boat)
	(v ?b - boat)
        (d ?t - person)
    )

    (:action go_north_east
         :parameters (?b - boat)
	 :precondition (and(not(dummy)))
         :effect (and (increase (x ?b) (* (v ?b) 1.5))
		      (increase (y ?b) (* (v ?b) 1.5))
                 )
    )

    (:action go_north_west
         :parameters (?b - boat)
	 :precondition (and(not(dummy)))
         :effect (and (decrease (x ?b) (* (v ?b) 1.5)) 
		      (increase (y ?b) (* (v ?b) 1.5))
                 )
    )
    (:action go_est
         :parameters (?b - boat)
	 :precondition (and(not(dummy)))
         :effect (and (increase (x ?b) (* (v ?b) 3))
                 )
    )
    (:action go_west
         :parameters (?b - boat)
	 :precondition (and(not(dummy)))
         :effect (and(decrease (x ?b) (* (v ?b) 3)))
    )
    (:action go_south_west
         :parameters(?b - boat)
	 :precondition (and(not(dummy)))
         :effect (and (increase (x ?b) (* (v ?b) 2)) 
		      (decrease (y ?b) (* (v ?b) 2))
                 )
    )
    (:action go_south_east
         :parameters(?b - boat)
	:precondition (and(not(dummy)))
         :effect (and (decrease (x ?b) (* (v ?b) 2)) 
                      (decrease (y ?b) (* (v ?b) 2))
                 )
    )
    (:action go_south
         :parameters(?b - boat)
	:precondition (and(not(dummy)))
         :effect (and (decrease (y ?b) (* (v ?b) 2)))
    )

    (:action accelerate
	 :parameters(?b - boat)
         :precondition (and (<= (+ (v ?b) 1) 3))
         :effect (and (increase (v ?b) 1))
    )


    (:action decelerate
	 :parameters(?b - boat)
	 :precondition (and (>= (- (v ?b) 1) 1))
         :effect (and (decrease (v ?b) 1))
    )

    (:action save_person
        :parameters(?b - boat ?t - person)
        :precondition ( and  (>= (+ (x ?b) (y ?b)) (d ?t)) 
                             (>= (- (y ?b) (x ?b)) (d ?t)) 
                             (<= (+ (x ?b) (y ?b)) (+ (d ?t) 25)) 
                             (<= (- (y ?b) (x ?b)) (+ (d ?t) 25))
                             (<= (v ?b) 1)
                      )
        :effect (and(saved ?t))
    )

)

