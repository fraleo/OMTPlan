;; Ben Pathak (pathak.ban@gmail.com)
(define (problem instance_2_sled_9)

	(:domain expedition)

	(:objects
		s0 s1 - sled
		wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wa8 wa9 wa10 wa11 wa12 wa13 - waypoint
	)

  (:init
		(at s0 wa0)
		(= (sled_capacity s0) 4)
		(= (sled_supplies s0) 1)
		(= (waypoint_supplies wa0) 1000)
		(= (waypoint_supplies wa1) 0)
		(= (waypoint_supplies wa2) 0)
		(= (waypoint_supplies wa3) 0)
		(= (waypoint_supplies wa4) 0)
		(= (waypoint_supplies wa5) 0)
		(= (waypoint_supplies wa6) 0)
		(= (waypoint_supplies wa7) 0)
		(= (waypoint_supplies wa8) 0)
		(= (waypoint_supplies wa9) 0)
		(= (waypoint_supplies wa10) 0)
		(= (waypoint_supplies wa11) 0)
		(= (waypoint_supplies wa12) 0)
		(= (waypoint_supplies wa13) 0)
		(is_next wa0 wa1)
		(is_next wa1 wa2)
		(is_next wa2 wa3)
		(is_next wa3 wa4)
		(is_next wa4 wa5)
		(is_next wa5 wa6)
		(is_next wa6 wa7)
		(is_next wa7 wa8)
		(is_next wa8 wa9)
		(is_next wa9 wa10)
		(is_next wa10 wa11)
		(is_next wa11 wa12)
		(is_next wa12 wa13)
		(at s1 wa0)
		(= (sled_capacity s1) 4)
		(= (sled_supplies s1) 1)
	)

	(:goal
		(and
			(at s0 wa13)
			(at s1 wa13)
		)
	)
)


