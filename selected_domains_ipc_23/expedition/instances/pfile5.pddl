;; Ben Pathak (pathak.ban@gmail.com)
(define (problem instance_2_sled_4)

	(:domain expedition)

	(:objects
		s0 s1 - sled
		wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wa8 wb0 wb1 wb2 wb3 wb4 wb5 wb6 wb7 wb8 - waypoint
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
		(is_next wa0 wa1)
		(is_next wa1 wa2)
		(is_next wa2 wa3)
		(is_next wa3 wa4)
		(is_next wa4 wa5)
		(is_next wa5 wa6)
		(is_next wa6 wa7)
		(is_next wa7 wa8)
		(at s1 wb0)
		(= (sled_capacity s1) 4)
		(= (sled_supplies s1) 1)
		(= (waypoint_supplies wb0) 1000)
		(= (waypoint_supplies wb1) 0)
		(= (waypoint_supplies wb2) 0)
		(= (waypoint_supplies wb3) 0)
		(= (waypoint_supplies wb4) 0)
		(= (waypoint_supplies wb5) 0)
		(= (waypoint_supplies wb6) 0)
		(= (waypoint_supplies wb7) 0)
		(= (waypoint_supplies wb8) 0)
		(is_next wb0 wb1)
		(is_next wb1 wb2)
		(is_next wb2 wb3)
		(is_next wb3 wb4)
		(is_next wb4 wb5)
		(is_next wb5 wb6)
		(is_next wb6 wb7)
		(is_next wb7 wb8)
	)

	(:goal
		(and
			(at s0 wa8)
			(at s1 wb8)
		)
	)
)


