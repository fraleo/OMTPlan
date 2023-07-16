(define (problem instance_11_17_2_1)
(:domain ext-plant-watering)
(:objects
	plant1 - plant
	plant2 - plant
	plant3 - plant
	plant4 - plant
	plant5 - plant
	plant6 - plant
	plant7 - plant
	plant8 - plant
	plant9 - plant
	plant10 - plant
	plant11 - plant
	plant12 - plant
	plant13 - plant
	plant14 - plant
	plant15 - plant
	plant16 - plant
	plant17 - plant
	tap1 - tap
	agent1 - agent
	agent2 - agent
)
(:init
	(= (maxx) 11)
	(= (minx) 1)
	(= (maxy) 11)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 111)
	(= (carrying agent1) 0)
	(= (max_carry agent1) 5)
	(= (carrying agent2) 0)
	(= (max_carry agent2) 5)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (poured plant4) 0)
	(= (poured plant5) 0)
	(= (poured plant6) 0)
	(= (poured plant7) 0)
	(= (poured plant8) 0)
	(= (poured plant9) 0)
	(= (poured plant10) 0)
	(= (poured plant11) 0)
	(= (poured plant12) 0)
	(= (poured plant13) 0)
	(= (poured plant14) 0)
	(= (poured plant15) 0)
	(= (poured plant16) 0)
	(= (poured plant17) 0)
	(= (x plant1) 8)
	(= (y plant1) 2)
	(= (x plant2) 11)
	(= (y plant2) 10)
	(= (x plant3) 11)
	(= (y plant3) 1)
	(= (x plant4) 8)
	(= (y plant4) 4)
	(= (x plant5) 3)
	(= (y plant5) 9)
	(= (x plant6) 2)
	(= (y plant6) 7)
	(= (x plant7) 1)
	(= (y plant7) 11)
	(= (x plant8) 1)
	(= (y plant8) 5)
	(= (x plant9) 5)
	(= (y plant9) 4)
	(= (x plant10) 5)
	(= (y plant10) 8)
	(= (x plant11) 6)
	(= (y plant11) 9)
	(= (x plant12) 6)
	(= (y plant12) 11)
	(= (x plant13) 5)
	(= (y plant13) 1)
	(= (x plant14) 6)
	(= (y plant14) 7)
	(= (x plant15) 2)
	(= (y plant15) 1)
	(= (x plant16) 5)
	(= (y plant16) 10)
	(= (x plant17) 9)
	(= (y plant17) 9)
	(= (x tap1) 7)
	(= (y tap1) 8)
	(= (x agent1) 1)
	(= (y agent1) 9)
	(= (x agent2) 1)
	(= (y agent2) 6)
)
(:goal
(and
	(= (poured plant1) 5)
	(= (poured plant2) 8)
	(= (poured plant3) 1)
	(= (poured plant4) 7)
	(= (poured plant5) 9)
	(= (poured plant6) 8)
	(= (poured plant7) 6)
	(= (poured plant8) 9)
	(= (poured plant9) 9)
	(= (poured plant10) 6)
	(= (poured plant11) 5)
	(= (poured plant12) 8)
	(= (poured plant13) 5)
	(= (poured plant14) 8)
	(= (poured plant15) 4)
	(= (poured plant16) 1)
	(= (poured plant17) 2)
	(= (total_poured) (total_loaded))
)))
