(define (problem instance_14_17_2_1)
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
	(= (maxx) 14)
	(= (minx) 1)
	(= (maxy) 14)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 86)
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
	(= (x plant1) 5)
	(= (y plant1) 1)
	(= (x plant2) 8)
	(= (y plant2) 7)
	(= (x plant3) 9)
	(= (y plant3) 8)
	(= (x plant4) 4)
	(= (y plant4) 7)
	(= (x plant5) 11)
	(= (y plant5) 9)
	(= (x plant6) 7)
	(= (y plant6) 3)
	(= (x plant7) 2)
	(= (y plant7) 1)
	(= (x plant8) 3)
	(= (y plant8) 1)
	(= (x plant9) 3)
	(= (y plant9) 10)
	(= (x plant10) 9)
	(= (y plant10) 10)
	(= (x plant11) 1)
	(= (y plant11) 4)
	(= (x plant12) 2)
	(= (y plant12) 10)
	(= (x plant13) 14)
	(= (y plant13) 1)
	(= (x plant14) 8)
	(= (y plant14) 10)
	(= (x plant15) 2)
	(= (y plant15) 12)
	(= (x plant16) 10)
	(= (y plant16) 10)
	(= (x plant17) 14)
	(= (y plant17) 8)
	(= (x tap1) 6)
	(= (y tap1) 14)
	(= (x agent1) 9)
	(= (y agent1) 5)
	(= (x agent2) 10)
	(= (y agent2) 4)
)
(:goal
(and
	(= (poured plant1) 2)
	(= (poured plant2) 6)
	(= (poured plant3) 1)
	(= (poured plant4) 8)
	(= (poured plant5) 1)
	(= (poured plant6) 3)
	(= (poured plant7) 9)
	(= (poured plant8) 1)
	(= (poured plant9) 7)
	(= (poured plant10) 1)
	(= (poured plant11) 2)
	(= (poured plant12) 1)
	(= (poured plant13) 7)
	(= (poured plant14) 4)
	(= (poured plant15) 9)
	(= (poured plant16) 8)
	(= (poured plant17) 9)
	(= (total_poured) (total_loaded))
)))
