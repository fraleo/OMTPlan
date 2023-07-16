(define (problem instance_10_17_2_1)
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
	(= (maxx) 10)
	(= (minx) 1)
	(= (maxy) 10)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 124)
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
	(= (x plant1) 1)
	(= (y plant1) 7)
	(= (x plant2) 9)
	(= (y plant2) 1)
	(= (x plant3) 4)
	(= (y plant3) 6)
	(= (x plant4) 7)
	(= (y plant4) 4)
	(= (x plant5) 6)
	(= (y plant5) 3)
	(= (x plant6) 5)
	(= (y plant6) 7)
	(= (x plant7) 8)
	(= (y plant7) 4)
	(= (x plant8) 6)
	(= (y plant8) 4)
	(= (x plant9) 6)
	(= (y plant9) 9)
	(= (x plant10) 9)
	(= (y plant10) 6)
	(= (x plant11) 1)
	(= (y plant11) 9)
	(= (x plant12) 7)
	(= (y plant12) 2)
	(= (x plant13) 5)
	(= (y plant13) 9)
	(= (x plant14) 2)
	(= (y plant14) 2)
	(= (x plant15) 10)
	(= (y plant15) 10)
	(= (x plant16) 8)
	(= (y plant16) 8)
	(= (x plant17) 6)
	(= (y plant17) 7)
	(= (x tap1) 8)
	(= (y tap1) 3)
	(= (x agent1) 8)
	(= (y agent1) 6)
	(= (x agent2) 4)
	(= (y agent2) 8)
)
(:goal
(and
	(= (poured plant1) 10)
	(= (poured plant2) 4)
	(= (poured plant3) 8)
	(= (poured plant4) 6)
	(= (poured plant5) 6)
	(= (poured plant6) 9)
	(= (poured plant7) 1)
	(= (poured plant8) 7)
	(= (poured plant9) 9)
	(= (poured plant10) 10)
	(= (poured plant11) 10)
	(= (poured plant12) 6)
	(= (poured plant13) 10)
	(= (poured plant14) 1)
	(= (poured plant15) 4)
	(= (poured plant16) 9)
	(= (poured plant17) 3)
	(= (total_poured) (total_loaded))
)))
