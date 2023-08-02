(define (problem instance_12_17_2_1)
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
	(= (maxx) 12)
	(= (minx) 1)
	(= (maxy) 12)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 96)
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
	(= (x plant1) 2)
	(= (y plant1) 9)
	(= (x plant2) 7)
	(= (y plant2) 7)
	(= (x plant3) 4)
	(= (y plant3) 3)
	(= (x plant4) 3)
	(= (y plant4) 1)
	(= (x plant5) 3)
	(= (y plant5) 11)
	(= (x plant6) 2)
	(= (y plant6) 11)
	(= (x plant7) 6)
	(= (y plant7) 6)
	(= (x plant8) 12)
	(= (y plant8) 5)
	(= (x plant9) 12)
	(= (y plant9) 3)
	(= (x plant10) 11)
	(= (y plant10) 9)
	(= (x plant11) 6)
	(= (y plant11) 1)
	(= (x plant12) 5)
	(= (y plant12) 9)
	(= (x plant13) 5)
	(= (y plant13) 12)
	(= (x plant14) 10)
	(= (y plant14) 12)
	(= (x plant15) 3)
	(= (y plant15) 4)
	(= (x plant16) 11)
	(= (y plant16) 12)
	(= (x plant17) 7)
	(= (y plant17) 6)
	(= (x tap1) 4)
	(= (y tap1) 6)
	(= (x agent1) 10)
	(= (y agent1) 8)
	(= (x agent2) 8)
	(= (y agent2) 7)
)
(:goal
(and
	(= (poured plant1) 2)
	(= (poured plant2) 6)
	(= (poured plant3) 8)
	(= (poured plant4) 6)
	(= (poured plant5) 2)
	(= (poured plant6) 9)
	(= (poured plant7) 2)
	(= (poured plant8) 1)
	(= (poured plant9) 3)
	(= (poured plant10) 6)
	(= (poured plant11) 9)
	(= (poured plant12) 7)
	(= (poured plant13) 8)
	(= (poured plant14) 5)
	(= (poured plant15) 3)
	(= (poured plant16) 10)
	(= (poured plant17) 1)
	(= (total_poured) (total_loaded))
)))
