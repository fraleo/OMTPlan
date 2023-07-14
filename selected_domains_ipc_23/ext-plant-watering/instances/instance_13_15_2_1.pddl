(define (problem instance_13_15_2_1)
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
	tap1 - tap
	agent1 - agent
	agent2 - agent
)
(:init
	(= (maxx) 13)
	(= (minx) 1)
	(= (maxy) 13)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 94)
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
	(= (x plant1) 9)
	(= (y plant1) 10)
	(= (x plant2) 13)
	(= (y plant2) 13)
	(= (x plant3) 12)
	(= (y plant3) 11)
	(= (x plant4) 2)
	(= (y plant4) 3)
	(= (x plant5) 7)
	(= (y plant5) 8)
	(= (x plant6) 7)
	(= (y plant6) 12)
	(= (x plant7) 1)
	(= (y plant7) 9)
	(= (x plant8) 6)
	(= (y plant8) 1)
	(= (x plant9) 12)
	(= (y plant9) 10)
	(= (x plant10) 1)
	(= (y plant10) 12)
	(= (x plant11) 2)
	(= (y plant11) 7)
	(= (x plant12) 5)
	(= (y plant12) 12)
	(= (x plant13) 4)
	(= (y plant13) 11)
	(= (x plant14) 9)
	(= (y plant14) 8)
	(= (x plant15) 5)
	(= (y plant15) 7)
	(= (x tap1) 5)
	(= (y tap1) 13)
	(= (x agent1) 6)
	(= (y agent1) 12)
	(= (x agent2) 5)
	(= (y agent2) 8)
)
(:goal
(and
	(= (poured plant1) 6)
	(= (poured plant2) 4)
	(= (poured plant3) 6)
	(= (poured plant4) 10)
	(= (poured plant5) 1)
	(= (poured plant6) 10)
	(= (poured plant7) 3)
	(= (poured plant8) 8)
	(= (poured plant9) 3)
	(= (poured plant10) 7)
	(= (poured plant11) 3)
	(= (poured plant12) 7)
	(= (poured plant13) 9)
	(= (poured plant14) 7)
	(= (poured plant15) 2)
	(= (total_poured) (total_loaded))
)))
