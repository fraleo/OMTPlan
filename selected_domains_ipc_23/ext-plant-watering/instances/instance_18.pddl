(define (problem instance_15_15_2_1)
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
	(= (maxx) 15)
	(= (minx) 1)
	(= (maxy) 15)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 93)
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
	(= (x plant1) 1)
	(= (y plant1) 5)
	(= (x plant2) 13)
	(= (y plant2) 1)
	(= (x plant3) 4)
	(= (y plant3) 11)
	(= (x plant4) 7)
	(= (y plant4) 8)
	(= (x plant5) 9)
	(= (y plant5) 3)
	(= (x plant6) 2)
	(= (y plant6) 6)
	(= (x plant7) 12)
	(= (y plant7) 15)
	(= (x plant8) 5)
	(= (y plant8) 3)
	(= (x plant9) 3)
	(= (y plant9) 4)
	(= (x plant10) 8)
	(= (y plant10) 14)
	(= (x plant11) 5)
	(= (y plant11) 11)
	(= (x plant12) 10)
	(= (y plant12) 4)
	(= (x plant13) 14)
	(= (y plant13) 15)
	(= (x plant14) 13)
	(= (y plant14) 12)
	(= (x plant15) 12)
	(= (y plant15) 9)
	(= (x tap1) 11)
	(= (y tap1) 1)
	(= (x agent1) 14)
	(= (y agent1) 5)
	(= (x agent2) 12)
	(= (y agent2) 6)
)
(:goal
(and
	(= (poured plant1) 3)
	(= (poured plant2) 5)
	(= (poured plant3) 2)
	(= (poured plant4) 8)
	(= (poured plant5) 7)
	(= (poured plant6) 7)
	(= (poured plant7) 8)
	(= (poured plant8) 8)
	(= (poured plant9) 8)
	(= (poured plant10) 2)
	(= (poured plant11) 2)
	(= (poured plant12) 8)
	(= (poured plant13) 3)
	(= (poured plant14) 8)
	(= (poured plant15) 6)
	(= (total_poured) (total_loaded))
)))
