(define (problem instance_15_17_2_1)
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
	(= (maxx) 15)
	(= (minx) 1)
	(= (maxy) 15)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 110)
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
	(= (x plant1) 15)
	(= (y plant1) 12)
	(= (x plant2) 3)
	(= (y plant2) 7)
	(= (x plant3) 5)
	(= (y plant3) 13)
	(= (x plant4) 4)
	(= (y plant4) 11)
	(= (x plant5) 9)
	(= (y plant5) 4)
	(= (x plant6) 5)
	(= (y plant6) 11)
	(= (x plant7) 9)
	(= (y plant7) 5)
	(= (x plant8) 2)
	(= (y plant8) 1)
	(= (x plant9) 11)
	(= (y plant9) 2)
	(= (x plant10) 5)
	(= (y plant10) 3)
	(= (x plant11) 7)
	(= (y plant11) 1)
	(= (x plant12) 6)
	(= (y plant12) 6)
	(= (x plant13) 10)
	(= (y plant13) 1)
	(= (x plant14) 9)
	(= (y plant14) 1)
	(= (x plant15) 6)
	(= (y plant15) 9)
	(= (x plant16) 15)
	(= (y plant16) 10)
	(= (x plant17) 9)
	(= (y plant17) 10)
	(= (x tap1) 13)
	(= (y tap1) 9)
	(= (x agent1) 4)
	(= (y agent1) 7)
	(= (x agent2) 12)
	(= (y agent2) 14)
)
(:goal
(and
	(= (poured plant1) 4)
	(= (poured plant2) 10)
	(= (poured plant3) 5)
	(= (poured plant4) 3)
	(= (poured plant5) 2)
	(= (poured plant6) 7)
	(= (poured plant7) 9)
	(= (poured plant8) 10)
	(= (poured plant9) 8)
	(= (poured plant10) 7)
	(= (poured plant11) 2)
	(= (poured plant12) 6)
	(= (poured plant13) 8)
	(= (poured plant14) 7)
	(= (poured plant15) 2)
	(= (poured plant16) 6)
	(= (poured plant17) 4)
	(= (total_poured) (total_loaded))
)))
