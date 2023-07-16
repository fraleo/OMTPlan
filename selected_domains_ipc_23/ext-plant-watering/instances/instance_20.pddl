(define (problem instance_15_19_2_1)
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
	plant18 - plant
	plant19 - plant
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
	(= (water_reserve) 100)
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
	(= (poured plant18) 0)
	(= (poured plant19) 0)
	(= (x plant1) 10)
	(= (y plant1) 7)
	(= (x plant2) 15)
	(= (y plant2) 7)
	(= (x plant3) 10)
	(= (y plant3) 10)
	(= (x plant4) 5)
	(= (y plant4) 11)
	(= (x plant5) 5)
	(= (y plant5) 13)
	(= (x plant6) 1)
	(= (y plant6) 2)
	(= (x plant7) 15)
	(= (y plant7) 6)
	(= (x plant8) 12)
	(= (y plant8) 2)
	(= (x plant9) 12)
	(= (y plant9) 11)
	(= (x plant10) 12)
	(= (y plant10) 3)
	(= (x plant11) 6)
	(= (y plant11) 11)
	(= (x plant12) 4)
	(= (y plant12) 10)
	(= (x plant13) 2)
	(= (y plant13) 6)
	(= (x plant14) 7)
	(= (y plant14) 2)
	(= (x plant15) 7)
	(= (y plant15) 3)
	(= (x plant16) 4)
	(= (y plant16) 3)
	(= (x plant17) 5)
	(= (y plant17) 6)
	(= (x plant18) 9)
	(= (y plant18) 9)
	(= (x plant19) 13)
	(= (y plant19) 3)
	(= (x tap1) 1)
	(= (y tap1) 1)
	(= (x agent1) 9)
	(= (y agent1) 10)
	(= (x agent2) 5)
	(= (y agent2) 8)
)
(:goal
(and
	(= (poured plant1) 2)
	(= (poured plant2) 2)
	(= (poured plant3) 4)
	(= (poured plant4) 10)
	(= (poured plant5) 6)
	(= (poured plant6) 5)
	(= (poured plant7) 8)
	(= (poured plant8) 1)
	(= (poured plant9) 7)
	(= (poured plant10) 8)
	(= (poured plant11) 6)
	(= (poured plant12) 8)
	(= (poured plant13) 1)
	(= (poured plant14) 4)
	(= (poured plant15) 8)
	(= (poured plant16) 3)
	(= (poured plant17) 4)
	(= (poured plant18) 3)
	(= (poured plant19) 1)
	(= (total_poured) (total_loaded))
)))
