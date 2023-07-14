(define (problem instance_14_19_2_1)
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
	(= (maxx) 14)
	(= (minx) 1)
	(= (maxy) 14)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 123)
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
	(= (x plant1) 8)
	(= (y plant1) 2)
	(= (x plant2) 10)
	(= (y plant2) 10)
	(= (x plant3) 1)
	(= (y plant3) 2)
	(= (x plant4) 13)
	(= (y plant4) 12)
	(= (x plant5) 9)
	(= (y plant5) 6)
	(= (x plant6) 8)
	(= (y plant6) 6)
	(= (x plant7) 1)
	(= (y plant7) 6)
	(= (x plant8) 5)
	(= (y plant8) 3)
	(= (x plant9) 3)
	(= (y plant9) 6)
	(= (x plant10) 10)
	(= (y plant10) 4)
	(= (x plant11) 9)
	(= (y plant11) 9)
	(= (x plant12) 11)
	(= (y plant12) 5)
	(= (x plant13) 9)
	(= (y plant13) 5)
	(= (x plant14) 2)
	(= (y plant14) 3)
	(= (x plant15) 10)
	(= (y plant15) 7)
	(= (x plant16) 10)
	(= (y plant16) 1)
	(= (x plant17) 5)
	(= (y plant17) 2)
	(= (x plant18) 6)
	(= (y plant18) 11)
	(= (x plant19) 14)
	(= (y plant19) 2)
	(= (x tap1) 14)
	(= (y tap1) 6)
	(= (x agent1) 2)
	(= (y agent1) 9)
	(= (x agent2) 2)
	(= (y agent2) 12)
)
(:goal
(and
	(= (poured plant1) 4)
	(= (poured plant2) 2)
	(= (poured plant3) 5)
	(= (poured plant4) 8)
	(= (poured plant5) 9)
	(= (poured plant6) 6)
	(= (poured plant7) 7)
	(= (poured plant8) 3)
	(= (poured plant9) 9)
	(= (poured plant10) 2)
	(= (poured plant11) 1)
	(= (poured plant12) 10)
	(= (poured plant13) 10)
	(= (poured plant14) 7)
	(= (poured plant15) 10)
	(= (poured plant16) 6)
	(= (poured plant17) 3)
	(= (poured plant18) 3)
	(= (poured plant19) 7)
	(= (total_poured) (total_loaded))
)))
