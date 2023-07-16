(define (problem instance_12_19_2_1)
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
	(= (maxx) 12)
	(= (minx) 1)
	(= (maxy) 12)
	(= (miny) 1)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (water_reserve) 113)
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
	(= (x plant1) 4)
	(= (y plant1) 9)
	(= (x plant2) 10)
	(= (y plant2) 10)
	(= (x plant3) 10)
	(= (y plant3) 3)
	(= (x plant4) 2)
	(= (y plant4) 6)
	(= (x plant5) 1)
	(= (y plant5) 8)
	(= (x plant6) 8)
	(= (y plant6) 9)
	(= (x plant7) 6)
	(= (y plant7) 5)
	(= (x plant8) 2)
	(= (y plant8) 10)
	(= (x plant9) 5)
	(= (y plant9) 9)
	(= (x plant10) 4)
	(= (y plant10) 3)
	(= (x plant11) 2)
	(= (y plant11) 1)
	(= (x plant12) 2)
	(= (y plant12) 5)
	(= (x plant13) 1)
	(= (y plant13) 5)
	(= (x plant14) 12)
	(= (y plant14) 4)
	(= (x plant15) 2)
	(= (y plant15) 4)
	(= (x plant16) 4)
	(= (y plant16) 6)
	(= (x plant17) 1)
	(= (y plant17) 10)
	(= (x plant18) 1)
	(= (y plant18) 12)
	(= (x plant19) 4)
	(= (y plant19) 5)
	(= (x tap1) 6)
	(= (y tap1) 12)
	(= (x agent1) 2)
	(= (y agent1) 12)
	(= (x agent2) 11)
	(= (y agent2) 11)
)
(:goal
(and
	(= (poured plant1) 6)
	(= (poured plant2) 7)
	(= (poured plant3) 3)
	(= (poured plant4) 10)
	(= (poured plant5) 4)
	(= (poured plant6) 5)
	(= (poured plant7) 4)
	(= (poured plant8) 9)
	(= (poured plant9) 8)
	(= (poured plant10) 5)
	(= (poured plant11) 1)
	(= (poured plant12) 9)
	(= (poured plant13) 3)
	(= (poured plant14) 7)
	(= (poured plant15) 9)
	(= (poured plant16) 4)
	(= (poured plant17) 4)
	(= (poured plant18) 2)
	(= (poured plant19) 3)
	(= (total_poured) (total_loaded))
)))
