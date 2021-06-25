;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_6_2_1)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	plant1 plant2 - plant
	agent1 - agent
  )

  (:init
    (= (max_int) 40)
	(= (maxx) 6)
	(= (minx) 1)
	(= (maxy) 6)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (x agent1) 2)
	(= (y agent1) 5)
	(= (x tap1) 1)
	(= (y tap1) 1)
	(= (x plant1) 1)
	(= (y plant1) 1)
	(= (x plant2) 2)
	(= (y plant2) 2)
  )

  (:goal (and 
    (= (poured plant1) 2)
	(= (poured plant2) 2)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
