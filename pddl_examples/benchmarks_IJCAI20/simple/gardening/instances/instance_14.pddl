;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_5_2_2)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	plant1 plant2 - plant
	agent1 - agent
  )

  (:init
    (= (max_int) 40)
	(= (maxx) 5)
	(= (minx) 1)
	(= (maxy) 5)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (x agent1) 5)
	(= (y agent1) 2)
	(= (x tap1) 3)
	(= (y tap1) 3)
	(= (x plant1) 2)
	(= (y plant1) 2)
	(= (x plant2) 4)
	(= (y plant2) 4)
  )

  (:goal (and 
    (= (poured plant1) 10)
	(= (poured plant2) 5)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
