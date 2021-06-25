;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_5_2_3)
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
	(= (x agent1) 1)
	(= (y agent1) 4)
	(= (x tap1) 4)
	(= (y tap1) 4)
	(= (x plant1) 4)
	(= (y plant1) 4)
	(= (x plant2) 2)
	(= (y plant2) 2)
  )

  (:goal (and 
    (= (poured plant1) 9)
	(= (poured plant2) 2)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
