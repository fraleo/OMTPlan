;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_8_2_1)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	plant1 plant2 - plant
	agent1 - agent
  )

  (:init
    (= (max_int) 40)
	(= (maxx) 8)
	(= (minx) 1)
	(= (maxy) 8)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (x agent1) 1)
	(= (y agent1) 3)
	(= (x tap1) 6)
	(= (y tap1) 6)
	(= (x plant1) 3)
	(= (y plant1) 3)
	(= (x plant2) 4)
	(= (y plant2) 4)
  )

  (:goal (and 
    (= (poured plant1) 6)
	(= (poured plant2) 3)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
