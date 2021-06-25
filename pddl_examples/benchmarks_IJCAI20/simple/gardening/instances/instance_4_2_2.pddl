;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_4_2_2)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	plant1 plant2 - plant
	agent1 - agent
  )

  (:init
    (= (max_int) 40)
	(= (maxx) 4)
	(= (minx) 1)
	(= (maxy) 4)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (x agent1) 1)
	(= (y agent1) 4)
	(= (x tap1) 2)
	(= (y tap1) 2)
	(= (x plant1) 1)
	(= (y plant1) 1)
	(= (x plant2) 2)
	(= (y plant2) 2)
  )

  (:goal (and 
    (= (poured plant1) 5)
	(= (poured plant2) 10)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
