;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_10_2_2)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	plant1 plant2 - plant
	agent1 - agent
  )

  (:init
    (= (max_int) 40)
	(= (maxx) 10)
	(= (minx) 1)
	(= (maxy) 10)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (x agent1) 5)
	(= (y agent1) 8)
	(= (x tap1) 6)
	(= (y tap1) 6)
	(= (x plant1) 9)
	(= (y plant1) 9)
	(= (x plant2) 2)
	(= (y plant2) 2)
  )

  (:goal (and 
    (= (poured plant1) 8)
	(= (poured plant2) 10)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
