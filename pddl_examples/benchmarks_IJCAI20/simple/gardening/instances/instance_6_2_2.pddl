;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_6_2_2)
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
	(= (x agent1) 4)
	(= (y agent1) 6)
	(= (x tap1) 3)
	(= (y tap1) 3)
	(= (x plant1) 3)
	(= (y plant1) 3)
	(= (x plant2) 6)
	(= (y plant2) 6)
  )

  (:goal (and 
    (= (poured plant1) 4)
	(= (poured plant2) 9)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
