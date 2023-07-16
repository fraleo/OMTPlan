;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_10_2_3)
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
	(= (y agent1) 7)
	(= (x tap1) 9)
	(= (y tap1) 9)
	(= (x plant1) 2)
	(= (y plant1) 2)
	(= (x plant2) 7)
	(= (y plant2) 7)
  )

  (:goal (and 
    (= (poured plant1) 9)
	(= (poured plant2) 6)
	(= (total_poured) (+ (poured plant1) (poured plant2)) )
  ))

  
  

  
)
