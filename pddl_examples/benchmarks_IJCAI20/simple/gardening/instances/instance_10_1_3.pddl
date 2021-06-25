;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_10_1_3)
  (:domain mt-plant-watering-constrained)
  (:objects
    agent1 - agent
	tap1 - tap
	plant1 - plant
  )

  (:init
    (= (max_int) 20)
	(= (maxx) 10)
	(= (minx) 1)
	(= (maxy) 10)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (x agent1) 2)
	(= (y agent1) 6)
	(= (x plant1) 1)
	(= (y plant1) 1)
	(= (x tap1) 3)
	(= (y tap1) 3)
  )

  (:goal (and 
    (= (poured plant1) 8)
	(= (total_poured) (poured plant1) )
  ))

  
  

  
)
