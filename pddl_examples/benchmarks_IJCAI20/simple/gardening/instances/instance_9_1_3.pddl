;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_9_1_3)
  (:domain mt-plant-watering-constrained)
  (:objects
    agent1 - agent
	tap1 - tap
	plant1 - plant
  )

  (:init
    (= (max_int) 20)
	(= (maxx) 9)
	(= (minx) 1)
	(= (maxy) 9)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (x agent1) 5)
	(= (y agent1) 9)
	(= (x plant1) 8)
	(= (y plant1) 8)
	(= (x tap1) 9)
	(= (y tap1) 9)
  )

  (:goal (and 
    (= (poured plant1) 1)
	(= (total_poured) (poured plant1) )
  ))

  
  

  
)
