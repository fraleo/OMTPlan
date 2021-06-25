;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_4_3_3)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	agent1 - agent
	plant2 plant1 plant3 - plant
  )

  (:init
    (= (max_int) 60)
	(= (maxx) 4)
	(= (minx) 1)
	(= (maxy) 4)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (x agent1) 1)
	(= (y agent1) 2)
	(= (x plant2) 3)
	(= (y plant2) 3)
	(= (x tap1) 4)
	(= (y tap1) 4)
	(= (x plant1) 3)
	(= (y plant1) 3)
	(= (x plant3) 2)
	(= (y plant3) 2)
  )

  (:goal (and 
    (= (poured plant1) 3)
	(= (poured plant2) 9)
	(= (poured plant3) 9)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
