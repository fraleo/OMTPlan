;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_8_3_3)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	agent1 - agent
	plant2 plant1 plant3 - plant
  )

  (:init
    (= (max_int) 60)
	(= (maxx) 8)
	(= (minx) 1)
	(= (maxy) 8)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (x agent1) 6)
	(= (y agent1) 6)
	(= (x plant2) 6)
	(= (y plant2) 6)
	(= (x tap1) 3)
	(= (y tap1) 3)
	(= (x plant1) 2)
	(= (y plant1) 2)
	(= (x plant3) 1)
	(= (y plant3) 1)
  )

  (:goal (and 
    (= (poured plant1) 6)
	(= (poured plant2) 2)
	(= (poured plant3) 9)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
