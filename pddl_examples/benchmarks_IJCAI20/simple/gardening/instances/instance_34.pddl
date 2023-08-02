;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_7_3_1)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	agent1 - agent
	plant2 plant1 plant3 - plant
  )

  (:init
    (= (max_int) 60)
	(= (maxx) 7)
	(= (minx) 1)
	(= (maxy) 7)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (x agent1) 5)
	(= (y agent1) 6)
	(= (x plant2) 7)
	(= (y plant2) 7)
	(= (x tap1) 2)
	(= (y tap1) 2)
	(= (x plant1) 2)
	(= (y plant1) 2)
	(= (x plant3) 5)
	(= (y plant3) 5)
  )

  (:goal (and 
    (= (poured plant1) 3)
	(= (poured plant2) 4)
	(= (poured plant3) 2)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
