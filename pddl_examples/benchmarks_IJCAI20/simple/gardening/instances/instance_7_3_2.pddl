;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_7_3_2)
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
	(= (x agent1) 2)
	(= (y agent1) 6)
	(= (x plant2) 5)
	(= (y plant2) 5)
	(= (x tap1) 7)
	(= (y tap1) 7)
	(= (x plant1) 3)
	(= (y plant1) 3)
	(= (x plant3) 2)
	(= (y plant3) 2)
  )

  (:goal (and 
    (= (poured plant1) 2)
	(= (poured plant2) 1)
	(= (poured plant3) 4)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
