;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_10_3_1)
  (:domain mt-plant-watering-constrained)
  (:objects
    tap1 - tap
	agent1 - agent
	plant2 plant1 plant3 - plant
  )

  (:init
    (= (max_int) 60)
	(= (maxx) 10)
	(= (minx) 1)
	(= (maxy) 10)
	(= (miny) 1)
	(= (carrying) 0)
	(= (total_poured) 0)
	(= (total_loaded) 0)
	(= (poured plant1) 0)
	(= (poured plant2) 0)
	(= (poured plant3) 0)
	(= (x agent1) 8)
	(= (y agent1) 9)
	(= (x plant2) 10)
	(= (y plant2) 10)
	(= (x tap1) 1)
	(= (y tap1) 1)
	(= (x plant1) 4)
	(= (y plant1) 4)
	(= (x plant3) 7)
	(= (y plant3) 7)
  )

  (:goal (and 
    (= (poured plant1) 10)
	(= (poured plant2) 10)
	(= (poured plant3) 6)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
