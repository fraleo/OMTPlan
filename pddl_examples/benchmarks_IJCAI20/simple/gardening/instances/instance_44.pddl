;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_8_3_2)
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
	(= (x agent1) 4)
	(= (y agent1) 3)
	(= (x plant2) 2)
	(= (y plant2) 2)
	(= (x tap1) 8)
	(= (y tap1) 8)
	(= (x plant1) 6)
	(= (y plant1) 6)
	(= (x plant3) 7)
	(= (y plant3) 7)
  )

  (:goal (and 
    (= (poured plant1) 6)
	(= (poured plant2) 7)
	(= (poured plant3) 5)
	(= (- (total_poured) (poured plant3)) (+ (poured plant1) (poured plant2))  )
  ))

  
  

  
)
