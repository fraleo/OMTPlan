;;Setting seed to 1229
;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_6_600_1229_ladder)
(:domain farmland_ln)
	(:objects
		farm0 farm1 farm2 farm3 farm4 farm5  - farm
	)
  (:init

                (= (num-of-cars) 0)
		(= (x farm0) 600)
		(= (x farm1) 1)
		(= (x farm2) 0)
		(= (x farm3) 0)
		(= (x farm4) 0)
		(= (x farm5) 1)
		
		(adj farm0 farm1)
		(adj farm0 farm3)
		(adj farm1 farm0)
		(adj farm1 farm2)
		(adj farm1 farm4)
		(adj farm2 farm1)
		(adj farm2 farm5)
		(adj farm3 farm0)
		(adj farm3 farm4)
		(adj farm4 farm1)
		(adj farm4 farm3)
		(adj farm4 farm5)
		(adj farm5 farm2)
		(adj farm5 farm4)
		
		(= (cost) 0)
	)
	(:goal
		(and
			(>= (x farm0) 1)
			(>= (x farm1) 1)
			(>= (x farm2) 1)
			(>= (x farm3) 1)
			(>= (x farm4) 1)
			(>= (x farm5) 1)
			
			(>= (- (+ (* 1.0 (x farm0))(+ (* 1.7 (x farm1))(+ (* 1.3 (x farm2))(+ (* 1.1 (x farm3))(+ (* 1.4 (x farm4))(+ (* 1.9 (x farm5)) 0)))))) (cost)) 840.0)		)
	)
)


