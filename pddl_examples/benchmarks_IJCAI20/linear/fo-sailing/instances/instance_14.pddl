;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
;;Setting seed to 1229
(define (problem instance_4_2_1229)

(:domain sailing_ln)

	(:objects
		b0 b1 b2 b3  - boat
		p0 p1  - person
	)

  (:init
		(= (x b0) 7)
(= (y b0) 0)
(= (v b0) 1)

(= (x b1) -7)
(= (y b1) 0)
(= (v b1) 1)

(= (x b2) -2)
(= (y b2) 0)
(= (v b2) 1)

(= (x b3) 0)
(= (y b3) 0)
(= (v b3) 1)



		(= (d p0) -370)
(= (d p1) -58)


	)

	(:goal
		(and
			(saved p0)
(saved p1)

		)
	)
)


