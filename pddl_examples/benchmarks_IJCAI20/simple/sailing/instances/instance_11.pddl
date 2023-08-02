;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
;;Setting seed to 1229
(define (problem instance_3_1_1229)

	(:domain sailing)

	(:objects
		b0 b1 b2  - boat
		p0  - person
	)

  (:init
		(= (x b0) 3)
(= (y b0) 0)
(= (x b1) 7)
(= (y b1) 0)
(= (x b2) -7)
(= (y b2) 0)


		(= (d p0) 32)


	)

	(:goal
		(and
			(saved p0)

		)
	)
)


