;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
;;Setting seed to 1229
(define (problem instance_3_5_1229)

	(:domain sailing)

	(:objects
		b0 b1 b2  - boat
		p0 p1 p2 p3 p4  - person
	)

  (:init
		(= (x b0) 0)
(= (y b0) 0)
(= (x b1) -5)
(= (y b1) 0)
(= (x b2) -5)
(= (y b2) 0)


		(= (d p0) 32)
(= (d p1) 110)
(= (d p2) 140)
(= (d p3) 26)
(= (d p4) 64)


	)

	(:goal
		(and
			(saved p0)
(saved p1)
(saved p2)
(saved p3)
(saved p4)

		)
	)
)


