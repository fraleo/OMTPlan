;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
;;Setting seed to 1229
(define (problem instance_5_3_1229)

	(:domain sailing-ln)

	(:objects
		b0 b1 b2 b3 b4  - boat
		p0 p1 p2  - person
	)

  (:init
		(= (x b0) -7)
(= (y b0) 0)
(= (v b0) 1)

(= (x b1) -2)
(= (y b1) 0)
(= (v b1) 1)

(= (x b2) 0)
(= (y b2) 0)
(= (v b2) 1)

(= (x b3) -5)
(= (y b3) 0)
(= (v b3) 1)

(= (x b4) -5)
(= (y b4) 0)
(= (v b4) 1)



		(= (d p0) 32)
(= (d p1) 110)
(= (d p2) 140)


	)

	(:goal
		(and
			(saved p0)
(saved p1)
(saved p2)

		)
	)
)


