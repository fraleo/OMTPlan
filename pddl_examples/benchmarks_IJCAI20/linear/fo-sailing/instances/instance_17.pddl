;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
;;Setting seed to 1229
(define (problem instance_5_1_1229)

	(:domain sailing_ln)

	(:objects
		b0 b1 b2 b3 b4  - boat
		p0  - person
	)

  (:init
		(= (x b0) 3)
(= (y b0) 0)
(= (v b0) 1)

(= (x b1) 7)
(= (y b1) 0)
(= (v b1) 1)

(= (x b2) -7)
(= (y b2) 0)
(= (v b2) 1)

(= (x b3) -2)
(= (y b3) 0)
(= (v b3) 1)

(= (x b4) 0)
(= (y b4) 0)
(= (v b4) 1)



		(= (d p0) 32)


	)

	(:goal
		(and
			(saved p0)

		)
	)
)


