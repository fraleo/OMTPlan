;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_2_1)
  (:domain fo-counters-rnd)
  (:objects
    c0 c1 - counter
  )

  (:init
    
    (= (max_int) 4)
        (= (value c0) 3)
        (= (value c1) 2)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
    )

  (:goal (and
    (<= (+ (value c0) 1) (value c1))
  ))
)
