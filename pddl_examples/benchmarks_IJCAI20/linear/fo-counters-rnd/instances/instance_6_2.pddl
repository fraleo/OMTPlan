(define (problem instance_6_2)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1 c2 c3 c4 c5  - counter
  )

  (:init
    
    (= (max_int) 12)
        (= (value c0) 11)
        (= (value c1) 6)
        (= (value c2) 7)
        (= (value c3) 1)
        (= (value c4) 8)
        (= (value c5) 3)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
        (= (rate_value c2) 0)
        (= (rate_value c3) 0)
        (= (rate_value c4) 0)
        (= (rate_value c5) 0)
    )

  (:goal (and

    (<= (+ (value c0) 1) (value c1))
    (<= (+ (value c1) 1) (value c2))
    (<= (+ (value c2) 1) (value c3))
    (<= (+ (value c3) 1) (value c4))
    (<= (+ (value c4) 1) (value c5))))
)