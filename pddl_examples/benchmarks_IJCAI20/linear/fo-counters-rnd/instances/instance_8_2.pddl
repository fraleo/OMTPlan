(define (problem instance_8_2)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1 c2 c3 c4 c5 c6 c7  - counter
  )

  (:init
    
    (= (max_int) 16)
        (= (value c0) 15)
        (= (value c1) 15)
        (= (value c2) 4)
        (= (value c3) 16)
        (= (value c4) 5)
        (= (value c5) 10)
        (= (value c6) 2)
        (= (value c7) 5)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
        (= (rate_value c2) 0)
        (= (rate_value c3) 0)
        (= (rate_value c4) 0)
        (= (rate_value c5) 0)
        (= (rate_value c6) 0)
        (= (rate_value c7) 0)
    )

  (:goal (and

    (<= (+ (value c0) 1) (value c1))
    (<= (+ (value c1) 1) (value c2))
    (<= (+ (value c2) 1) (value c3))
    (<= (+ (value c3) 1) (value c4))
    (<= (+ (value c4) 1) (value c5))
    (<= (+ (value c5) 1) (value c6))
    (<= (+ (value c6) 1) (value c7))))
)