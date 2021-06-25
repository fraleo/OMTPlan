(define (problem instance_11_2)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10  - counter
  )

  (:init
    
    (= (max_int) 22)
        (= (value c0) 18)
        (= (value c1) 22)
        (= (value c2) 22)
        (= (value c3) 18)
        (= (value c4) 16)
        (= (value c5) 19)
        (= (value c6) 5)
        (= (value c7) 19)
        (= (value c8) 11)
        (= (value c9) 15)
        (= (value c10) 18)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
        (= (rate_value c2) 0)
        (= (rate_value c3) 0)
        (= (rate_value c4) 0)
        (= (rate_value c5) 0)
        (= (rate_value c6) 0)
        (= (rate_value c7) 0)
        (= (rate_value c8) 0)
        (= (rate_value c9) 0)
        (= (rate_value c10) 0)
    )

  (:goal (and

    (<= (+ (value c0) 1) (value c1))
    (<= (+ (value c1) 1) (value c2))
    (<= (+ (value c2) 1) (value c3))
    (<= (+ (value c3) 1) (value c4))
    (<= (+ (value c4) 1) (value c5))
    (<= (+ (value c5) 1) (value c6))
    (<= (+ (value c6) 1) (value c7))
    (<= (+ (value c7) 1) (value c8))
    (<= (+ (value c8) 1) (value c9))
    (<= (+ (value c9) 1) (value c10))))
)