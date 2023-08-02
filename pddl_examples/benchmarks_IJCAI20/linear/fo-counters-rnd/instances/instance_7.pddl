(define (problem instance_4_1)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1 c2 c3  - counter
  )

  (:init
    
    (= (max_int) 8)
        (= (value c0) 0)
        (= (value c1) 1)
        (= (value c2) 1)
        (= (value c3) 0)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
        (= (rate_value c2) 0)
        (= (rate_value c3) 0)
    )

  (:goal (and

    (<= (+ (value c0) 1) (value c1))
    (<= (+ (value c1) 1) (value c2))
    (<= (+ (value c2) 1) (value c3))))
)