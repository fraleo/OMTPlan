(define (problem instance_2_2)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1  - counter
  )

  (:init
    
    (= (max_int) 4)
        (= (value c0) 4)
        (= (value c1) 4)

        (= (rate_value c0) 0)
        (= (rate_value c1) 0)
    )

  (:goal (and

    (<= (+ (value c0) 1) (value c1))))
)