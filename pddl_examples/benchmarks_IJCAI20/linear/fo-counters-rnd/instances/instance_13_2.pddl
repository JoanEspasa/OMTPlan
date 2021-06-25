(define (problem instance_13_2)
  (:domain fo-counters-rnd)
  (:objects

    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12  - counter
  )

  (:init
    
    (= (max_int) 26)
        (= (value c0) 2)
        (= (value c1) 24)
        (= (value c2) 18)
        (= (value c3) 11)
        (= (value c4) 17)
        (= (value c5) 17)
        (= (value c6) 14)
        (= (value c7) 24)
        (= (value c8) 0)
        (= (value c9) 14)
        (= (value c10) 14)
        (= (value c11) 20)
        (= (value c12) 7)

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
        (= (rate_value c11) 0)
        (= (rate_value c12) 0)
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
    (<= (+ (value c9) 1) (value c10))
    (<= (+ (value c10) 1) (value c11))
    (<= (+ (value c11) 1) (value c12))))
)