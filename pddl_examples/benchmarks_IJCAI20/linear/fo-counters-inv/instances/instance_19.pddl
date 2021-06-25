;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (problem instance_19)
  (:domain fn-counters)
  (:objects
    c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 - counter
  )

  (:init
    (= (max_int) 38)
        (= (value c0) 36)
        (= (value c1) 34)
        (= (value c2) 32)
        (= (value c3) 30)
        (= (value c4) 28)
        (= (value c5) 26)
        (= (value c6) 24)
        (= (value c7) 22)
        (= (value c8) 20)
        (= (value c9) 18)
        (= (value c10) 16)
        (= (value c11) 14)
        (= (value c12) 12)
        (= (value c13) 10)
        (= (value c14) 8)
        (= (value c15) 6)
        (= (value c16) 4)
        (= (value c17) 2)
        (= (value c18) 0)

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
        (= (rate_value c13) 0)
        (= (rate_value c14) 0)
        (= (rate_value c15) 0)
        (= (rate_value c16) 0)
        (= (rate_value c17) 0)
        (= (rate_value c18) 0)
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
    (<= (+ (value c11) 1) (value c12))
    (<= (+ (value c12) 1) (value c13))
    (<= (+ (value c13) 1) (value c14))
    (<= (+ (value c14) 1) (value c15))
    (<= (+ (value c15) 1) (value c16))
    (<= (+ (value c16) 1) (value c17))
    (<= (+ (value c17) 1) (value c18))
  ))
)