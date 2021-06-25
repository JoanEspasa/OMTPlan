;; Enrico Scala (enricos83@gmail.com) and Miquel Ramirez (miquel.ramirez@gmail.com)
(define (domain farmland)
    (:requirements :fluents :typing :equality)
    (:types farm - object)
    (:predicates (adj ?f1 ?f2 - farm))
    (:functions
        (x ?b - farm)
    )

    ;; Move a person from a unit f1 to a unit f2
    (:action move-fast
        :parameters (?f1 ?f2 - farm)
       :precondition (and (not (= ?f1 ?f2)) (>= (x ?f1) 4) (adj ?f1 ?f2) )
      :effect (and(decrease (x ?f1) 4) (increase (x ?f2) 4))
    )
    
    (:action move-slow
         :parameters (?f1 ?f2 - farm)
         :precondition (and (not (= ?f1 ?f2)) (>= (x ?f1) 1) (adj ?f1 ?f2))
         :effect (and(decrease (x ?f1) 1) (increase (x ?f2) 1))
    )

)
