(define (problem security-clearance-9-2)

	(:domain security-clearance)

	(:init
 		(not (clear_d1_l1) )
 		(not (clear_d1_l2) )
 		(not (clear_d2_l1) )
 		(not (clear_d2_l2) )
 		(not (clear_d3_l1) )
 		(not (clear_d3_l2) )
 		(not (clear_d4_l1) )
 		(not (clear_d4_l2) )
 		(not (clear_d5_l1) )
 		(not (clear_d5_l2) )
 		(not (clear_d6_l1) )
 		(not (clear_d6_l2) )
 		(not (clear_d7_l1) )
 		(not (clear_d7_l2) )
 		(not (clear_d8_l1) )
 		(not (clear_d8_l2) )
 		(not (clear_d9_l1) )
 		(not (clear_d9_l2) )
		(= (cost_d1) 0)
 		(= (priority_d1) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d2) 0)
 		(= (priority_d2) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d3) 0)
 		(= (priority_d3) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d4) 0)
 		(= (priority_d4) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d5) 0)
 		(= (priority_d5) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d6) 0)
 		(= (priority_d6) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d7) 0)
 		(= (priority_d7) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d8) 0)
 		(= (priority_d8) 1)
 		(= (high) 2)
 		(= (low) 1)
 		(= (cost_d9) 0)
 		(= (priority_d9) 1)
 		(= (high) 2)
 		(= (low) 1)
	)

	(:goal (and
 		(clear_d1_l1 )
 		(clear_d1_l2 )
 		(clear_d2_l1 )
 		(clear_d2_l2 )
 		(clear_d3_l1 )
 		(clear_d3_l2 )
 		(clear_d4_l1 )
 		(clear_d4_l2 )
 		(clear_d5_l1 )
 		(clear_d5_l2 )
 		(clear_d6_l1 )
 		(clear_d6_l2 )
 		(clear_d7_l1 )
 		(clear_d7_l2 )
 		(clear_d8_l1 )
 		(clear_d8_l2 )
 		(clear_d9_l1 )
 		(clear_d9_l2 ))
	)

	(:metric minimize (+ (cost_d2) (+ (cost_d3) (+ (cost_d4) (+ (cost_d5) (+ (cost_d6) (+ (cost_d7) (+ (cost_d8) (+ (cost_d9)  (cost_d1))))))))))

)