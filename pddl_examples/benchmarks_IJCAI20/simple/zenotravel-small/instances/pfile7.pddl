(define (problem ZTRAVEL-2-6)
(:domain zenotravel)
(:objects
	plane1 - aircraft
	plane2 - aircraft
	person1 - person
	person2 - person
	person3 - person
	person4 - person
	person5 - person
	person6 - person
	city0 - city
	city1 - city
	city2 - city
	city3 - city
	)
(:init
	(located plane1 city2)
	(= (capacity plane1) 8351)
	(= (fuel plane1) 2612)
	(= (slow-burn plane1) 3)
	(= (fast-burn plane1) 10)
	(= (onboard plane1) 0)
	(= (zoom-limit plane1) 10)
	(located plane2 city1)
	(= (capacity plane2) 6506)
	(= (fuel plane2) 2850)
	(= (slow-burn plane2) 3)
	(= (fast-burn plane2) 6)
	(= (onboard plane2) 0)
	(= (zoom-limit plane2) 9)
	(located person1 city3)
	(located person2 city3)
	(located person3 city3)
	(located person4 city1)
	(located person5 city3)
	(located person6 city0)
	(= (distance city0 city0) 0)
	(= (distance city0 city1) 559)
	(= (distance city0 city2) 602)
	(= (distance city0 city3) 709)
	(= (distance city1 city0) 559)
	(= (distance city1 city1) 0)
	(= (distance city1 city2) 899)
	(= (distance city1 city3) 529)
	(= (distance city2 city0) 602)
	(= (distance city2 city1) 899)
	(= (distance city2 city2) 0)
	(= (distance city2 city3) 722)
	(= (distance city3 city0) 709)
	(= (distance city3 city1) 529)
	(= (distance city3 city2) 722)
	(= (distance city3 city3) 0)
	(= (total-fuel-used) 0)
)
(:goal (and
	(located plane2 city1)
	(located person1 city2)
	(located person3 city3)
	(located person4 city3)
	(located person5 city2)
	(located person6 city2)
	))

;(:metric minimize (+ (* 5 (total-time))  (* 1 (total-fuel-used))))
)
