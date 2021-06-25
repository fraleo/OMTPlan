(define (problem ZTRAVEL-2-5)
(:domain zenotravel)
(:objects
	plane1 - aircraft
	plane2 - aircraft
	person1 - person
	person2 - person
	person3 - person
	person4 - person
	person5 - person
	city0 - city
	city1 - city
	city2 - city
	)
(:init
	(located plane1 city2)
	(= (capacity plane1) 5304)
	(= (fuel plane1) 1048)
	(= (slow-burn plane1) 2)
	(= (fast-burn plane1) 7)
	(= (onboard plane1) 0)
	(= (zoom-limit plane1) 2)
	(located plane2 city2)
	(= (capacity plane2) 6148)
	(= (fuel plane2) 973)
	(= (slow-burn plane2) 2)
	(= (fast-burn plane2) 4)
	(= (onboard plane2) 0)
	(= (zoom-limit plane2) 7)
	(located person1 city0)
	(located person2 city1)
	(located person3 city0)
	(located person4 city0)
	(located person5 city2)
	(= (distance city0 city0) 0)
	(= (distance city0 city1) 834)
	(= (distance city0 city2) 743)
	(= (distance city1 city0) 834)
	(= (distance city1 city1) 0)
	(= (distance city1 city2) 502)
	(= (distance city2 city0) 743)
	(= (distance city2 city1) 502)
	(= (distance city2 city2) 0)
	(= (total-fuel-used) 0)
)
(:goal (and
	(located plane1 city0)
	(located person2 city2)
	(located person3 city0)
	(located person4 city1)
	(located person5 city2)
	))

;(:metric minimize (+ (* 4 (total-time))  (* 3 (total-fuel-used))))
)
