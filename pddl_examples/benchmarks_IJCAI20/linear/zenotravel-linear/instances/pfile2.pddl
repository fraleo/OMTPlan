(define (problem ZTRAVEL-1-3)
(:domain zenotravel)
(:objects
	plane1 - aircraft
	person1 - person
	person2 - person
	person3 - person
	city0 - city
	city1 - city
	city2 - city
	)
(:init
	(located plane1 city0)
	(= (capacity plane1) 6830)
	(= (fuel plane1) 1773)
	(= (slow-burn plane1) 3)
	(= (fast-burn plane1) 11)
	(= (onboard plane1) 0)
	(= (zoom-limit plane1) 9)
	(located person1 city2)
	(located person2 city1)
	(located person3 city2)
	(= (distance city0 city0) 0)
	(= (distance city0 city1) 627)
	(= (distance city0 city2) 998)
	(= (distance city1 city0) 627)
	(= (distance city1 city1) 0)
	(= (distance city1 city2) 631)
	(= (distance city2 city0) 998)
	(= (distance city2 city1) 631)
	(= (distance city2 city2) 0)
	(= (total-fuel-used) 0)
)
(:goal (and
	(located plane1 city2)
	(located person1 city1)
	(located person3 city2)
	))
)
