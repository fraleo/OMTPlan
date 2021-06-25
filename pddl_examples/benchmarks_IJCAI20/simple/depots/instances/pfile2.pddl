(define (problem depotprob7512) (:domain depot)
(:objects
	depot0 - depot
	distributor0 distributor1 - distributor
	truck0 truck1 - truck
	pallet0 pallet1 pallet2 - pallet
	crate0 crate1 crate2 crate3 - crate
	hoist0 hoist1 hoist2 - hoist)
(:init
	(located pallet0 depot0)
	(clear crate0)
	(located pallet1 distributor0)
	(clear crate3)
	(located pallet2 distributor1)
	(clear crate2)
	(located truck0 depot0)
	(= (current_load truck0) 0)
	(= (load_limit truck0) 411)
	(located truck1 depot0)
	(= (current_load truck1) 0)
	(= (load_limit truck1) 390)
	(located hoist0 depot0)
	(available hoist0)
	(located hoist1 distributor0)
	(available hoist1)
	(located hoist2 distributor1)
	(available hoist2)
	(located crate0 depot0)
	(on crate0 pallet0)
	(= (weight crate0) 32)
	(located crate1 distributor1)
	(on crate1 pallet2)
	(= (weight crate1) 4)
	(located crate2 distributor1)
	(on crate2 crate1)
	(= (weight crate2) 89)
	(located crate3 distributor0)
	(on crate3 pallet1)
	(= (weight crate3) 62)
	(= (fuel-cost) 0)
)

(:goal (and
		(on crate0 pallet2)
		(on crate1 crate3)
		(on crate2 pallet0)
		(on crate3 pallet1)
	)
)

)