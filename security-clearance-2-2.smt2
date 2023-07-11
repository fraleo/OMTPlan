; benchmark generated from python API
(set-info :status unknown)
(declare-fun cost_d1_0 () Real)
(declare-fun priority_d1_0 () Real)
(declare-fun cost_d2_0 () Real)
(declare-fun priority_d2_0 () Real)
(declare-fun clear_d1_l1_0 () Bool)
(declare-fun clear_d1_l2_0 () Bool)
(declare-fun clear_d2_l1_0 () Bool)
(declare-fun clear_d2_l2_0 () Bool)
(declare-fun clear_d2_l2_1 () Bool)
(declare-fun clear_d2_l1_1 () Bool)
(declare-fun clear_d1_l2_1 () Bool)
(declare-fun clear_d1_l1_1 () Bool)
(declare-fun increase_priority_d1_0 () Bool)
(declare-fun priority_d1_1 () Real)
(declare-fun cost_d1_1 () Real)
(declare-fun authorize_all_d1_0 () Bool)
(declare-fun authorize_d1_l1_0 () Bool)
(declare-fun authorize_d1_l2_0 () Bool)
(declare-fun increase_priority_d2_0 () Bool)
(declare-fun priority_d2_1 () Real)
(declare-fun cost_d2_1 () Real)
(declare-fun authorize_all_d2_0 () Bool)
(declare-fun authorize_d2_l1_0 () Bool)
(declare-fun authorize_d2_l2_0 () Bool)
(assert
 (= cost_d1_0 0.0))
(assert
 (= priority_d1_0 1.0))
(assert
 (= cost_d2_0 0.0))
(assert
 (= priority_d2_0 1.0))
(assert
 (not clear_d1_l1_0))
(assert
 (not clear_d1_l2_0))
(assert
 (not clear_d2_l1_0))
(assert
 (not clear_d2_l2_0))
(assert
 (and clear_d1_l1_1 clear_d1_l2_1 clear_d2_l1_1 clear_d2_l2_1))
(assert
 (=> increase_priority_d1_0 (> 2.0 priority_d1_0)))
(assert
 (=> increase_priority_d1_0 (= priority_d1_1 (+ priority_d1_0 1.0))))
(assert
 (=> increase_priority_d1_0 (= cost_d1_1 (+ cost_d1_0 priority_d1_0))))
(assert
 (let (($x57 (<= 2.0 priority_d1_0)))
 (=> authorize_all_d1_0 $x57)))
(assert
 (let (($x43 (not clear_d1_l1_0)))
 (=> authorize_all_d1_0 $x43)))
(assert
 (let (($x44 (not clear_d1_l2_0)))
 (=> authorize_all_d1_0 $x44)))
(assert
 (=> authorize_all_d1_0 clear_d1_l1_1))
(assert
 (=> authorize_all_d1_0 clear_d1_l2_1))
(assert
 (let (($x64 (= cost_d1_1 (+ cost_d1_0 2.0))))
 (=> authorize_all_d1_0 $x64)))
(assert
 (let (($x43 (not clear_d1_l1_0)))
 (=> authorize_d1_l1_0 $x43)))
(assert
 (=> authorize_d1_l1_0 clear_d1_l1_1))
(assert
 (=> authorize_d1_l1_0 (= cost_d1_1 (+ cost_d1_0 1.0))))
(assert
 (let (($x44 (not clear_d1_l2_0)))
 (=> authorize_d1_l2_0 $x44)))
(assert
 (=> authorize_d1_l2_0 clear_d1_l2_1))
(assert
 (let (($x73 (not clear_d1_l1_1)))
 (=> authorize_d1_l2_0 $x73)))
(assert
 (let (($x64 (= cost_d1_1 (+ cost_d1_0 2.0))))
 (=> authorize_d1_l2_0 $x64)))
(assert
 (=> increase_priority_d2_0 (> 2.0 priority_d2_0)))
(assert
 (=> increase_priority_d2_0 (= priority_d2_1 (+ priority_d2_0 1.0))))
(assert
 (=> increase_priority_d2_0 (= cost_d2_1 (+ cost_d2_0 priority_d2_0))))
(assert
 (let (($x84 (<= 2.0 priority_d2_0)))
 (=> authorize_all_d2_0 $x84)))
(assert
 (let (($x45 (not clear_d2_l1_0)))
 (=> authorize_all_d2_0 $x45)))
(assert
 (let (($x46 (not clear_d2_l2_0)))
 (=> authorize_all_d2_0 $x46)))
(assert
 (=> authorize_all_d2_0 clear_d2_l1_1))
(assert
 (=> authorize_all_d2_0 clear_d2_l2_1))
(assert
 (let (($x91 (= cost_d2_1 (+ cost_d2_0 2.0))))
 (=> authorize_all_d2_0 $x91)))
(assert
 (let (($x45 (not clear_d2_l1_0)))
 (=> authorize_d2_l1_0 $x45)))
(assert
 (=> authorize_d2_l1_0 clear_d2_l1_1))
(assert
 (=> authorize_d2_l1_0 (= cost_d2_1 (+ cost_d2_0 1.0))))
(assert
 (let (($x46 (not clear_d2_l2_0)))
 (=> authorize_d2_l2_0 $x46)))
(assert
 (=> authorize_d2_l2_0 clear_d2_l2_1))
(assert
 (let (($x100 (not clear_d2_l1_1)))
 (=> authorize_d2_l2_0 $x100)))
(assert
 (let (($x91 (= cost_d2_1 (+ cost_d2_0 2.0))))
 (=> authorize_d2_l2_0 $x91)))
(assert
 (=> (and (not clear_d1_l1_0) clear_d1_l1_1) (or authorize_all_d1_0 authorize_d1_l1_0)))
(assert
 (=> (and clear_d1_l1_0 (not clear_d1_l1_1)) (or authorize_d1_l2_0)))
(assert
 (=> (and (not clear_d1_l2_0) clear_d1_l2_1) (or authorize_all_d1_0 authorize_d1_l2_0)))
(assert
 (=> (and clear_d1_l2_0 (not clear_d1_l2_1)) or))
(assert
 (=> (and (not clear_d2_l1_0) clear_d2_l1_1) (or authorize_all_d2_0 authorize_d2_l1_0)))
(assert
 (=> (and clear_d2_l1_0 (not clear_d2_l1_1)) (or authorize_d2_l2_0)))
(assert
 (=> (and (not clear_d2_l2_0) clear_d2_l2_1) (or authorize_all_d2_0 authorize_d2_l2_0)))
(assert
 (=> (and clear_d2_l2_0 (not clear_d2_l2_1)) or))
(assert
 (let (($x129 (or increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0)))
 (or (= cost_d1_1 cost_d1_0) $x129)))
(assert
 (or (= priority_d1_1 priority_d1_0) (or increase_priority_d1_0)))
(assert
 (let (($x135 (or increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0)))
 (or (= cost_d2_1 cost_d2_0) $x135)))
(assert
 (or (= priority_d2_1 priority_d2_0) (or increase_priority_d2_0)))
(assert
 ((_ at-most 1) increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0 increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0))
(check-sat)
