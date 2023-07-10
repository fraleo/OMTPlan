; benchmark generated from python API
(set-info :status unknown)
(declare-fun cost_d1_0 () Real)
(declare-fun priority_d1_0 () Real)
(declare-fun high_0 () Real)
(declare-fun low_0 () Real)
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
(declare-fun |0| () Real)
(declare-fun increase_priority_d1_0 () Bool)
(declare-fun |1| () Real)
(declare-fun priority_d1_1 () Real)
(declare-fun cost_d1_1 () Real)
(declare-fun authorize_all_d1_0 () Bool)
(declare-fun |2| () Real)
(declare-fun authorize_d1_l1_0 () Bool)
(declare-fun authorize_d1_l2_0 () Bool)
(declare-fun increase_priority_d2_0 () Bool)
(declare-fun priority_d2_1 () Real)
(declare-fun cost_d2_1 () Real)
(declare-fun authorize_all_d2_0 () Bool)
(declare-fun authorize_d2_l1_0 () Bool)
(declare-fun authorize_d2_l2_0 () Bool)
(declare-fun high_1 () Real)
(declare-fun low_1 () Real)
(assert
 (= cost_d1_0 0.0))
(assert
 (= priority_d1_0 1.0))
(assert
 (= high_0 2.0))
(assert
 (= low_0 1.0))
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
 (=> increase_priority_d1_0 (< (- priority_d1_0 high_0) |0|)))
(assert
 (=> increase_priority_d1_0 (= priority_d1_1 (+ priority_d1_0 |1|))))
(assert
 (=> increase_priority_d1_0 (= cost_d1_1 (+ cost_d1_0 priority_d1_0))))
(assert
 (=> authorize_all_d1_0 (<= (- high_0 priority_d1_0) |0|)))
(assert
 (let (($x50 (not clear_d1_l1_0)))
 (=> authorize_all_d1_0 $x50)))
(assert
 (let (($x51 (not clear_d1_l2_0)))
 (=> authorize_all_d1_0 $x51)))
(assert
 (=> authorize_all_d1_0 clear_d1_l1_1))
(assert
 (=> authorize_all_d1_0 clear_d1_l2_1))
(assert
 (let (($x75 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_all_d1_0 $x75)))
(assert
 (let (($x50 (not clear_d1_l1_0)))
 (=> authorize_d1_l1_0 $x50)))
(assert
 (=> authorize_d1_l1_0 clear_d1_l1_1))
(assert
 (=> authorize_d1_l1_0 (= cost_d1_1 (+ cost_d1_0 |1|))))
(assert
 (let (($x51 (not clear_d1_l2_0)))
 (=> authorize_d1_l2_0 $x51)))
(assert
 (=> authorize_d1_l2_0 clear_d1_l2_1))
(assert
 (let (($x84 (not clear_d1_l1_1)))
 (=> authorize_d1_l2_0 $x84)))
(assert
 (let (($x75 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_d1_l2_0 $x75)))
(assert
 (=> increase_priority_d2_0 (< (- priority_d2_0 high_0) |0|)))
(assert
 (=> increase_priority_d2_0 (= priority_d2_1 (+ priority_d2_0 |1|))))
(assert
 (=> increase_priority_d2_0 (= cost_d2_1 (+ cost_d2_0 priority_d2_0))))
(assert
 (=> authorize_all_d2_0 (<= (- high_0 priority_d2_0) |0|)))
(assert
 (let (($x52 (not clear_d2_l1_0)))
 (=> authorize_all_d2_0 $x52)))
(assert
 (let (($x53 (not clear_d2_l2_0)))
 (=> authorize_all_d2_0 $x53)))
(assert
 (=> authorize_all_d2_0 clear_d2_l1_1))
(assert
 (=> authorize_all_d2_0 clear_d2_l2_1))
(assert
 (let (($x104 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_all_d2_0 $x104)))
(assert
 (let (($x52 (not clear_d2_l1_0)))
 (=> authorize_d2_l1_0 $x52)))
(assert
 (=> authorize_d2_l1_0 clear_d2_l1_1))
(assert
 (=> authorize_d2_l1_0 (= cost_d2_1 (+ cost_d2_0 |1|))))
(assert
 (let (($x53 (not clear_d2_l2_0)))
 (=> authorize_d2_l2_0 $x53)))
(assert
 (=> authorize_d2_l2_0 clear_d2_l2_1))
(assert
 (let (($x113 (not clear_d2_l1_1)))
 (=> authorize_d2_l2_0 $x113)))
(assert
 (let (($x104 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_d2_l2_0 $x104)))
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
 (let (($x142 (or increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0)))
 (or (= cost_d1_1 cost_d1_0) $x142)))
(assert
 (or (= priority_d1_1 priority_d1_0) (or increase_priority_d1_0)))
(assert
 (or (= high_1 high_0) or))
(assert
 (or (= low_1 low_0) or))
(assert
 (let (($x152 (or increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0)))
 (or (= cost_d2_1 cost_d2_0) $x152)))
(assert
 (or (= priority_d2_1 priority_d2_0) (or increase_priority_d2_0)))
(assert
 ((_ at-most 1) increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0 increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0))
(check-sat)
