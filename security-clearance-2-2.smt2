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
 (and (and clear_d1_l1_1 clear_d1_l2_1 clear_d2_l1_1 clear_d2_l2_1) (and and)))
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
 (let (($x78 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_all_d1_0 $x78)))
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
 (let (($x87 (not clear_d1_l1_1)))
 (=> authorize_d1_l2_0 $x87)))
(assert
 (let (($x78 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_d1_l2_0 $x78)))
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
 (let (($x107 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_all_d2_0 $x107)))
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
 (let (($x116 (not clear_d2_l1_1)))
 (=> authorize_d2_l2_0 $x116)))
(assert
 (let (($x107 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_d2_l2_0 $x107)))
(assert
 (let (($x50 (not clear_d1_l1_0)))
 (let (($x119 (and $x50 clear_d1_l1_1)))
 (=> $x119 (or authorize_all_d1_0 authorize_d1_l1_0)))))
(assert
 (let (($x87 (not clear_d1_l1_1)))
 (let (($x122 (and clear_d1_l1_0 $x87)))
 (=> $x122 (or authorize_d1_l2_0)))))
(assert
 (let (($x51 (not clear_d1_l2_0)))
 (let (($x125 (and $x51 clear_d1_l2_1)))
 (=> $x125 (or authorize_all_d1_0 authorize_d1_l2_0)))))
(assert
 (let (($x129 (and clear_d1_l2_0 (not clear_d1_l2_1))))
 (=> $x129 or)))
(assert
 (let (($x52 (not clear_d2_l1_0)))
 (let (($x132 (and $x52 clear_d2_l1_1)))
 (=> $x132 (or authorize_all_d2_0 authorize_d2_l1_0)))))
(assert
 (let (($x116 (not clear_d2_l1_1)))
 (let (($x135 (and clear_d2_l1_0 $x116)))
 (=> $x135 (or authorize_d2_l2_0)))))
(assert
 (let (($x53 (not clear_d2_l2_0)))
 (let (($x138 (and $x53 clear_d2_l2_1)))
 (=> $x138 (or authorize_all_d2_0 authorize_d2_l2_0)))))
(assert
 (let (($x142 (and clear_d2_l2_0 (not clear_d2_l2_1))))
 (=> $x142 or)))
(assert
 (let (($x145 (or increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0)))
 (let (($x144 (= cost_d1_1 cost_d1_0)))
 (or $x144 $x145))))
(assert
 (let (($x147 (= priority_d1_1 priority_d1_0)))
 (or $x147 (or increase_priority_d1_0))))
(assert
 (let (($x150 (= high_1 high_0)))
 (or $x150 or)))
(assert
 (let (($x152 (= low_1 low_0)))
 (or $x152 or)))
(assert
 (let (($x155 (or increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0)))
 (let (($x154 (= cost_d2_1 cost_d2_0)))
 (or $x154 $x155))))
(assert
 (let (($x157 (= priority_d2_1 priority_d2_0)))
 (or $x157 (or increase_priority_d2_0))))
(assert
 ((_ at-most 1) increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0 increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0))
(check-sat)
