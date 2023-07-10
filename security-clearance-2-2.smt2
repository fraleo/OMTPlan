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
(declare-fun |0| () Real)
(declare-fun |2| () Real)
(declare-fun increase_priority_d1_0 () Bool)
(declare-fun |1| () Real)
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
 (=> increase_priority_d1_0 (< (- priority_d1_0 |2|) |0|)))
(assert
 (=> increase_priority_d1_0 (= priority_d1_1 (+ priority_d1_0 |1|))))
(assert
 (=> increase_priority_d1_0 (= cost_d1_1 (+ cost_d1_0 priority_d1_0))))
(assert
 (=> authorize_all_d1_0 (<= (- |2| priority_d1_0) |0|)))
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
 (let (($x68 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_all_d1_0 $x68)))
(assert
 (let (($x43 (not clear_d1_l1_0)))
 (=> authorize_d1_l1_0 $x43)))
(assert
 (=> authorize_d1_l1_0 clear_d1_l1_1))
(assert
 (=> authorize_d1_l1_0 (= cost_d1_1 (+ cost_d1_0 |1|))))
(assert
 (let (($x44 (not clear_d1_l2_0)))
 (=> authorize_d1_l2_0 $x44)))
(assert
 (=> authorize_d1_l2_0 clear_d1_l2_1))
(assert
 (let (($x77 (not clear_d1_l1_1)))
 (=> authorize_d1_l2_0 $x77)))
(assert
 (let (($x68 (= cost_d1_1 (+ cost_d1_0 |2|))))
 (=> authorize_d1_l2_0 $x68)))
(assert
 (=> increase_priority_d2_0 (< (- priority_d2_0 |2|) |0|)))
(assert
 (=> increase_priority_d2_0 (= priority_d2_1 (+ priority_d2_0 |1|))))
(assert
 (=> increase_priority_d2_0 (= cost_d2_1 (+ cost_d2_0 priority_d2_0))))
(assert
 (=> authorize_all_d2_0 (<= (- |2| priority_d2_0) |0|)))
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
 (let (($x97 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_all_d2_0 $x97)))
(assert
 (let (($x45 (not clear_d2_l1_0)))
 (=> authorize_d2_l1_0 $x45)))
(assert
 (=> authorize_d2_l1_0 clear_d2_l1_1))
(assert
 (=> authorize_d2_l1_0 (= cost_d2_1 (+ cost_d2_0 |1|))))
(assert
 (let (($x46 (not clear_d2_l2_0)))
 (=> authorize_d2_l2_0 $x46)))
(assert
 (=> authorize_d2_l2_0 clear_d2_l2_1))
(assert
 (let (($x106 (not clear_d2_l1_1)))
 (=> authorize_d2_l2_0 $x106)))
(assert
 (let (($x97 (= cost_d2_1 (+ cost_d2_0 |2|))))
 (=> authorize_d2_l2_0 $x97)))
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
 (let (($x135 (or increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0)))
 (or (= cost_d1_1 cost_d1_0) $x135)))
(assert
 (or (= priority_d1_1 priority_d1_0) (or increase_priority_d1_0)))
(assert
 (let (($x141 (or increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0)))
 (or (= cost_d2_1 cost_d2_0) $x141)))
(assert
 (or (= priority_d2_1 priority_d2_0) (or increase_priority_d2_0)))
(assert
 ((_ at-most 1) increase_priority_d1_0 authorize_all_d1_0 authorize_d1_l1_0 authorize_d1_l2_0 increase_priority_d2_0 authorize_all_d2_0 authorize_d2_l1_0 authorize_d2_l2_0))
(check-sat)
