; benchmark generated from python API
(set-info :status unknown)
(declare-fun |located(plane1, city0)_0| () Bool)
(declare-fun |fuel(plane1)_0| () Real)
(declare-fun |onboard(plane1)_0| () Real)
(declare-fun |located(person1, city0)_0| () Bool)
(declare-fun |located(person2, city0)_0| () Bool)
(declare-fun |located(person3, city1)_0| () Bool)
(declare-fun total-fuel-used_0 () Real)
(declare-fun |located(person3, city0)_0| () Bool)
(declare-fun |located(plane1, city1)_0| () Bool)
(declare-fun |located(person1, city1)_0| () Bool)
(declare-fun |located(person2, city1)_0| () Bool)
(declare-fun |located(plane1, city2)_0| () Bool)
(declare-fun |located(person1, city2)_0| () Bool)
(declare-fun |located(person2, city2)_0| () Bool)
(declare-fun |located(person3, city2)_0| () Bool)
(declare-fun |in(person1, plane1)_0| () Bool)
(declare-fun |in(person2, plane1)_0| () Bool)
(declare-fun |in(person3, plane1)_0| () Bool)
(declare-fun |located(person3, city2)_1| () Bool)
(declare-fun |located(person2, city1)_1| () Bool)
(declare-fun |located(person1, city2)_1| () Bool)
(declare-fun board_person1_plane1_city0_0 () Bool)
(declare-fun |located(person1, city0)_1| () Bool)
(declare-fun |in(person1, plane1)_1| () Bool)
(declare-fun |onboard(plane1)_1| () Real)
(declare-fun board_person1_plane1_city1_0 () Bool)
(declare-fun |located(person1, city1)_1| () Bool)
(declare-fun board_person1_plane1_city2_0 () Bool)
(declare-fun board_person2_plane1_city0_0 () Bool)
(declare-fun |located(person2, city0)_1| () Bool)
(declare-fun |in(person2, plane1)_1| () Bool)
(declare-fun board_person2_plane1_city1_0 () Bool)
(declare-fun board_person2_plane1_city2_0 () Bool)
(declare-fun |located(person2, city2)_1| () Bool)
(declare-fun board_person3_plane1_city0_0 () Bool)
(declare-fun |located(person3, city0)_1| () Bool)
(declare-fun |in(person3, plane1)_1| () Bool)
(declare-fun board_person3_plane1_city1_0 () Bool)
(declare-fun |located(person3, city1)_1| () Bool)
(declare-fun board_person3_plane1_city2_0 () Bool)
(declare-fun debark_person1_plane1_city0_0 () Bool)
(declare-fun debark_person1_plane1_city1_0 () Bool)
(declare-fun debark_person1_plane1_city2_0 () Bool)
(declare-fun debark_person2_plane1_city0_0 () Bool)
(declare-fun debark_person2_plane1_city1_0 () Bool)
(declare-fun debark_person2_plane1_city2_0 () Bool)
(declare-fun debark_person3_plane1_city0_0 () Bool)
(declare-fun debark_person3_plane1_city1_0 () Bool)
(declare-fun debark_person3_plane1_city2_0 () Bool)
(declare-fun fly-slow_plane1_city0_city0_0 () Bool)
(declare-fun |located(plane1, city0)_1| () Bool)
(declare-fun total-fuel-used_1 () Real)
(declare-fun |fuel(plane1)_1| () Real)
(declare-fun fly-slow_plane1_city0_city1_0 () Bool)
(declare-fun |located(plane1, city1)_1| () Bool)
(declare-fun fly-slow_plane1_city0_city2_0 () Bool)
(declare-fun |located(plane1, city2)_1| () Bool)
(declare-fun fly-slow_plane1_city1_city0_0 () Bool)
(declare-fun fly-slow_plane1_city1_city1_0 () Bool)
(declare-fun fly-slow_plane1_city1_city2_0 () Bool)
(declare-fun fly-slow_plane1_city2_city0_0 () Bool)
(declare-fun fly-slow_plane1_city2_city1_0 () Bool)
(declare-fun fly-slow_plane1_city2_city2_0 () Bool)
(declare-fun fly-fast_plane1_city0_city0_0 () Bool)
(declare-fun fly-fast_plane1_city0_city1_0 () Bool)
(declare-fun fly-fast_plane1_city0_city2_0 () Bool)
(declare-fun fly-fast_plane1_city1_city0_0 () Bool)
(declare-fun fly-fast_plane1_city1_city1_0 () Bool)
(declare-fun fly-fast_plane1_city1_city2_0 () Bool)
(declare-fun fly-fast_plane1_city2_city0_0 () Bool)
(declare-fun fly-fast_plane1_city2_city1_0 () Bool)
(declare-fun fly-fast_plane1_city2_city2_0 () Bool)
(declare-fun refuel_plane1_0 () Bool)
(assert
 |located(plane1, city0)_0|)
(assert
 (= |fuel(plane1)_0| 4000.0))
(assert
 (= |onboard(plane1)_0| 0.0))
(assert
 |located(person1, city0)_0|)
(assert
 |located(person2, city0)_0|)
(assert
 |located(person3, city1)_0|)
(assert
 (= total-fuel-used_0 0.0))
(assert
 (not |located(person3, city0)_0|))
(assert
 (not |located(plane1, city1)_0|))
(assert
 (not |located(person1, city1)_0|))
(assert
 (not |located(person2, city1)_0|))
(assert
 (not |located(plane1, city2)_0|))
(assert
 (not |located(person1, city2)_0|))
(assert
 (not |located(person2, city2)_0|))
(assert
 (not |located(person3, city2)_0|))
(assert
 (not |in(person1, plane1)_0|))
(assert
 (not |in(person2, plane1)_0|))
(assert
 (not |in(person3, plane1)_0|))
(assert
 (and |located(person1, city2)_1| |located(person2, city1)_1| |located(person3, city2)_1|))
(assert
 (=> board_person1_plane1_city0_0 |located(person1, city0)_0|))
(assert
 (=> board_person1_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x134 (not |located(person1, city0)_1|)))
 (=> board_person1_plane1_city0_0 $x134)))
(assert
 (=> board_person1_plane1_city0_0 |in(person1, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person1_plane1_city0_0 $x139)))
(assert
 (=> board_person1_plane1_city1_0 |located(person1, city1)_0|))
(assert
 (=> board_person1_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x143 (not |located(person1, city1)_1|)))
 (=> board_person1_plane1_city1_0 $x143)))
(assert
 (=> board_person1_plane1_city1_0 |in(person1, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person1_plane1_city1_0 $x139)))
(assert
 (=> board_person1_plane1_city2_0 |located(person1, city2)_0|))
(assert
 (=> board_person1_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x149 (not |located(person1, city2)_1|)))
 (=> board_person1_plane1_city2_0 $x149)))
(assert
 (=> board_person1_plane1_city2_0 |in(person1, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person1_plane1_city2_0 $x139)))
(assert
 (=> board_person2_plane1_city0_0 |located(person2, city0)_0|))
(assert
 (=> board_person2_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x155 (not |located(person2, city0)_1|)))
 (=> board_person2_plane1_city0_0 $x155)))
(assert
 (=> board_person2_plane1_city0_0 |in(person2, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person2_plane1_city0_0 $x139)))
(assert
 (=> board_person2_plane1_city1_0 |located(person2, city1)_0|))
(assert
 (=> board_person2_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x161 (not |located(person2, city1)_1|)))
 (=> board_person2_plane1_city1_0 $x161)))
(assert
 (=> board_person2_plane1_city1_0 |in(person2, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person2_plane1_city1_0 $x139)))
(assert
 (=> board_person2_plane1_city2_0 |located(person2, city2)_0|))
(assert
 (=> board_person2_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x167 (not |located(person2, city2)_1|)))
 (=> board_person2_plane1_city2_0 $x167)))
(assert
 (=> board_person2_plane1_city2_0 |in(person2, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person2_plane1_city2_0 $x139)))
(assert
 (=> board_person3_plane1_city0_0 |located(person3, city0)_0|))
(assert
 (=> board_person3_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x173 (not |located(person3, city0)_1|)))
 (=> board_person3_plane1_city0_0 $x173)))
(assert
 (=> board_person3_plane1_city0_0 |in(person3, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person3_plane1_city0_0 $x139)))
(assert
 (=> board_person3_plane1_city1_0 |located(person3, city1)_0|))
(assert
 (=> board_person3_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x179 (not |located(person3, city1)_1|)))
 (=> board_person3_plane1_city1_0 $x179)))
(assert
 (=> board_person3_plane1_city1_0 |in(person3, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person3_plane1_city1_0 $x139)))
(assert
 (=> board_person3_plane1_city2_0 |located(person3, city2)_0|))
(assert
 (=> board_person3_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x185 (not |located(person3, city2)_1|)))
 (=> board_person3_plane1_city2_0 $x185)))
(assert
 (=> board_person3_plane1_city2_0 |in(person3, plane1)_1|))
(assert
 (let (($x139 (= |onboard(plane1)_1| (+ |onboard(plane1)_0| 1.0))))
 (=> board_person3_plane1_city2_0 $x139)))
(assert
 (=> debark_person1_plane1_city0_0 |in(person1, plane1)_0|))
(assert
 (=> debark_person1_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x191 (not |in(person1, plane1)_1|)))
 (=> debark_person1_plane1_city0_0 $x191)))
(assert
 (=> debark_person1_plane1_city0_0 |located(person1, city0)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person1_plane1_city0_0 $x195)))
(assert
 (=> debark_person1_plane1_city1_0 |in(person1, plane1)_0|))
(assert
 (=> debark_person1_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x191 (not |in(person1, plane1)_1|)))
 (=> debark_person1_plane1_city1_0 $x191)))
(assert
 (=> debark_person1_plane1_city1_0 |located(person1, city1)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person1_plane1_city1_0 $x195)))
(assert
 (=> debark_person1_plane1_city2_0 |in(person1, plane1)_0|))
(assert
 (=> debark_person1_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x191 (not |in(person1, plane1)_1|)))
 (=> debark_person1_plane1_city2_0 $x191)))
(assert
 (=> debark_person1_plane1_city2_0 |located(person1, city2)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person1_plane1_city2_0 $x195)))
(assert
 (=> debark_person2_plane1_city0_0 |in(person2, plane1)_0|))
(assert
 (=> debark_person2_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x209 (not |in(person2, plane1)_1|)))
 (=> debark_person2_plane1_city0_0 $x209)))
(assert
 (=> debark_person2_plane1_city0_0 |located(person2, city0)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person2_plane1_city0_0 $x195)))
(assert
 (=> debark_person2_plane1_city1_0 |in(person2, plane1)_0|))
(assert
 (=> debark_person2_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x209 (not |in(person2, plane1)_1|)))
 (=> debark_person2_plane1_city1_0 $x209)))
(assert
 (=> debark_person2_plane1_city1_0 |located(person2, city1)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person2_plane1_city1_0 $x195)))
(assert
 (=> debark_person2_plane1_city2_0 |in(person2, plane1)_0|))
(assert
 (=> debark_person2_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x209 (not |in(person2, plane1)_1|)))
 (=> debark_person2_plane1_city2_0 $x209)))
(assert
 (=> debark_person2_plane1_city2_0 |located(person2, city2)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person2_plane1_city2_0 $x195)))
(assert
 (=> debark_person3_plane1_city0_0 |in(person3, plane1)_0|))
(assert
 (=> debark_person3_plane1_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x225 (not |in(person3, plane1)_1|)))
 (=> debark_person3_plane1_city0_0 $x225)))
(assert
 (=> debark_person3_plane1_city0_0 |located(person3, city0)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person3_plane1_city0_0 $x195)))
(assert
 (=> debark_person3_plane1_city1_0 |in(person3, plane1)_0|))
(assert
 (=> debark_person3_plane1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x225 (not |in(person3, plane1)_1|)))
 (=> debark_person3_plane1_city1_0 $x225)))
(assert
 (=> debark_person3_plane1_city1_0 |located(person3, city1)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person3_plane1_city1_0 $x195)))
(assert
 (=> debark_person3_plane1_city2_0 |in(person3, plane1)_0|))
(assert
 (=> debark_person3_plane1_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x225 (not |in(person3, plane1)_1|)))
 (=> debark_person3_plane1_city2_0 $x225)))
(assert
 (=> debark_person3_plane1_city2_0 |located(person3, city2)_1|))
(assert
 (let (($x195 (= |onboard(plane1)_1| (- |onboard(plane1)_0| 1.0))))
 (=> debark_person3_plane1_city2_0 $x195)))
(assert
 (=> fly-slow_plane1_city0_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city0_city0_0 $x240)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-slow_plane1_city0_city0_0 $x242)))
(assert
 (=> fly-slow_plane1_city0_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x248 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 4.0)))))
 (=> fly-slow_plane1_city0_city0_0 $x248)))
(assert
 (let (($x251 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 4.0)))))
 (=> fly-slow_plane1_city0_city0_0 $x251)))
(assert
 (=> fly-slow_plane1_city0_city1_0 |located(plane1, city0)_0|))
(assert
 (let (($x255 (<= 2712.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city0_city1_0 $x255)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-slow_plane1_city0_city1_0 $x242)))
(assert
 (=> fly-slow_plane1_city0_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x262 (= total-fuel-used_1 (+ total-fuel-used_0 (* 678.0 4.0)))))
 (=> fly-slow_plane1_city0_city1_0 $x262)))
(assert
 (let (($x265 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 678.0 4.0)))))
 (=> fly-slow_plane1_city0_city1_0 $x265)))
(assert
 (=> fly-slow_plane1_city0_city2_0 |located(plane1, city0)_0|))
(assert
 (let (($x269 (<= 3100.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city0_city2_0 $x269)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-slow_plane1_city0_city2_0 $x242)))
(assert
 (=> fly-slow_plane1_city0_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x276 (= total-fuel-used_1 (+ total-fuel-used_0 (* 775.0 4.0)))))
 (=> fly-slow_plane1_city0_city2_0 $x276)))
(assert
 (let (($x279 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 775.0 4.0)))))
 (=> fly-slow_plane1_city0_city2_0 $x279)))
(assert
 (=> fly-slow_plane1_city1_city0_0 |located(plane1, city1)_0|))
(assert
 (let (($x255 (<= 2712.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city1_city0_0 $x255)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-slow_plane1_city1_city0_0 $x283)))
(assert
 (=> fly-slow_plane1_city1_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x262 (= total-fuel-used_1 (+ total-fuel-used_0 (* 678.0 4.0)))))
 (=> fly-slow_plane1_city1_city0_0 $x262)))
(assert
 (let (($x265 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 678.0 4.0)))))
 (=> fly-slow_plane1_city1_city0_0 $x265)))
(assert
 (=> fly-slow_plane1_city1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city1_city1_0 $x240)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-slow_plane1_city1_city1_0 $x283)))
(assert
 (=> fly-slow_plane1_city1_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x248 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 4.0)))))
 (=> fly-slow_plane1_city1_city1_0 $x248)))
(assert
 (let (($x251 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 4.0)))))
 (=> fly-slow_plane1_city1_city1_0 $x251)))
(assert
 (=> fly-slow_plane1_city1_city2_0 |located(plane1, city1)_0|))
(assert
 (let (($x296 (<= 3240.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city1_city2_0 $x296)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-slow_plane1_city1_city2_0 $x283)))
(assert
 (=> fly-slow_plane1_city1_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x303 (= total-fuel-used_1 (+ total-fuel-used_0 (* 810.0 4.0)))))
 (=> fly-slow_plane1_city1_city2_0 $x303)))
(assert
 (let (($x306 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 810.0 4.0)))))
 (=> fly-slow_plane1_city1_city2_0 $x306)))
(assert
 (=> fly-slow_plane1_city2_city0_0 |located(plane1, city2)_0|))
(assert
 (let (($x269 (<= 3100.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city2_city0_0 $x269)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-slow_plane1_city2_city0_0 $x310)))
(assert
 (=> fly-slow_plane1_city2_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x276 (= total-fuel-used_1 (+ total-fuel-used_0 (* 775.0 4.0)))))
 (=> fly-slow_plane1_city2_city0_0 $x276)))
(assert
 (let (($x279 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 775.0 4.0)))))
 (=> fly-slow_plane1_city2_city0_0 $x279)))
(assert
 (=> fly-slow_plane1_city2_city1_0 |located(plane1, city2)_0|))
(assert
 (let (($x296 (<= 3240.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city2_city1_0 $x296)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-slow_plane1_city2_city1_0 $x310)))
(assert
 (=> fly-slow_plane1_city2_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x303 (= total-fuel-used_1 (+ total-fuel-used_0 (* 810.0 4.0)))))
 (=> fly-slow_plane1_city2_city1_0 $x303)))
(assert
 (let (($x306 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 810.0 4.0)))))
 (=> fly-slow_plane1_city2_city1_0 $x306)))
(assert
 (=> fly-slow_plane1_city2_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-slow_plane1_city2_city2_0 $x240)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-slow_plane1_city2_city2_0 $x310)))
(assert
 (=> fly-slow_plane1_city2_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x248 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 4.0)))))
 (=> fly-slow_plane1_city2_city2_0 $x248)))
(assert
 (let (($x251 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 4.0)))))
 (=> fly-slow_plane1_city2_city2_0 $x251)))
(assert
 (=> fly-fast_plane1_city0_city0_0 |located(plane1, city0)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city0_city0_0 $x240)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city0_city0_0 $x330)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-fast_plane1_city0_city0_0 $x242)))
(assert
 (=> fly-fast_plane1_city0_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x337 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 15.0)))))
 (=> fly-fast_plane1_city0_city0_0 $x337)))
(assert
 (let (($x340 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 15.0)))))
 (=> fly-fast_plane1_city0_city0_0 $x340)))
(assert
 (=> fly-fast_plane1_city0_city1_0 |located(plane1, city0)_0|))
(assert
 (let (($x344 (<= 10170.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city0_city1_0 $x344)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city0_city1_0 $x330)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-fast_plane1_city0_city1_0 $x242)))
(assert
 (=> fly-fast_plane1_city0_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x351 (= total-fuel-used_1 (+ total-fuel-used_0 (* 678.0 15.0)))))
 (=> fly-fast_plane1_city0_city1_0 $x351)))
(assert
 (let (($x354 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 678.0 15.0)))))
 (=> fly-fast_plane1_city0_city1_0 $x354)))
(assert
 (=> fly-fast_plane1_city0_city2_0 |located(plane1, city0)_0|))
(assert
 (let (($x358 (<= 11625.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city0_city2_0 $x358)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city0_city2_0 $x330)))
(assert
 (let (($x242 (not |located(plane1, city0)_1|)))
 (=> fly-fast_plane1_city0_city2_0 $x242)))
(assert
 (=> fly-fast_plane1_city0_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x365 (= total-fuel-used_1 (+ total-fuel-used_0 (* 775.0 15.0)))))
 (=> fly-fast_plane1_city0_city2_0 $x365)))
(assert
 (let (($x368 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 775.0 15.0)))))
 (=> fly-fast_plane1_city0_city2_0 $x368)))
(assert
 (=> fly-fast_plane1_city1_city0_0 |located(plane1, city1)_0|))
(assert
 (let (($x344 (<= 10170.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city1_city0_0 $x344)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city1_city0_0 $x330)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-fast_plane1_city1_city0_0 $x283)))
(assert
 (=> fly-fast_plane1_city1_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x351 (= total-fuel-used_1 (+ total-fuel-used_0 (* 678.0 15.0)))))
 (=> fly-fast_plane1_city1_city0_0 $x351)))
(assert
 (let (($x354 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 678.0 15.0)))))
 (=> fly-fast_plane1_city1_city0_0 $x354)))
(assert
 (=> fly-fast_plane1_city1_city1_0 |located(plane1, city1)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city1_city1_0 $x240)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city1_city1_0 $x330)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-fast_plane1_city1_city1_0 $x283)))
(assert
 (=> fly-fast_plane1_city1_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x337 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 15.0)))))
 (=> fly-fast_plane1_city1_city1_0 $x337)))
(assert
 (let (($x340 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 15.0)))))
 (=> fly-fast_plane1_city1_city1_0 $x340)))
(assert
 (=> fly-fast_plane1_city1_city2_0 |located(plane1, city1)_0|))
(assert
 (let (($x386 (<= 12150.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city1_city2_0 $x386)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city1_city2_0 $x330)))
(assert
 (let (($x283 (not |located(plane1, city1)_1|)))
 (=> fly-fast_plane1_city1_city2_0 $x283)))
(assert
 (=> fly-fast_plane1_city1_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x393 (= total-fuel-used_1 (+ total-fuel-used_0 (* 810.0 15.0)))))
 (=> fly-fast_plane1_city1_city2_0 $x393)))
(assert
 (let (($x396 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 810.0 15.0)))))
 (=> fly-fast_plane1_city1_city2_0 $x396)))
(assert
 (=> fly-fast_plane1_city2_city0_0 |located(plane1, city2)_0|))
(assert
 (let (($x358 (<= 11625.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city2_city0_0 $x358)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city2_city0_0 $x330)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-fast_plane1_city2_city0_0 $x310)))
(assert
 (=> fly-fast_plane1_city2_city0_0 |located(plane1, city0)_1|))
(assert
 (let (($x365 (= total-fuel-used_1 (+ total-fuel-used_0 (* 775.0 15.0)))))
 (=> fly-fast_plane1_city2_city0_0 $x365)))
(assert
 (let (($x368 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 775.0 15.0)))))
 (=> fly-fast_plane1_city2_city0_0 $x368)))
(assert
 (=> fly-fast_plane1_city2_city1_0 |located(plane1, city2)_0|))
(assert
 (let (($x386 (<= 12150.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city2_city1_0 $x386)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city2_city1_0 $x330)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-fast_plane1_city2_city1_0 $x310)))
(assert
 (=> fly-fast_plane1_city2_city1_0 |located(plane1, city1)_1|))
(assert
 (let (($x393 (= total-fuel-used_1 (+ total-fuel-used_0 (* 810.0 15.0)))))
 (=> fly-fast_plane1_city2_city1_0 $x393)))
(assert
 (let (($x396 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 810.0 15.0)))))
 (=> fly-fast_plane1_city2_city1_0 $x396)))
(assert
 (=> fly-fast_plane1_city2_city2_0 |located(plane1, city2)_0|))
(assert
 (let (($x240 (<= 0.0 |fuel(plane1)_0|)))
 (=> fly-fast_plane1_city2_city2_0 $x240)))
(assert
 (let (($x330 (>= 8.0 |onboard(plane1)_0|)))
 (=> fly-fast_plane1_city2_city2_0 $x330)))
(assert
 (let (($x310 (not |located(plane1, city2)_1|)))
 (=> fly-fast_plane1_city2_city2_0 $x310)))
(assert
 (=> fly-fast_plane1_city2_city2_0 |located(plane1, city2)_1|))
(assert
 (let (($x337 (= total-fuel-used_1 (+ total-fuel-used_0 (* 0.0 15.0)))))
 (=> fly-fast_plane1_city2_city2_0 $x337)))
(assert
 (let (($x340 (= |fuel(plane1)_1| (- |fuel(plane1)_0| (* 0.0 15.0)))))
 (=> fly-fast_plane1_city2_city2_0 $x340)))
(assert
 (=> refuel_plane1_0 (> 6000.0 |fuel(plane1)_0|)))
(assert
 (=> refuel_plane1_0 (= |fuel(plane1)_1| (+ |fuel(plane1)_0| 6000.0))))
(assert
 (let (($x427 (or fly-slow_plane1_city0_city0_0 fly-slow_plane1_city1_city0_0 fly-slow_plane1_city2_city0_0 fly-fast_plane1_city0_city0_0 fly-fast_plane1_city1_city0_0 fly-fast_plane1_city2_city0_0)))
 (=> (and (not |located(plane1, city0)_0|) |located(plane1, city0)_1|) $x427)))
(assert
 (let (($x430 (or fly-slow_plane1_city0_city0_0 fly-slow_plane1_city0_city1_0 fly-slow_plane1_city0_city2_0 fly-fast_plane1_city0_city0_0 fly-fast_plane1_city0_city1_0 fly-fast_plane1_city0_city2_0)))
 (=> (and |located(plane1, city0)_0| (not |located(plane1, city0)_1|)) $x430)))
(assert
 (=> (and (not |located(person1, city0)_0|) |located(person1, city0)_1|) (or debark_person1_plane1_city0_0)))
(assert
 (=> (and |located(person1, city0)_0| (not |located(person1, city0)_1|)) (or board_person1_plane1_city0_0)))
(assert
 (=> (and (not |located(person2, city0)_0|) |located(person2, city0)_1|) (or debark_person2_plane1_city0_0)))
(assert
 (=> (and |located(person2, city0)_0| (not |located(person2, city0)_1|)) (or board_person2_plane1_city0_0)))
(assert
 (=> (and (not |located(person3, city1)_0|) |located(person3, city1)_1|) (or debark_person3_plane1_city1_0)))
(assert
 (=> (and |located(person3, city1)_0| (not |located(person3, city1)_1|)) (or board_person3_plane1_city1_0)))
(assert
 (=> (and (not |located(person3, city0)_0|) |located(person3, city0)_1|) (or debark_person3_plane1_city0_0)))
(assert
 (=> (and |located(person3, city0)_0| (not |located(person3, city0)_1|)) (or board_person3_plane1_city0_0)))
(assert
 (let (($x460 (or fly-slow_plane1_city0_city1_0 fly-slow_plane1_city1_city1_0 fly-slow_plane1_city2_city1_0 fly-fast_plane1_city0_city1_0 fly-fast_plane1_city1_city1_0 fly-fast_plane1_city2_city1_0)))
 (=> (and (not |located(plane1, city1)_0|) |located(plane1, city1)_1|) $x460)))
(assert
 (let (($x463 (or fly-slow_plane1_city1_city0_0 fly-slow_plane1_city1_city1_0 fly-slow_plane1_city1_city2_0 fly-fast_plane1_city1_city0_0 fly-fast_plane1_city1_city1_0 fly-fast_plane1_city1_city2_0)))
 (=> (and |located(plane1, city1)_0| (not |located(plane1, city1)_1|)) $x463)))
(assert
 (=> (and (not |located(person1, city1)_0|) |located(person1, city1)_1|) (or debark_person1_plane1_city1_0)))
(assert
 (=> (and |located(person1, city1)_0| (not |located(person1, city1)_1|)) (or board_person1_plane1_city1_0)))
(assert
 (=> (and (not |located(person2, city1)_0|) |located(person2, city1)_1|) (or debark_person2_plane1_city1_0)))
(assert
 (=> (and |located(person2, city1)_0| (not |located(person2, city1)_1|)) (or board_person2_plane1_city1_0)))
(assert
 (let (($x478 (or fly-slow_plane1_city0_city2_0 fly-slow_plane1_city1_city2_0 fly-slow_plane1_city2_city2_0 fly-fast_plane1_city0_city2_0 fly-fast_plane1_city1_city2_0 fly-fast_plane1_city2_city2_0)))
 (=> (and (not |located(plane1, city2)_0|) |located(plane1, city2)_1|) $x478)))
(assert
 (let (($x481 (or fly-slow_plane1_city2_city0_0 fly-slow_plane1_city2_city1_0 fly-slow_plane1_city2_city2_0 fly-fast_plane1_city2_city0_0 fly-fast_plane1_city2_city1_0 fly-fast_plane1_city2_city2_0)))
 (=> (and |located(plane1, city2)_0| (not |located(plane1, city2)_1|)) $x481)))
(assert
 (=> (and (not |located(person1, city2)_0|) |located(person1, city2)_1|) (or debark_person1_plane1_city2_0)))
(assert
 (=> (and |located(person1, city2)_0| (not |located(person1, city2)_1|)) (or board_person1_plane1_city2_0)))
(assert
 (=> (and (not |located(person2, city2)_0|) |located(person2, city2)_1|) (or debark_person2_plane1_city2_0)))
(assert
 (=> (and |located(person2, city2)_0| (not |located(person2, city2)_1|)) (or board_person2_plane1_city2_0)))
(assert
 (=> (and (not |located(person3, city2)_0|) |located(person3, city2)_1|) (or debark_person3_plane1_city2_0)))
(assert
 (=> (and |located(person3, city2)_0| (not |located(person3, city2)_1|)) (or board_person3_plane1_city2_0)))
(assert
 (let (($x502 (or board_person1_plane1_city0_0 board_person1_plane1_city1_0 board_person1_plane1_city2_0)))
 (=> (and (not |in(person1, plane1)_0|) |in(person1, plane1)_1|) $x502)))
(assert
 (let (($x505 (or debark_person1_plane1_city0_0 debark_person1_plane1_city1_0 debark_person1_plane1_city2_0)))
 (=> (and |in(person1, plane1)_0| (not |in(person1, plane1)_1|)) $x505)))
(assert
 (let (($x508 (or board_person2_plane1_city0_0 board_person2_plane1_city1_0 board_person2_plane1_city2_0)))
 (=> (and (not |in(person2, plane1)_0|) |in(person2, plane1)_1|) $x508)))
(assert
 (let (($x511 (or debark_person2_plane1_city0_0 debark_person2_plane1_city1_0 debark_person2_plane1_city2_0)))
 (=> (and |in(person2, plane1)_0| (not |in(person2, plane1)_1|)) $x511)))
(assert
 (let (($x514 (or board_person3_plane1_city0_0 board_person3_plane1_city1_0 board_person3_plane1_city2_0)))
 (=> (and (not |in(person3, plane1)_0|) |in(person3, plane1)_1|) $x514)))
(assert
 (let (($x517 (or debark_person3_plane1_city0_0 debark_person3_plane1_city1_0 debark_person3_plane1_city2_0)))
 (=> (and |in(person3, plane1)_0| (not |in(person3, plane1)_1|)) $x517)))
(assert
 (let (($x520 (or fly-slow_plane1_city0_city0_0 fly-slow_plane1_city0_city1_0 fly-slow_plane1_city0_city2_0 fly-slow_plane1_city1_city0_0 fly-slow_plane1_city1_city1_0 fly-slow_plane1_city1_city2_0 fly-slow_plane1_city2_city0_0 fly-slow_plane1_city2_city1_0 fly-slow_plane1_city2_city2_0 fly-fast_plane1_city0_city0_0 fly-fast_plane1_city0_city1_0 fly-fast_plane1_city0_city2_0 fly-fast_plane1_city1_city0_0 fly-fast_plane1_city1_city1_0 fly-fast_plane1_city1_city2_0 fly-fast_plane1_city2_city0_0 fly-fast_plane1_city2_city1_0 fly-fast_plane1_city2_city2_0 refuel_plane1_0)))
 (let (($x519 (= |fuel(plane1)_1| |fuel(plane1)_0|)))
 (or $x519 $x520))))
(assert
 (let (($x523 (or board_person1_plane1_city0_0 board_person1_plane1_city1_0 board_person1_plane1_city2_0 board_person2_plane1_city0_0 board_person2_plane1_city1_0 board_person2_plane1_city2_0 board_person3_plane1_city0_0 board_person3_plane1_city1_0 board_person3_plane1_city2_0 debark_person1_plane1_city0_0 debark_person1_plane1_city1_0 debark_person1_plane1_city2_0 debark_person2_plane1_city0_0 debark_person2_plane1_city1_0 debark_person2_plane1_city2_0 debark_person3_plane1_city0_0 debark_person3_plane1_city1_0 debark_person3_plane1_city2_0)))
 (or (= |onboard(plane1)_1| |onboard(plane1)_0|) $x523)))
(assert
 (let (($x526 (or fly-slow_plane1_city0_city0_0 fly-slow_plane1_city0_city1_0 fly-slow_plane1_city0_city2_0 fly-slow_plane1_city1_city0_0 fly-slow_plane1_city1_city1_0 fly-slow_plane1_city1_city2_0 fly-slow_plane1_city2_city0_0 fly-slow_plane1_city2_city1_0 fly-slow_plane1_city2_city2_0 fly-fast_plane1_city0_city0_0 fly-fast_plane1_city0_city1_0 fly-fast_plane1_city0_city2_0 fly-fast_plane1_city1_city0_0 fly-fast_plane1_city1_city1_0 fly-fast_plane1_city1_city2_0 fly-fast_plane1_city2_city0_0 fly-fast_plane1_city2_city1_0 fly-fast_plane1_city2_city2_0)))
 (let (($x525 (= total-fuel-used_1 total-fuel-used_0)))
 (or $x525 $x526))))
(assert
 ((_ at-most 1) board_person1_plane1_city0_0 board_person1_plane1_city1_0 board_person1_plane1_city2_0 board_person2_plane1_city0_0 board_person2_plane1_city1_0 board_person2_plane1_city2_0 board_person3_plane1_city0_0 board_person3_plane1_city1_0 board_person3_plane1_city2_0 debark_person1_plane1_city0_0 debark_person1_plane1_city1_0 debark_person1_plane1_city2_0 debark_person2_plane1_city0_0 debark_person2_plane1_city1_0 debark_person2_plane1_city2_0 debark_person3_plane1_city0_0 debark_person3_plane1_city1_0 debark_person3_plane1_city2_0 fly-slow_plane1_city0_city0_0 fly-slow_plane1_city0_city1_0 fly-slow_plane1_city0_city2_0 fly-slow_plane1_city1_city0_0 fly-slow_plane1_city1_city1_0 fly-slow_plane1_city1_city2_0 fly-slow_plane1_city2_city0_0 fly-slow_plane1_city2_city1_0 fly-slow_plane1_city2_city2_0 fly-fast_plane1_city0_city0_0 fly-fast_plane1_city0_city1_0 fly-fast_plane1_city0_city2_0 fly-fast_plane1_city1_city0_0 fly-fast_plane1_city1_city1_0 fly-fast_plane1_city1_city2_0 fly-fast_plane1_city2_city0_0 fly-fast_plane1_city2_city1_0 fly-fast_plane1_city2_city2_0 refuel_plane1_0))
(check-sat)
