(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (not (=> (and (and (and (<= y b) (= x a)) (= z (+ (+ a y) c))) (not (< y b))) (and (= z (+ (+ a b) c)) true))))
(check-sat)