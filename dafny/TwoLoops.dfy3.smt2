(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (not (=> (and (and (and (and (<= x a) (= y 0)) (= z (+ (+ x y) c))) (>= b 0)) (not (< x a))) (and (and (<= y b) (= x a)) (= z (+ (+ a y) c))))))
(check-sat)