(declare-const x Int)
(declare-const z Int)
(assert (not (=> (and (<= (* z z) x) (<= (* (+ z 1) (+ z 1)) x)) (<= (* (+ z 1) (+ z 1)) x))))
(check-sat)