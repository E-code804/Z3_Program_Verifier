(declare-const x Int)
(declare-const z Int)
(assert (not (=> (and (<= (* z z) x) (not (<= (* (+ z 1) (+ z 1)) x))) (and (and (<= (* z z) x) (< x (* (+ z 1) (+ z 1)))) true))))
(check-sat)