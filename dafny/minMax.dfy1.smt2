(declare-const x Int)
(declare-const y Int)
(assert (not (=> true (and (=> (< x y) (and (and (and (<= x x) (<= x y)) (or (= x x) (= x y))) (and (and (and (>= y x) (>= y y)) (or (= y x) (= y y))) true))) (=> (not (< x y)) (and (and (and (<= y x) (<= y y)) (or (= y x) (= y y))) (and (and (and (>= x x) (>= x y)) (or (= x x) (= x y))) true)))))))
(check-sat)