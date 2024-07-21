(declare-const m Int)
(declare-const n Int)
(assert (not (=> (and (> n 0) true) (and (= m (+ (* (div m n) n) (mod m n))) (and (and (<= 0 (mod m n)) (< (mod m n) n)) true)))))
(check-sat)