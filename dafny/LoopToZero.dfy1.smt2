(declare-const m Int)
(declare-const p Int)
(assert (not (=> (and (> m 0) true) (and (>= m 0) (= (- p m) (- p m))))))
(check-sat)