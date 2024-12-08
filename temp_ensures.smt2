(declare-fun length ((Array Int Int)) Int)
(declare-const a (Array Int Int))
(assert (not (and (= true (forall ((j Int)) (=> (< (<= 1 j) (length ((as const (Array Int Int)) 0))) (<= (select a (- j 1)) (select a j))))) true)))
(check-sat)