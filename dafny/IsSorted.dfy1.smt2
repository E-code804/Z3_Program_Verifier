(declare-fun length ((Array Int Int)) Int)
(declare-const a (Array Int Int))

(assert (not 
    (=> true 
        (and 
            (=> (< (length a) 2) 
                (and (= true (forall ((j Int)) 
                    (=> (< (<= 1 j) (length a)) 
                        (<= (select a (- j 1)) (select a j))))) true)) 
            (=> (not (< (length a) 2)) 
                (and 
                    (<= 1 (length a)) 
                    (= true (forall ((j Int)) 
                        (=> (< (<= 1 j) 1) (<= (select a (- j 1)) (select a j)))))))))))
(check-sat)