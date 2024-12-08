; Variable Declarations
(declare-const a (Array Int Int))
(declare-const isSorted Bool)
(declare-const i Int)
(declare-fun length ((Array Int Int)) Int)

; Method-Level VC
(assert (not
  (=> true
    (and
      (=> (< (length a) 2)
          (= isSorted (forall ((j Int))
            (=> (and (<= 1 j) (< j (length a)))
                (<= (select a (- j 1)) (select a j))))))
      (=> (not (< (length a) 2))
          (and
            (<= i (length a))
            (= isSorted (forall ((j Int))
              (=> (and (<= 1 j) (< j i))
                  (<= (select a (- j 1)) (select a j))))))))))
)

; Initialization VC
(assert (not
  (and
    (= i 1)
    (= isSorted true)
    (<= i (length a))
    (= isSorted (forall ((j Int))
      (=> (and (<= 1 j) (< j i))
          (<= (select a (- j 1)) (select a j))))))
))

; Maintenance VC
(assert (not
  (=> (and
        (<= i (length a))
        (= isSorted (forall ((j Int))
          (=> (and (<= 1 j) (< j i))
              (<= (select a (- j 1)) (select a j)))))
        (< i (length a)))
      (and
        (=> (> (select a (- i 1)) (select a i))
            (and
              (= i (length a))
              (= isSorted false)
              (<= i (length a))
              (= isSorted (forall ((j Int))
                (=> (and (<= 1 j) (< j i))
                    (<= (select a (- j 1)) (select a j)))))))
        (=> (not (> (select a (- i 1)) (select a i)))
            (and
              (<= (+ i 1) (length a))
              (= isSorted (forall ((j Int))
                (=> (and (<= 1 j) (< j (+ i 1)))
                    (<= (select a (- j 1)) (select a j)))))))))
))

; Termination VC
(assert (not
  (=> (and
        (<= i (length a))
        (= isSorted (forall ((j Int))
          (=> (and (<= 1 j) (< j i))
              (<= (select a (- j 1)) (select a j)))))
        (not (< i (length a))))
      (= isSorted (forall ((j Int))
        (=> (and (<= 1 j) (< j (length a)))
            (<= (select a (- j 1)) (select a j))))))
))

; Satisfiability Check
(check-sat)
