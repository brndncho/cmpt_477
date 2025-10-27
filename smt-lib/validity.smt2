; Declare boolean variables
(declare-const p Bool)
(declare-const q Bool)

; Check the validity of p -> (q -> p)
; Check the unsatisfiability of *not* (p -> (q -> p))
(assert (not (=> p (=> q p))))
(check-sat)

