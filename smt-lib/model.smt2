; Declare boolean variables
(declare-const p Bool)
(declare-const q Bool)

; Check the satisfiability of p <-> q
(assert (= p q))
(check-sat)

; Get a model
(get-model)

; One model: p and q are both false
; What if you want to find another model?
; Add a blocking clause

;(echo "1===========")
;(assert (not (and (not p) (not q))))
;(check-sat)
;(get-model)

; Get another model: p and q are both true
; What if you want to find a different model?
; And another blocking clause

;(echo "2===========")
;(assert (not (and p q)))
;(check-sat)
; UNSAT means no more model

