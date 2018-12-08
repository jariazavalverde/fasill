;; Boolean lattice

;; &bool
(define-fun lat!and!bool!2 ((x Bool) (y Bool)) Bool
	(and x y))

;; |bool
(define-fun lat!or!bool!2 ((x Bool) (y Bool)) Bool
	(or x y))

;; @xor
(define-fun lat!agr!xor!2 ((x Bool) (y Bool)) Bool
	(xor x y))

;; @not
(define-fun lat!agr!not!1 ((x Bool)) Bool
	(not x))

;; distance
(define-fun lat!distance ((x Bool) (y Bool)) Real
	(ite (= x y) 0.0 1.0))
