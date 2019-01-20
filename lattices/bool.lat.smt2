;; Boolean lattice

;; distance
(define-fun lat!distance ((x Bool) (y Bool)) Real
	(ite (= x y) 0.0 1.0))

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

;; domain of symbolic conjunctions (arity 2)
(define-fun dom!sym!and!2 ((s String)) Bool 
	(or
		(= s "and_bool")))

;; domain of symbolic disjunctions (arity 2)
(define-fun dom!sym!or!2 ((s String)) Bool 
	(or
		(= s "or_bool")))

;; domain of symbolic aggregators (arity 1)
(define-fun dom!sym!agr!1 ((s String)) Bool 
	(or
		(= s "agr_not")))

;; domain of symbolic aggregators (arity 2)
(define-fun dom!sym!agr!2 ((s String)) Bool 
	(or 
		(= s "agr_xor")))

;; eval symbolic conjunctions (arity 2)
(define-fun call!sym!and!2 ((s String) (x Bool) (y Bool)) Bool 
	(lat!and!bool!2 x y))

;; eval symbolic disjunctions (arity 2)
(define-fun call!sym!or!2 ((s String) (x Bool) (y Bool)) Bool 
	(lat!or!bool!2 x y))

;; eval symbolic aggregatos (arity 1)
(define-fun call!sym!agr!1 ((s String) (x Bool)) Bool 
	(lat!agr!not!1 x))

;; eval symbolic aggregators (arity 2)
(define-fun call!sym!agr!2 ((s String) (x Bool) (y Bool)) Bool 
	(lat!agr!xor!2 x y))
