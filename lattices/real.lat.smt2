;; Real lattice

;; distance
(define-fun lat!distance ((x Real) (y Real)) Real 
	(abs (- y x)))

;; |add
(define-fun lat!or!add!2 ((x Real) (y Real)) Real 
	(+ x y))

;; &prod
(define-fun lat!and!prod!2 ((x Real) (y Real)) Real 
	(* x y))

;; domain of symbolic conjunctions (arity 2)
(define-fun dom!sym!and!2 ((s String)) Bool 
	(or
		(= s "and_prod")))

;; domain of symbolic disjunctions (arity 2)
(define-fun dom!sym!or!2 ((s String)) Bool 
	(or
		(= s "or_add")))

;; eval symbolic conjunctions (arity 2)
(define-fun call!sym!and!2 ((s String) (x Real) (y Real)) Real 
	(lat!and!prod!2 x y))

;; eval symbolic disjunctions (arity 2)
(define-fun call!sym!or!2 ((s String) (x Real) (y Real)) Real 
	(lat!or!add!2 x y))
