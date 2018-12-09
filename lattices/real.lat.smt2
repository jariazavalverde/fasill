;; Real lattice

;; max
(define-fun max ((x Real) (y Real)) Real 
	(ite (>= x y) x y))

;; min
(define-fun min ((x Real) (y Real)) Real 
	(ite (<= x y) x y))

;; member
(define-fun lat!member ((x Real)) Bool 
	(and (<= 0.0 x) (<= x 1.0)))

;; distance
(define-fun lat!distance ((x Real) (y Real)) Real 
	(abs (- y x)))

;; |luka
(define-fun lat!or!luka!2 ((x Real) (y Real)) Real 
	(min (+ x y) 1))

;; |prod
(define-fun lat!or!prod!2 ((x Real) (y Real)) Real 
	(- (+ x y) (* x y)))

;; |godel
(define-fun lat!or!godel!2 ((x Real) (y Real)) Real 
	(max x y))

;; &luka
(define-fun lat!and!luka!2 ((x Real) (y Real)) Real 
	(max (- (+ x y) 1) 0))

;; &prod
(define-fun lat!and!prod!2 ((x Real) (y Real)) Real 
	(* x y))

;; &godel
(define-fun lat!and!godel!2 ((x Real) (y Real)) Real 
	(min x y))

;; @aver
(define-fun lat!agr!aver!2 ((x Real) (y Real)) Real 
	(/ (+ x y) 2))

;; @very
(define-fun lat!agr!very!1 ((x Real)) Real 
	(* x x))

;; domain of symbolic conjunctions (arity 2)
(define-fun dom!sym!and!2 ((s String)) Bool 
	(or
		(= s "godel") 
		(= s "luka") 
		(= s "prod")))

;; domain of symbolic disjunctions (arity 2)
(define-fun dom!sym!or!2 ((s String)) Bool 
	(or
		(= s "godel") 
		(= s "luka") 
		(= s "prod")))

;; domain of symbolic aggregators (arity 1)
(define-fun dom!sym!agr!1 ((s String)) Bool 
	(or
		(= s "very")))

;; domain of symbolic aggregators (arity 2)
(define-fun dom!sym!agr!2 ((s String)) Bool 
	(or 
		(= s "aver")))

;; eval symbolic conjunctions (arity 2)
(define-fun call!sym!and!2 ((s String) (x Real) (y Real)) Real 
	(ite 
		(= s "godel") 
		(lat!and!godel!2 x y) 
		(ite 
			(= s "luka") 
			(lat!and!luka!2 x y)
			(lat!and!prod!2 x y))))

;; eval symbolic disjunctions (arity 2)
(define-fun call!sym!or!2 ((s String) (x Real) (y Real)) Real 
	(ite 
		(= s "godel") 
		(lat!or!godel!2 x y) 
		(ite 
			(= s "luka") 
			(lat!or!luka!2 x y) 
			(lat!or!prod!2 x y))))

;; eval symbolic aggregatos (arity 1)
(define-fun call!sym!agr!1 ((s String) (x Real)) Real 
	(lat!agr!very!1 x))

;; eval symbolic aggregators (arity 2)
(define-fun call!sym!agr!2 ((s String) (x Real) (y Real)) Real 
	(lat!agr!aver!2 x y))
