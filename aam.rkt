#lang racket
(require redex)
(require (only-in srfi/1 car+cdr))
(require (only-in srfi/8 receive))

; (acons 'cs252 "difficult" '((history1300 . "no more midterms")))
; => ((cs252 . "difficult") (history1300 . "no more midterms"))
(define (acons k v alist) (cons (cons k v) alist))

(define-language LC
  (e (e e)
     (λ x e)
     x)
  (x variable-not-otherwise-mentioned)
  (v (λ x e))
  )

(define-extended-language CEK LC
  (kappa mt
         (ar e rho kappa)
         (fn v rho kappa))
  (rho ((x v rho) ...))
  )

(define (inj-CEK expr)
  (term (,expr () mt)))

(define red-CEK
  (reduction-relation
   CEK
   (--> (x rho kappa)
        ,(receive (v rho) (apply values (dict-ref (term rho) (term x)))
           (term (,v ,rho kappa)))
        "#1")
   (--> ((e_0 e_1) rho kappa)
        (e_0 rho (ar e_1 rho kappa))
        "#2")
   (--> (v rho_0 (ar e rho_1 kappa))
        (e rho_1 (fn v rho_0 kappa))
        "#3")
   (--> (v rho_0 (fn (λ x e) rho_1 kappa))
        (e ,(cons (cons (term x) (term (v rho_0))) (term rho_1)) kappa)
        "#4")
   ))

(define-extended-language CESK* LC
  (a number)
  (kappa mt (ar e rho a) (fn v rho a))
  (rho any) ; alist of (x . a)
  (sigma any) ; alist of (a . (v . rho)) or (a . kappa)
  )

(define (inj-CESK* expr)
  (term (,expr () ((0 . mt)) 0)))

(define red-CESK*
  (reduction-relation
   CESK*
   (--> (x rho sigma a)
        ,(receive (v rho) (car+cdr (dict-ref (term sigma) (dict-ref (term rho) (term x))))
           (term (,v ,rho sigma a)))
        "#1")
   (--> ((e_0 e_1) rho sigma a)
        ,(let ((b (+ 1 (apply max (map car (term sigma))))))
           (term (e_0 rho ,(dict-set (term sigma) b (term (ar e_1 rho a))) ,b)))
        "#2")
   (--> (v rho_0 sigma a_0)
        ,(let ([b (+ 1 (apply max (map car (term sigma))))])
           (term (e rho_1 ,(dict-set (term sigma) b (term (fn v rho_0 a_1))) ,b)))
        (where (ar e rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#3")
   (--> (v rho_0 sigma a_0)
        ,(let ([b (+ 1 (apply max (map car (term sigma))))])
           (term (e
                  ,(dict-set (term rho_1) (term x) b)
                  ,(dict-set (term sigma) b (cons (term v) (term rho_0)))
                  a_1)))
        (where (fn (λ x e) rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#4")
   ))

; e.g.: (traces red-CESK* (inj-CESK* '((λ f (f f)) (λ x x))))

(define-language t-CESK*
  (x variable-not-otherwise-mentioned)
  (v (lmd x e)
     number)
  (op * / + -)
  (a number)
  (t number)
  (e x
     v
     (e e)
     (op e ...))
  (vp (v p))
  (c (e p))
  (p ((x a) ...))
  (k mt
     (arg c a)
     (fun vp a)
     (op (vp ...) (c ...) a))
  (z vp k)
  (s ((a z) ...)))
(define-metafunction t-CESK*
  [(inj e) ((e ()) ((0 mt)) 0 1)])
(define-metafunction t-CESK*
  [(dlt * number ...) ,(apply * (term (number ...)))]
  [(dlt / number ...) ,(apply / (term (number ...)))]
  [(dlt + number ...) ,(apply + (term (number ...)))]
  [(dlt - number ...) ,(apply - (term (number ...)))])
(define-metafunction t-CESK*
  [(lookup x p) ,(second (findf (lambda (obj) (equal? (first obj) (term x))) (term p)))]
  [(lookup a s) ,(second (findf (lambda (obj) (equal? (first obj) (term a))) (term s)))])
(define-metafunction t-CESK*
  [(insert x a p) ,(cons (term (x a)) (term p))]
  [(insert a z s) ,(cons (term (a z)) (term s))])
(define-metafunction t-CESK*
  [(tick t) ,(+ (term t) 1)])
(define-metafunction t-CESK*
  [(alloc t) t])
(define reduce
  (reduction-relation
   t-CESK*
   (--> ((x p) s a t) ((lookup (lookup x p) s) s a (tick t)))
   (--> (((e_1 e_2) p) s a t) ((e_1 p) (insert (alloc t) (arg (e_2 p) a) s) (alloc t) (tick t)))
   (--> (vp ((a_1 z_1) ... (a_3 (arg c a_4)) (a_2 z_2) ...) a_3 t)
        ,(let ([s (term ((a_1 z_1) ... (a_3 (arg c a_4)) (a_2 z_2) ...))])
           (term (c (insert (alloc t) (fun vp a_4) ,s) (alloc t) (tick t)))))
   (--> (vp ((a_1 z_1) ... (a_3 (fun ((lmd x e) p) a_4)) (a_2 z_2) ...) a_3 t)
        ,(let ([s (term ((a_1 z_1) ... (a_3 (fun ((lmd x e) p) a_4)) (a_2 z_2) ...))])
           (term ((e (insert x (alloc t) p)) (insert (alloc t) vp ,s) a_4 (tick t)))))
   (--> (((op e_1 e_2 ...) p) s a t)
        ,(let ([cs (map (lambda (e) (list e (term p))) (term (e_2 ...)))])
           (term ((e_1 p) (insert (alloc t) (op () ,cs a) s) (alloc t) (tick t)))))
   (--> (vp_1 ((a_1 z_1) ... (a_3 (op (vp_2 ...) (c_1 c_2 ...) a_4)) (a_2 z_2) ...) a_3 t)
        ,(let ([s (term ((a_1 z_1) ... (a_3 (op (vp_2 ...) (c_1 c_2 ...) a_4)) (a_2 z_2) ...))])
           (term (c_1 (insert (alloc t) (op (vp_2 ... vp_1) (c_2 ...) a_4) ,s) (alloc t) (tick t)))))
   (--> ((v_1 p_1) ((a_1 z_1) ... (a_3 (op ((v_2 p_2) ...) () a_4)) (a_2 z_2) ...) a_3 t)
        ,(let ([s (term ((a_1 z_1) ... (a_3 (op ((v_2 p_2) ...) () a_4)) (a_2 z_2) ...))])
           (term (((dlt op v_2 ... v_1) ()) ,s a_4 (tick t)))))))