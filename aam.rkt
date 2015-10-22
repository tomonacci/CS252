#lang racket
(require redex)
(require (only-in racket/generator generator yield))
(require (only-in srfi/1 car+cdr))
(require (only-in srfi/8 receive))
(require (only-in unstable/debug debug))

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

(define (enlarge-sigma-domain sigma)
  (+ 1 (apply max (map car sigma))))

(define red-CESK*
  (reduction-relation
   CESK*
   (--> (x rho sigma a)
        ,(receive (v rho) (car+cdr (dict-ref (term sigma) (dict-ref (term rho) (term x))))
           (term (,v ,rho sigma a)))
        "#1")
   (--> ((e_0 e_1) rho sigma a)
        ,(let ([b (enlarge-sigma-domain (term sigma))])
           (term (e_0 rho ,(dict-set (term sigma) b (term (ar e_1 rho a))) ,b)))
        "#2")
   (--> (v rho_0 sigma a_0)
        ,(let ([b (enlarge-sigma-domain (term sigma))])
           (term (e rho_1 ,(dict-set (term sigma) b (term (fn v rho_0 a_1))) ,b)))
        (where (ar e rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#3")
   (--> (v rho_0 sigma a_0)
        ,(let ([b (enlarge-sigma-domain (term sigma))])
           (term (e
                  ,(dict-set (term rho_1) (term x) b)
                  ,(dict-set (term sigma) b (cons (term v) (term rho_0)))
                  a_1)))
        (where (fn (λ x e) rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#4")
   ))

; e.g.: (traces red-CESK* (inj-CESK* '((λ f (f f)) (λ x x))))

(define-extended-language tCESK* LC
  (a number)
  (t number)
  (rho any)
  (kappa mt (arg c a) (fun vp a))
  (sigma any))

; There actually is a minor mistake in the paper, claiming that they can have t_0 = 0.
; This is wrong since it will lead to overwriting (0 . mt) with some other value.
; Here we choose t_0 = 1.
(define (inj-tCESK* expr)
  (term (,expr () ((0 . mt)) 0 1)))

(define (tick t) (+ t 1))
(define alloc identity)

(define red-tCESK*
  (reduction-relation
   tCESK*
   (--> (x rho sigma a t)
        ,(receive (v rho) (car+cdr (dict-ref (term sigma) (dict-ref (term rho) (term x))))
           (term (,v ,rho sigma a ,(tick (term t)))))
        "#1")
   (--> ((e_0 e_1) rho sigma a t)
        ,(let ([b (alloc (term t))])
           (term (e_0 rho ,(dict-set (term sigma) b (term (ar e_1 rho a))) ,b ,(tick (term t)))))
        "#2")
   (--> (v rho_0 sigma a_0 t)
        ,(let ([b (alloc (term t))])
           (term (e rho_1 ,(dict-set (term sigma) b (term (fn v rho_0 a_1))) ,b ,(tick (term t)))))
        (where (ar e rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#3")
   (--> (v rho_0 sigma a_0 t)
        ,(let ([b (alloc (term t))])
           (term (e
                  ,(dict-set (term rho_1) (term x) b)
                  ,(dict-set (term sigma) b (cons (term v) (term rho_0)))
                  a_1
                  ,(tick (term t)))))
        (where (fn (λ x e) rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#4")
   ))

(define (label-expr expr)
  (define label (generator () (let loop ([i 1]) (yield i) (loop (+ i 1)))))
  (let rec ((expr expr))
    (match expr
      [(list 'λ x e) `(,(label) λ ,x ,(rec e))]
      [(list e1 e2) `(,(label) ,(rec e1) ,(rec e2))]
      [(? symbol? x) `(,(label) ,x)]
      )))

(define-language k-CFA-like
  (l number) ; label
  (e (l λ x e)
     (l x)
     (l e e))
  (v (l λ x e))
  (x variable-not-otherwise-mentioned)
  (a (any delta))
  (t (any delta))
  (delta (l ...))
  (kappa mt (ar e rho a) (fn v rho a))
  (rho any)
  (sigma any)
  )

(define (inj-k-CFA-like expr)
  (term (,(label-expr expr) () (((#f ()) . mt)) (#f ()) (#f ()))))

(define-metafunction k-CFA-like
  [(tickk (l x) rho sigma a t) t]
  [(tickk (l e_0 e_1) rho sigma a (any delta)) (l delta)]
  [(tickk v rho sigma a t)
   t
   (where (ar e_ar rho_ar a_ar) ,(dict-ref (term sigma) (term a)))]
  [(tickk v rho sigma a (l delta))
   (#f ,(cons (term l) (term delta)))
   (where (fn v_fn rho_fn (any_fn0 any_fn1)) ,(debug (dict-ref (term sigma) (term a))))]
  )

(define-metafunction k-CFA-like
  [(allock (l_0 (l_1 any_0 ...) e) rho sigma a (any delta)) (l_1 delta)]
  [(allock v rho sigma a (any delta))
   (l delta)
   (where (ar (l any_0 ...) rho_ar a_ar) ,(dict-ref (term sigma) (term a)))]
  [(allock v rho sigma a (any delta))
   (x delta)
   (where (fn (l λ x e) rho_fn a_fn) ,(dict-ref (term sigma) (term a)))]
  )

(define red-k-CFA-like
  (reduction-relation
   k-CFA-like
   (--> ((l x) rho sigma a t)
        ,(receive (v- rho-) (car+cdr (dict-ref (term sigma) (dict-ref (term rho) (term x))))
           (term (,v- ,rho- sigma a (tickk (l x) rho sigma a t))))
        "#1")
   (--> ((l e_0 e_1) rho sigma a t)
        ,(let ([b (term (allock (l e_0 e_1) rho sigma a t))])
           (term (e_0
                  rho
                  ,(dict-set (term sigma) b (term (ar e_1 rho a)))
                  ,b
                  (tickk (l e_0 e_1) rho sigma a t))))
        "#2")
   (--> (v rho_0 sigma a_0 t)
        ,(let ([b (term (allock v rho_0 sigma a_0 t))])
           (term (e
                  rho_1
                  ,(dict-set (term sigma) b (term (fn v rho_0 a_1)))
                  ,b
                  (tickk v rho_0 sigma a_0 t))))
        (where (ar e rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#3")
   (--> (v rho_0 sigma a_0 t)
        ,(let ([b (term (allock v rho_0 sigma a_0 t))])
           (term (e
                  ,(dict-set (term rho_1) (term x) b)
                  ,(dict-set (term sigma) b (cons (term v) (term rho_0)))
                  a_1
                  (tickk v rho_0 sigma a_0 t))))
        (where (fn (l λ x e) rho_1 a_1) ,(dict-ref (term sigma) (term a_0)))
        "#4")
   ))

; (traces red-k-CFA-like (inj-k-CFA-like '((λ x x) (λ y y))))
; (traces red-k-CFA-like (inj-k-CFA-like '((λ f (f (f f))) (λ x x))))