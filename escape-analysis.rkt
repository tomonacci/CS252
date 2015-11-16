#lang racket

(require redex)

(define-language tCESK
  (e x v (e e))
  (v (λ x e)
     (λ a x e))
  (x variable-not-otherwise-mentioned)
  (κ mt (ar e ρ a) (fn e ρ a))
  (ρ ((x a) ...))
  (σ ((a storable) ...))
  (storable κ (v ρ))
  (a number)
  (t number)
  (E (v ...)) ; escaped lambdas
  )

(define-metafunction tCESK
  lookup : ((any any) ...) any -> any
  [(lookup (any_pre ... (any_k any_v) any_post ...) any_k) any_v]
  )

(define-metafunction tCESK
  extend : ((any any) ...) any any -> ((any any) ...)
  [(extend (any_pre ... (any_k any_ov) any_post ...) any_k any_nv)
   (any_pre ... (any_k any_nv) any_post ...)]
  [(extend (any ...) any_k any_v)
   ((any_k any_v) any ...)]
  )

(define-metafunction tCESK
  tick : e ρ σ a t -> t
  [(tick e ρ σ a t) ,(+ (term t) 1)]
  )

(define-metafunction tCESK
  alloc : e ρ σ a t -> a
  [(alloc e ρ σ a t) t]
  )

(define-metafunction tCESK
  λ-body : v -> e
  [(λ-body (λ x e)) e]
  [(λ-body (λ a x e)) e]
  )

(define-metafunction tCESK
  λ-var : v -> x
  [(λ-var (λ x e)) x]
  [(λ-var (λ a x e)) x]
  )

(define-metafunction tCESK
  reachable? : σ a a -> #t ∨ #f ; for some weird reason if I write 'boolean' as the codomain I get a runtime error :<
  [(reachable? σ a a) #t]
  [(reachable? σ a_from a_to)
   (reachable? σ a a_to)
   (where (ar e ρ a) (lookup σ a_from))]
  [(reachable? σ a_from a_to)
   (reachable? σ a a_to)
   (where (fn e ρ a) (lookup σ a_from))]
  [(reachable? σ a_from a_to) #f]
  )

; The function name is misleading: it modifies E when we actually find something escaping
(define-metafunction tCESK
  check-escape : σ a v E -> E
  [(check-escape σ a_κ v (v_E ...))
   (v v_E ...)
   (where (λ a_v x e) v)
   (where #f (reachable? σ a_κ a_v))
   ]
  [(check-escape σ a_κ v E) E]
  )

(define-metafunction tCESK
  inj : e -> (e ρ σ a t E)
  [(inj e) (e () ((0 mt)) 0 1 ())]
  )

(define rr-concrete
  (reduction-relation
   tCESK
   (--> (x ρ σ a t E)
        (v ρ_v σ a (tick x ρ σ a t) E)
        (where (v ρ_v) (lookup σ (lookup ρ x)))
        "1")
   (--> ((e_1 e_2) ρ σ a t E)
        ,(let ([b (term (alloc (e_1 e_2) ρ σ a t))])
           (term (e_1 ρ (extend σ ,b (ar e_2 ρ a)) ,b (tick (e_1 e_2) ρ σ a t) E)))
        "2")
   (--> (v ρ σ a t E)
        ,(let ([b (term (alloc v ρ σ a t))])
           (term (e ρ_κ (extend σ ,b (fn v ρ a_κ)) ,b (tick v ρ σ a t) E)))
        (where (ar e ρ_κ a_κ) (lookup σ a))
        "3")
   (--> ((λ x e) ρ σ a t E)
        ,(let ([b (term (alloc (λ x e) ρ σ a t))])
           (term ((λ-body v_κ)
                  (extend ρ_κ (λ-var v_κ) ,b)
                  (extend σ ,b ((λ a_κ x e) ρ))
                  a_κ
                  (tick (λ x e) ρ σ a t)
                  (check-escape σ a_κ v_κ E))))
        (where (fn v_κ ρ_κ a_κ) (lookup σ a))
        "4a")
   (--> ((λ a_v x e) ρ σ a t E)
        ,(let ([b (term (alloc (λ a_v x e) ρ σ a t))])
           (term ((λ-body v_κ)
                  (extend ρ_κ (λ-var v_κ) ,b)
                  (extend σ ,b ((λ a_v x e) ρ))
                  a_κ
                  (tick (λ a_v x e) ρ σ a t)
                  (check-escape σ a_κ v_κ E))))
        (where (fn v_κ ρ_κ a_κ) (lookup σ a))
        "4b")
   ))

; Things to try:
; (apply-reduction-relation* rr-concrete (term (inj ((λ x x) (λ y y)))))
; (traces rr-concrete (term (inj ((λ x x) (λ y y)))))
; (traces rr-concrete (term (inj (((λ f (λ g (g f))) (λ x x)) (λ y (y (λ z z)))))))