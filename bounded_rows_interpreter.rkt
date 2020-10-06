#lang racket

(require racket/match
         racket/set)

;; GTFL using BRR in the intermediate language.
;; This file uses Bounded Rows but the non-space efficient semantics
;; that is presented for RL.  If you are interested in
;; the RL^+ language (space efficient), please visit
;; bounded_rows_space_efficient_interpreter.rkt


;; Syntax as defined in Fig. 1

(define label? symbol?)

(define (Type? e)
  (match e
    ['Int #t]
    ['Bool #t]
    [`(,(? Type?) -> ,(? Type?)) #t]
    [(hash-table ((? label?) (? Type?)) ...) #t]
    [else #f]))

(define (SrcGType? t)
  (match t
    ['? #t]
    ['Int #t]
    ['Bool #t]
    [`(,(? SrcGType?) -> ,(? SrcGType?)) #t]
    [(list 'Rec (hash-table ((? label?) (? SrcGType?)) ...)) #t]
    [(list 'Row (hash-table ((? label?) (? SrcGType?)) ...)) #t]
    [else #f]))

(define Var? symbol?)

(define (Term? t)
  (match t
    [(? number?) #t]
    ['true #t]
    ['false #t] ; Note this will be key: false != #f
    [(? Var?) #t]
    [`(λ (,(? Var?) : ,(? SrcGType?)) ,(? Term?)) #t]
    [`(,(? Term?) ,(? Term?)) #t]
    [`(,(? Term?) + ,(? Term?)) #t]
    [`(,(? Term?) * ,(? Term?)) #t]
    [`(,(? Term?) <= ,(? Term?)) #t]
    [`(if ,(? Term?) then (? Term?) else (? Term?)) #t]
    [(hash-table ((? label?) (? Term?)) ...) #t]
    [`(proj ,(? Term?) ,(? label?)) #t]
    [`(,(? Term?) :: ,(? SrcGType?)) #t]
    [else #f]))

;; Definition of the environment datatype

(define Env?
  (listof (cons/c Var? SrcGType?)))

(define/contract (Γ-in? x Γ)
  (-> Var? Env? (or/c SrcGType? false?))
  (let ([lookup (assoc x Γ)])
    (if lookup
        (cdr lookup)
        (error (format "Could not find ~a in Γ" x)))))

(define/contract Γ-mt
  Env?
  empty)

(define/contract (Γ-extend x S Γ)
  (-> Var? SrcGType? Env? Env?)
  (cons (cons x S) Γ))

;; Definition of Helper functions

(define/contract (~dom S)
  (-> SrcGType? (or/c false? SrcGType?))
  (match S
    [`(,(? SrcGType? dom) -> ,(? SrcGType?)) dom]
    ['? '?]
    [else #f]))

(define/contract (~cod S)
  (-> SrcGType? (or/c false? SrcGType?))
  (match S
    [`(,(? SrcGType?) -> ,(? SrcGType? cod)) cod]
    ['? '?]
    [else #f]))

(define/contract (~proj S l)
  (-> SrcGType? label? (or/c false? SrcGType?))
  (match S
    [`(Rec ,hash) (hash-ref hash l #f)]
    [`(Row ,hash) (hash-ref hash l '?)]
    ['? '?]
    [else #f]))

(define/contract (consistent-subtyping S_1 S_2)
  (-> SrcGType? SrcGType? boolean?)
  (match (cons S_1 S_2)
    [`(? . ,S) #t]
    [`(S . ?) #t]
    [`(Int . Int) #t]
    [`(Bool . Bool) #t]
    [`((,S_11 -> ,S_12) . (,S_21 -> ,S_22)) (and (consistent-subtyping S_21 S_11)
                                                 (consistent-subtyping S_21 S_22))]
    [`([Rec ,hash_l] . [Rec ,hash_r])
     (andmap (λ (M) (let* ([l (car M)]
                           [S_2 (cdr M)]
                           [S_1 (hash-ref hash_l l #f)])
                      (and S_1 (consistent-subtyping S_1 S_2))))
             (hash->list hash_r))]
    [`([Rec ,hash_l] . [Row ,hash_r])
     (andmap (λ (M) (let* ([l (car M)]
                           [S_2 (cdr M)]
                           [S_1 (hash-ref hash_l l #f)])
                      (and S_1 (consistent-subtyping S_1 S_2))))
             (hash->list hash_r))]
    [`([Row ,hash_l] . [Rec ,hash_r])
     (andmap (λ (M) (let* ([l (car M)]
                           [S_2 (cdr M)]
                           [S_1 (hash-ref hash_l l #f)])
                      (or (not S_1) (consistent-subtyping S_1 S_2))))
             (hash->list hash_r))]
    [`([Row ,hash_l] . [Row ,hash_r])
     (andmap (λ (M) (let* ([l (car M)]
                           [S_2 (cdr M)]
                           [S_1 (hash-ref hash_l l #f)])
                      (or (not S_1) (consistent-subtyping S_1 S_2))))
             (hash->list hash_r))]
     [else #f]))

; We now define Mappings and GType with bounded rows and records:
(define (GType? t)
  (match t
    ['? #t]
    ['Int #t]
    ['Bool #t]
    [`(,(? GType?) -> ,(? GType?)) #t]
    [(list 'Rec (hash-table ((? label?) (? Mapping?)) ...)) #t]
    [(list 'Row (hash-table ((? label?) (? Mapping?)) ...)) #t]
    [else #f]))

(define (Mapping? M)
  (match M
    ['∅ #t]
    [`(,(? GType?) O) #t]
    [`(,(? GType?) R) #t]
    [otherwise #f]))

(define Ev? (cons/c GType? GType?))


(define (RTerm? x)
  (match x
    [(? number?) #t]
    ['true #t]
    ['false #t]
    [(? Var?) #t]
    [`(λ (,(? Var?) : ,(? GType?)) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RTerm?) (,(? GType?) -> ,(? GType?)) ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RTerm?) + ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RTerm?) <= ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RTerm?) * ,(? Ev?) ,(? RTerm?)) #t]
    [`(if ,(? Ev?) ,(? RTerm?) ,(? GType?) then ,(? Ev?) ,(? RTerm?) else ,(? Ev?) ,(? RTerm?)) #t]
    [(? hash? hash)
     (andmap identity (hash-map hash (λ (key t) (RTerm? t))))]
    [`(proj ,(? Ev?) ,(? RTerm?) ,(? GType?) ,(? label?)) #t]
    [`(,(? Ev?) ,(? GType?) ,(? RTerm?)) #t]
    [otherwise #f]))

(define (RawValue? u)
  (match u
    [(? number?) #t]
    ['true #t]
    ['false #t]
    [(? Var?) #t]
    [`(λ (,(? Var?) : ,(? GType?)) ,(? RTerm?)) #t]
    [(? hash? hash)
     (andmap identity (hash-map hash (λ (key t) (Value? t))))]
    [otherwise #f]))

(define (Value? v)
  (match v
    [(? RawValue?) #t]
    [`(,(? Ev?) ,(? GType?) ,(? RawValue?)) #t]
    [otherwise #f]))

; We have chosen to only provide an interpreter for bounded rows,
; As the runtime typing is not syntax directed. (because the well-formed mappings judgement is not syntax directed)

;; Runtime system
;; While we /could/ have written a more optimal implementation,
;; We chose instead to be as faithtul to the semantics written in the paper
;; As possible.

;; Fig. 4 on the paper.

(define (EvFrame? F)
  (match F
    [`(,(? GType?) □) #t] ; While in the paper is exactly a hole, here it's more specific, as it is for the ascription case
    [`(□ + ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RawValue?) + ,□) #t]
    [`(□ <= ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RawValue?) <= ,□) #t]
    [`(□ * ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RawValue?) * ,□) #t]
    [`(□ (,(? GType?) -> ,(? GType?)) ,(? Ev?) ,(? RTerm?)) #t]
    [`(,(? Ev?) ,(? RawValue?) (,(? GType?) -> ,(? GType?)) □) #t]
    [`(proj □ ,(? GType?) ,(? label?)) #t]
    [`(if □ ,(? GType?) then ,(? Ev?) ,(? RTerm?) else ,(? Ev?) ,(? RTerm?)) #t]
    [otherwise #f]))

(define (ECtxt-elem? E)
  (match E
    [`(((,(? label?) . ,(? Value?)) ...) ,(? label?) □ ((,(? label?) . ,(? RTerm?)) ...)) #t]
    [`(,(? EvFrame?) ,(? Ev?)) #t]
    [otherwise #f]))

(define ECtxt? (listof ECtxt-elem?))
  
;; Helper Functions

;; Definition of Helper functions

(define/contract (~~dom S)
  (-> GType? (or/c false? GType?))
  (match S
    [`(,(? GType? dom) -> ,(? GType?)) dom]
    ['? '?]
    [else #f]))

(define/contract (~~cod S)
  (-> GType? (or/c false? GType?))
  (match S
    [`(,(? GType?) -> ,(? GType? cod)) cod]
    ['? '?]
    [else #f]))

(define/contract (~~proj S l)
  (-> GType? label? (or/c false? GType?))
  (match S
    [`(Rec ,hash) (hash-ref hash l #f)]
    [`(Row ,hash) (hash-ref hash l '?)]
    ['? '?]
    [else #f]))

(define/contract (idom ev)
  (-> Ev? (or/c false? Ev?))
  (let ([S_2 (~~dom (cdr ev))]
        [S_1 (~~dom (car ev))])
    (and S_1 S_2 (cons S_2 S_1))))

(define/contract (icod ev)
  (-> Ev? (or/c false? Ev?))
  (let ([S_1 (~~cod (car ev))]
        [S_2 (~~cod (cdr ev))])
    (and S_1 S_2 (cons S_1 S_2))))

(define/contract (iproj ev l)
  (-> Ev? label? (or/c false? Ev?))
  (let ([S_1 (~~proj (car ev) l)]
        [S_2 (~~proj (cdr ev) l)])
    (and S_1 S_2 (cons S_1 S_2))))

;; Note: The following definitions are exactly the same as in gradual_rows_interpreter.rkt.
;;       (Up to interp.  We introduce a marker where new code appears)

(define (error? e)
  (equal? e 'error))

(define/contract (subst e_2 x e_1)
  (-> RTerm? Var? RTerm? RTerm?)
  (match e_1
    [(? Var? y) (if (eq? x y) e_2 e_1)]
    [`(λ (,(? Var? y) : ,(? GType? S)) ,(? RTerm? t))
     (if (eq? x y)
         e_1
         `(λ (,y : ,S) ,(subst e_2 x t)))]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) (,(? GType? S_1) -> ,(? GType? S_2)) ,(? Ev? ev_2) ,(? RTerm? t_2))
     `(,ev_1 ,(subst e_2 x t_1) (,S_1 -> ,S_2) ,ev_2 ,(subst e_2 x t_2))]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) + ,(? Ev? ev_2) ,(? RTerm? t_2))
     `(,ev_1 ,(subst e_2 x t_1) + ,ev_2 ,(subst e_2 x t_2))]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) <= ,(? Ev? ev_2) ,(? RTerm? t_2))
     `(,ev_1 ,(subst e_2 x t_1) <= ,ev_2 ,(subst e_2 x t_2))]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) * ,(? Ev? ev_2) ,(? RTerm? t_2))
     `(,ev_1 ,(subst e_2 x t_1) * ,ev_2 ,(subst e_2 x t_2))]
    [`(if ,(? Ev? ev_1) ,(? RTerm? t_1) ,(? GType? S) then ,(? Ev? ev_2) ,(? RTerm? t_2) else ,(? Ev? ev_3) ,(? RTerm? t_3))
     `(if ,ev_1 ,(subst e_2 x t_1) ,S then ,ev_2 ,(subst e_2 x t_2) else ,ev_3 ,(subst e_2 x t_3))]
    [(? hash? hash)
     (make-hash (hash-map hash (λ (key t)
                                 (cons key (subst e_2 x t)))))]
    [`(proj ,(? Ev? ev_1) ,(? RTerm? t) ,(? GType? S ) ,(? label? l))
     `(proj ,ev_1 ,(subst e_2 x t) ,S ,l)]
    [`(,(? Ev? ev) ,(? GType? S ) ,(? RTerm? t))
     `(,ev ,S ,(subst e_2 x t))]
    [otherwise e_1]))

; Function equivalent to the Notions of Reduction presented in Fig. 4.
(define/contract (↝ e_1)
  (-> RTerm? (or/c false? RTerm? error?))
  (match e_1
    [`(,(? Ev?) ,(? number? n_1) + ,(? Ev?) ,(? number? n_2)) (+ n_1 n_2)]
    [`(,(? Ev?) ,(? number? n_1) * ,(? Ev?) ,(? number? n_2)) (* n_1 n_2)]
    [`(,(? Ev?) ,(? number? n_1) <= ,(? Ev?) ,(? number? n_2)) (if (<= n_1 n_2) 'true 'false)]
    [`(,(? Ev? ev_1) (λ (,(? Var? x) : ,(? GType? S)) ,(? RTerm? t)) (,(? GType?) -> ,(? GType? S_cod)) ,(? Ev? ev_2) ,(? RawValue? u))
     (let ([ev_3 (trans ev_2 (idom ev_1))])
       (if ev_3
           `(,(icod ev_1) ,S_cod ,(subst `(,ev_3 ,S ,u) x t))
           'error))]
    [`(if ,(? Ev?) true ,(? GType? S) then ,(? Ev? ev_2) ,(? RTerm? t_2) else ,(? Ev?) ,(? RTerm?))
     `(,ev_2 ,S ,t_2)]
    [`(if ,(? Ev?) false ,(? GType? S) then ,(? Ev?) ,(? RTerm?) else ,(? Ev? ev_3) ,(? RTerm? t_3))
     `(,ev_3 ,S ,t_3)]
    [`(proj ,(? Ev? ev) ,(? hash? hash) ,(? GType? S) ,(? label? l))
     (let ([v_j (hash-ref hash l #f)])
       (and (RawValue? hash)
            v_j
            `(,(iproj ev l) ,S ,v_j)))]
    [otherwise #f]))

(define/contract (stackify e)
  ; Take a term and separate it into an expression and a list of pending contexts (evaluation stack)
  (-> RTerm? (cons/c RTerm? ECtxt?))
  (match e
    [(? number?) (list e)] ;; (list e) = (cons e empty)
    ['true (list e)]
    ['false (list e)]
    [(? Var?) (list e)]
    [`(λ (,(? Var?) : ,(? GType?)) ,(? RTerm?)) (list e)]
    [`(,(? Ev? ev_1) ,(? RawValue? u) (,(? GType? S_1) -> ,(? GType? S_2)) ,(? Ev? ev_2) ,(? RTerm? t))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((,ev_1 ,u (,S_1 -> ,S_2) □)
                                      ,ev_2))))])]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) (,(? GType? S_1) -> ,(? GType? S_2)) ,(? Ev? ev_2) ,(? RTerm? t_2))
     (match (stackify t_1)
       [(cons t stack)
        (cons t (append stack (list `((□ (,S_1 -> ,S_2) ,ev_2 ,t_2)
                                      ,ev_1))))])]
    [`(,(? Ev? ev_1) ,(? RawValue? u) + ,(? Ev? ev_2) ,(? RTerm? t))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((,ev_1 ,u + □)
                                      ,ev_2))))])]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) + ,(? Ev? ev_2) ,(? RTerm? t_2))
     (match (stackify t_1)
       [(cons t stack)
        (cons t (append stack (list `((□ + ,ev_2 ,t_2)
                                      ,ev_1))))])]
    [`(,(? Ev? ev_1) ,(? RawValue? u) * ,(? Ev? ev_2) ,(? RTerm? t))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((,ev_1 ,u * □)
                                      ,ev_2))))])]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) * ,(? Ev? ev_2) ,(? RTerm? t_2))
     (match (stackify t_1)
       [(cons t stack)
        (cons t (append stack (list `((□ * ,ev_2 ,t_2)
                                      ,ev_1))))])]
    [`(,(? Ev? ev_1) ,(? RawValue? u) <= ,(? Ev? ev_2) ,(? RTerm? t))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((,ev_1 ,u <= □)
                                      ,ev_2))))])]
    [`(,(? Ev? ev_1) ,(? RTerm? t_1) <= ,(? Ev? ev_2) ,(? RTerm? t_2))
     (match (stackify t_1)
       [(cons t stack)
        (cons t (append stack (list `((□ <= ,ev_2 ,t_2)
                                      ,ev_1))))])]
    [`(if ,(? Ev? ev_1) ,(? RTerm? t_1) ,(? GType? S) then ,(? Ev? ev_2) ,(? RTerm? t_2) else ,(? Ev? ev_3) ,(? RTerm? t_3))
     (match (stackify t_1)
       [(cons t stack)
        (cons t (append stack (list `((if □ ,S then ,ev_2 ,t_2 else ,ev_3 ,t_3)
                                      ,ev_1))))])]
    [(? hash? hash)
     (let* ([mappings (hash->list hash)]
            [is-value? (λ (x) (Value? (cdr x)))]
            [values (filter is-value? mappings)]
            [terms (filter-not is-value? mappings)])
       (if (empty? terms) ; it's a value!
           (list e)
           (match terms
             [(cons (cons l hd) tl)
              (match (stackify hd)
                [(cons t stack)
                 (append stack (list `(,values ,l □ ,terms)))])])))]
    [`(proj ,(? Ev? ev) ,(? RTerm? t) ,(? GType? S) ,(? label? l))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((proj □ ,S ,l)
                                      ,ev))))])]
    [`(,(? Ev? ev) ,(? GType? S) ,(? RawValue? t))
     (list e)]
    [`(,(? Ev? ev) ,(? GType? S) ,(? RTerm? t))
     (match (stackify t)
       [(cons t stack)
        (cons t (append stack (list `((,S □)
                                      ,ev))))])]))

(define/contract (plug E t)
  (-> ECtxt-elem? RTerm? RTerm?)
  (match E
    [`(,values ,(? label? l) □ ,terms)
     (make-hash (append values (list (cons l t)) terms))]
    [`(,(? EvFrame? F) ,(? Ev? ev_t ))
     (match F
       [`(,(? GType? S) □) `(,ev_t ,S ,t)]
       [`(□ + ,(? Ev? ev_2) ,(? RTerm? t_2)) `(,ev_t ,t + ,ev_2 ,t_2)]
       [`(,(? Ev? ev_1) ,(? RawValue? t_1) + ,□) `(,ev_1 ,t_1 + ,ev_t ,t)]
       [`(□ * ,(? Ev? ev_2) ,(? RTerm? t_2)) `(,ev_t ,t * ,ev_2 ,t_2)]
       [`(,(? Ev? ev_1) ,(? RawValue? t_1) * ,□) `(,ev_1 ,t_1 * ,ev_t ,t)]
       [`(□ <= ,(? Ev? ev_2) ,(? RTerm? t_2)) `(,ev_t ,t <= ,ev_2 ,t_2)]
       [`(,(? Ev? ev_1) ,(? RawValue? t_1) <= ,□) `(,ev_1 ,t_1 <= ,ev_t ,t)]
       [`(□ (,(? GType? S_1) -> ,(? GType? S_2)) ,(? Ev? ev_2) ,(? RTerm? t_2))
        `(,ev_t ,t (,S_1 -> ,S_2) ,ev_2 ,t_2)]
       [`(,(? Ev? ev_1) ,(? RawValue? u) (,(? GType? S_1) -> ,(? GType? S_2)) □)
        `(,ev_1 ,u (,S_1 -> ,S_2) ,ev_t ,t)]
       [`(proj □ ,(? GType? S) ,(? label? l))
        `(proj ,ev_t ,t ,S ,l)]
       [`(if □ ,(? GType? S) then ,(? Ev? ev_2) ,(? RTerm? t_2) else ,(? Ev? ev_3) ,(? RTerm? t_3))
        `(if ,ev_t ,t ,S then ,ev_2 ,t_2 else ,ev_3 ,t_3)])]))
    
(define/contract (contextual-reduction e E)
  (-> RTerm? ECtxt? (cons/c (or/c false? RTerm? error?) ECtxt?))
  #;(displayln (format "Stepping ~s with ~s" e E))
  (match (cons e E)
    [`( (,(? Ev? ev_2) ,(? GType? S_2) ,(? RawValue? u))
        .
        ((,F ,ev_1) . ,stack))
     (let ([ev_c (trans ev_2 ev_1)])
       #;(displayln (format "cast composition"))
       (cons (if ev_c
                 (plug `(,F ,ev_c) u)
                 'error)
             stack))]
    [otherwise (cons (↝ e) E)]))


(define/contract (interp/stack e E)
  (-> RTerm? ECtxt? (cons/c (or/c RTerm? error?) ECtxt?))
  (match (contextual-reduction e E)
    [`(error . ,stack) (cons 'error stack)] ; Stop evaluation : error
    [(list #f)  ; Cannot take a step!
     (list e)] ; that is the end of evaluation.
    [(cons #f (cons hd stack)) ; We couldn't take a step here so we must pop the stack.
     (interp/stack (plug hd e) stack)]
    [`(,step . ,stack) ; Continue evaluation.  Substitution might require growing the stack!
     (match (stackify step)
       [`(,t . ,recent_stack)
        (interp/stack t (append recent_stack stack))])]))

(define/contract (interp e)
  (-> RTerm? (or/c RTerm? error?))
  (match (stackify e)
    [`(,t . ,stack)
     (let ([stack-step (interp/stack t stack)])
       (if (empty? (cdr stack-step))
           (car stack-step)
           (error "left something unevaluated. retry.")))]))

;; New code :  The following functions change between gradual and bounded rows.
;; Initial Evidence as defined in Fig. 5.

(define/contract (I S_1 S_2)
  (-> GType? GType? (or/c false? Ev?))
  (match (cons S_1 S_2)
    [`(Int . Int) `(Int . Int)]
    [`(Bool . Bool) `(Bool . Bool)]
    [`(? . ?) `(? . ?)]
    [`(? . Int) `(Int . Int)]
    [`(? . Bool) `(Bool . Bool)]
    [`(Int . ?) `(Int . Int)]
    [`(Bool . ?) `(Bool . Bool)]
    [`((,S_11 -> ,S_12) . ?) (I `(,S_11 -> ,S_12) `(? -> ?))]
    [`(? . (,S_21 -> ,S_22)) (I `(? -> ?) `(,S_21 -> ,S_22))]
    [`((,S_11 -> ,S_12) . (,S_21 -> ,S_22))
     (let ([dom (I S_21 S_11)]
           [cod (I S_12 S_22)])
       (and dom cod
            `((,(cdr dom) -> ,(car cod)) . (,(car dom) -> ,(cdr cod)))))]
    [`(? . (Rec ,hash_r))
     (I `(Row #hash()) `(Rec ,hash_r))]
    [`(? . (Row ,hash_r))
     (I `(Row #hash()) `(Row ,hash_r))]
    [`((Rec ,hash_l) . ?)
     `((Rec ,hash_l) . (Row #hash()))]
    [`((Row ,hash_l) . ?)
     `((Row ,hash_l) . (Row #hash()))]
    [`((Rec ,hash_l) . (Rec ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key)
                             (let* ([M_l (hash-ref hash_l key '∅)]
                                    [M_r (hash-ref hash_r key '∅)]
                                    [pair (I^M M_l M_r)])
                               (and pair (cons key pair))))
                           keys)])
       (and (andmap identity mappings)
            (let ([mappings-l (map (λ (x) (cons (car x) (car (cdr x)))) mappings)]
                  [mappings-r (map (λ (x) (cons (car x) (cdr (cdr x)))) mappings)])
              `((Rec ,(make-hash mappings-l)) . (Rec ,(make-hash mappings-r))))))]
    [`((Rec ,hash_l) . (Row ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key)
                             (let* ([M_l (hash-ref hash_l key '∅)]
                                    [M_r (hash-ref hash_r key '(? O))]
                                    [pair (I^M M_l M_r)])
                               (and pair (cons key pair))))
                           keys)])
       (and (andmap identity mappings)
            (let ([mappings-l (map (λ (x) (cons (car x) (car (cdr x)))) mappings)]
                  [mappings-r (map (λ (x) (cons (car x) (cdr (cdr x)))) mappings)])
              `((Rec ,(make-hash mappings-l)) . (Rec ,(make-hash mappings-r))))))]
    [`((Row ,hash_l) . (Rec ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key)
                             (let* ([M_l (hash-ref hash_l key '(? O))]
                                    [M_r (hash-ref hash_r key '∅)]
                                    [pair (I^M M_l M_r)])
                               (and pair (cons key pair))))
                           keys)])
       (and (andmap identity mappings)
            (let ([mappings-l (map (λ (x) (cons (car x) (car (cdr x)))) mappings)]
                  [mappings-r (map (λ (x) (cons (car x) (cdr (cdr x)))) mappings)])
              `((Row ,(make-hash mappings-l)) . (Rec ,(make-hash mappings-r))))))]
    [`((Row ,hash_l) . (Row ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key)
                             (let* ([M_l (hash-ref hash_l key '(? O))]
                                    [M_r (hash-ref hash_r key '(? O))]
                                    [pair (I^M M_l M_r)])
                               (and pair (cons key pair))))
                           keys)])
       (and (andmap identity mappings)
            (let ([mappings-l (map (λ (x) (cons (car x) (car (cdr x)))) mappings)]
                  [mappings-r (map (λ (x) (cons (car x) (cdr (cdr x)))) mappings)])
              `((Row ,(make-hash mappings-l)) . (Row ,(make-hash mappings-r))))))]))

(define/contract (I^M M_1 M_2)
  (-> Mapping? Mapping? (or/c false? (cons/c Mapping? Mapping?)))
  (match (cons M_1 M_2)
    [`(,M . ∅) `(,M . ∅)]
    [`((,S_1 ,Ann) . (,S_2 R))
     (let ([pair (I S_1 S_2)])
       (and pair `((,(car pair) R) . (,(cdr pair) R))))]
    [`((,S_1 ,Ann) . (,S_2 O))
     (let ([pair (I S_1 S_2)])
       (if pair
           `((,S_1 ,Ann) . (,(cdr pair) O))
           `((,S_1 ,Ann) . ∅)))]
    [otherwise #f]))

;; Gradual Meet as defined in Fig. 19.

(define/contract (⊓ S_1 S_2)
  (-> GType? GType? (or/c false? GType?))
  (match (cons S_1 S_2)
    [`(? . ,S) S]
    [`(,S . ?) S]
    [`(Int . Int) 'Int]
    [`(Bool . Bool) 'Bool]
    [`((,S_11 -> ,S_12) . (,S_21 -> ,S_22))
     (let ([dom (⊓ S_11 S_21)]
           [cod (⊓ S_12 S_22)])
       (and dom cod
            `(,dom -> ,cod)))]
    [`((Rec ,hash_l) . (Rec ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key) (let* ([M_l (hash-ref hash_l key '∅)]
                                           [M_r (hash-ref hash_r key '∅)]
                                           [meet (⊓^M M_l M_r)])
                                      (and meet (cons key meet))))
                           keys)])
            (and (andmap identity mappings) `(Rec ,(make-hash mappings))))]
    [`((Rec ,hash_l) . (Row ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key) (let* ([M_l (hash-ref hash_l key '∅)]
                                           [M_r (hash-ref hash_r key '(? O))]
                                           [meet (⊓^M M_l M_r)])
                                      (and meet (cons key meet))))
                           keys)])
            (and (andmap identity mappings) `(Rec ,(make-hash mappings))))]
    [`((Row ,hash_l) . (Rec ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key) (let* ([M_l (hash-ref hash_l key '(? O))]
                                           [M_r (hash-ref hash_r key '∅)]
                                           [meet (⊓^M M_l M_r)])
                                      (and meet (cons key meet))))
                           keys)])
            (and (andmap identity mappings) `(Rec ,(make-hash mappings))))]
    [`((Row ,hash_l) . (Row ,hash_r))
     (let* ([keys (set-union (hash-keys hash_l) (hash-keys hash_r))]
            [mappings (map (λ (key) (let* ([M_l (hash-ref hash_l key '(? O))]
                                           [M_r (hash-ref hash_r key '(? O))]
                                           [meet (⊓^M M_l M_r)])
                                      (and meet (cons key meet))))
                           keys)])
            (and (andmap identity mappings) `(Row ,(make-hash mappings))))]
    [otherwise #f]))

(define/contract (⊓^M M_1 M_2)
  (-> Mapping? Mapping? (or/c false? Mapping?))
  (match (cons M_1 M_2)
    [`(∅ . ∅) '∅]
    [`(∅ . (,S O)) '∅]
    [`((,S O) . ∅) '∅]
    [`((,S_1 R) . (,S_2 ,Ann))
     (let ([meet (⊓ S_1 S_2)])
       (and meet `(,meet R)))]
    [`((,S_1 ,Ann) . (,S_2 R))
     (let ([meet (⊓ S_1 S_2)])
       (and meet `(,meet R)))]
    [`((,S_1 O) . (,S_2 O))
     (let ([meet (⊓ S_1 S_2)])
       (if meet
           `(,meet O)
           '∅))]
    [otherwise #f]))

;; Definition of Consistent Transitivity Following Proposition 3.3
(define/contract (trans ev_1 ev_2)
  (-> Ev? Ev? (or/c false? Ev?))
  (let ([meet (⊓ (cdr ev_1) (car ev_2))])
    (and meet
         (let ([Il (I (car ev_1) meet)]
               [Ir (I meet (cdr ev_2))])
           (and Il Ir
                (I (car Il) (cdr Ir)))))))

(module* test #f
  (require rackunit)
  ;; Tests for Type?
  (check-true (Type? 'Int))
  (check-true (Type? (make-hash '((x . Int) (y . Bool) (z . (Int -> Int))))))
  (check-false (Type? '?))
  (check-false (Type? '('Int ->)))
  ;; Tests for GType?
  (check-true (GType? '?))
  (check-true (GType? (list 'Row (make-hash '((x . (Int O)) (y . (Bool R)) (z . ((Int -> Int) R)))))))
  (check-true (SrcGType? `(Rec ,(make-hash '((x . Int) (y . Bool) (z . (Int -> Int)))))))
  (check-true (GType? `(Int -> Int)))
  (check-false (GType? `notatype))

  (check-not-false (Γ-in? 'x `((a . Int) (b . ?) (x . Bool) (z . Bool))))
  (check-exn exn:fail? (lambda () (Γ-in? 'y `((a . Bool)))))

  ;; Some tests for consistent-subtyping

  (check-true (consistent-subtyping `(Rec ,(make-hash '((x . Int) (y . Bool) (z . ?))))
                                    `(Rec ,(make-hash))))
  (check-false (consistent-subtyping `(Rec ,(make-hash '((x . Int) (y . Bool) (z . ?))))
                                    `(Rec ,(make-hash '((w . ?))))))
  (check-true (consistent-subtyping `(Row ,(make-hash '((x . Int) (y . Bool) (z . ?))))
                                    `(Rec ,(make-hash '((w . ?))))))
  (check-true (ECtxt-elem? '(((? . ?) 5 + □) (? . ?))))
  (check-true (ECtxt-elem? '((Int □) (? . ?))))
  (check-eq? (interp `((? . ?) 5 + (? . ?) 10))
             15)

  (check-equal? (interp `(if (? . ?) true Int then (Int . Int) ((? . ?) 6 + (? . ?) 7) else (? . ?) 2))
             `((Int . Int) Int 13))


  (check-equal? (interp `(((Int -> Int) . (Int -> Int)) (λ (x : Int) x) (Int -> Int) (Int . Int) 2))
                '((Int . Int) Int 2))
  
  ;z combinator in GTFL
  (define fix-xx '(((? -> ?) . (? -> ?)) x (? -> ?) (? . ?) ((? . ?) ? x)))
  (check-true (RTerm? fix-xx))
  (define fix-v `(λ (v : ?) (((? -> ?) . (? -> ?)) ,fix-xx (? -> ?) (? . ?) v)))
  (check-true (RTerm? fix-v))

  (define fix-repeated `(λ (x : (? -> ?)) (((? -> ?) . (? -> ?)) f (? -> ?) ((? -> ?) . (? -> ?)) ,fix-v)))
  (check-true (RTerm? fix-repeated))
    
  
  (define fix `(λ (f : (? -> ?)) ((((? -> ?) -> ?) . ((? -> ?) -> ?)) ,fix-repeated (? -> ?) (((? -> ?) -> ?) . ((? -> ?) -> ?)) ,fix-repeated)))
  (check-true (RTerm? fix))

  (define factorial
    `((? . ?) ,fix (((? -> ?) -> ?) -> ((Int -> Int) -> (Int -> Int)))
              (((Int -> Int) -> (Int -> Int))
               .
               ((Int -> Int) -> (Int -> Int)))
              (λ (fact : (Int -> Int))
                (λ (x : Int)
                  (if (Bool . Bool) ((Int . Int) x <= (Int . Int) 1)
                      Int
                      then (Int . Int) 1
                      else (Int . Int) ((Int . Int) x * (Int . Int) (((Int -> Int) . (Int -> Int)) fact (Int -> Int) (Int . Int) ((Int . Int) x + (Int . Int) -1))))))))
  (check-true (RTerm? factorial))

  (check-equal? (interp `(((Int -> Int) . (Int -> Int)) ,factorial (Int -> Int) ( Int . Int) 1))
                '((Int . Int) Int 1))
  )
  


