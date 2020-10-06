#lang racket
(require redex)
(require racket/match)

; NOTE: Redex *needs RAM too*. In fact,
;       this particular program fails with less than 1024MB as
;       a memory limit.

(define (unique? l)
  (not (check-duplicates l)))

; Implementation file for Gradual Rows, as introduced by
; Garcia, Clark and Tanter 2016

(define-language Types
  [T ::= ; Static Types
     B
     (T → T)
     (side-condition [(l_ : T) ...]
                     (unique? (term (l_ ...))))]
  [S ::= ; Gradual Types
     ?
     Int
     Bool
     (S → S)
     (side-condition [(l_ : S) ... *]
                     (unique? (term (l_ ...))))]

  [* ::= ; Marker for rows/records
     ·
     ?]

  [B ::= ; Base Types
     Int
     Bool]
  
  [l ::= string]
  )

(define-extended-language
  GTFLcsub Types
  [t ::= ; terms
     number
     boolean
     x
     (λ (x : S) t)
     (t t)
     (t + t)
     (if t then t else t)
     (side-condition [(l_ = t_) ...]
                     (unique? (term (l_ ...))))
     (t \. l)
     (t :: S)
     (let x : S = t in t) ]
  [x ::= variable-not-otherwise-mentioned]
  [Γ ::=
     ·
     [(x ↦ S) Γ]]

  #:binding-forms ;To get capture-avoiding substitution for free.

  (λ (x : S) t #:refers-to x)
  (let x : S = t in t #:refers-to x)
  )

(define-judgment-form GTFLcsub
  #:mode (~dom I O)
  #:contract (~dom S S)
  [-------
   (~dom (S_1 → S_2) S_1)]
  [-------
   (~dom ? ?)])

(define-judgment-form GTFLcsub
  #:mode (~cod I O)
  #:contract (~cod S S)
  [(~cod (S_1 → S_2) S_2)]
  [(~cod ? ?)])

(define-judgment-form GTFLcsub
  #:mode (~proj I I O)
  #:contract (~proj S l S)
  [#;(side-condition (assoc (term l_2) (term [(l_1 S_1) ...])))
   (where (l_2 S_3) ,(assoc (term l_2) (term [(l_1 S_1) ...])))
   ---------------------------------
   (~proj [(l_1 : S_1) ... *] l_2 S_3)]

  [(side-condition (not (assoc (term l_2) (term [(l_1 S_1) ...]))))
   ----------------------------------
   (~proj [(l_1 : S_1) ... ?] l_2 ?)
   ]
  
  [-------------
   (~proj ? l ?)]
  )

(test-judgment-holds (~proj [("l1" : Int) ("l2" : Bool) ·] "l1" Int))
(test-judgment-holds (~proj [("l1" : Int) ("l2" : Bool) ·] "l2" Bool))
(test-equal (judgment-holds (~proj [("l1" : Int) ("l2" : Bool) ·] "l3" S))
            false)
(test-judgment-holds (~proj [("l1" : Int) ?] "l3" ?))

(define-judgment-form GTFLcsub
  ; Consistent Subtyping
  #:mode (≲ I I)
  #:contract (≲ S S)

  [-------
   (≲ ? S)]

  [-------
   (≲ S ?)]

  [-----------
   (≲ Int Int)]

  [-------------
   (≲ Bool Bool)]

  [(≲ S_21 S_11)
   (≲ S_12 S_22)
   -------------------------------
   (≲ (S_11 → S_12) (S_21 → S_22))]

  [--------------------
   (≲ [(l_1 : S_1) ... *]
      [*])]
  
  [; Point-wise csub, record record
   (~proj [(l_1 : S_1) ... ·] l_2 S_4)
   (≲ S_4 S_2)
   (≲ [(l_1 : S_1) ... ·]
      [(l_3 : S_3) ... ·])  
   --------------------------------
   (≲ [(l_1 : S_1) ... ·]
      [(l_2 : S_2) (l_3 : S_3) ... ·])]

  [; Point-wise csub, record row
   (~proj [(l_1 : S_1) ... ·] l_2 S_4)
   (≲ S_4 S_2)
   (≲ [(l_1 : S_1) ... ·]
      [(l_3 : S_3) ... ?])  
   --------------------------------
   (≲ [(l_1 : S_1) ... ·]
      [(l_2 : S_2) (l_3 : S_3) ... ?])]

  [; Point-wise csub, row record
   (~proj [(l_1 : S_1) ... ?] l_2 S_4)
   (≲ S_4 S_2)
   (≲ [(l_1 : S_1) ... ?]
      [(l_3 : S_3) ... ·])  
   --------------------------------
   (≲ [(l_1 : S_1) ... ?]
      [(l_2 : S_2) (l_3 : S_3) ... ·])]

  [; Point-wise csub, row row, (left declared)
   (≲ S_4 S_2)
   (≲ [(l_1 : S_1) ... (l_2 : S_4) (l_5 : S_5) ... ?]
      [(l_3 : S_3) ... ?])
   --------------------------------------------------
   (≲ [(l_1 : S_1) ... (l_2 : S_4) (l_5 : S_5) ... ?]
      [(l_2 : S_2) (l_3 : S_3) ... ?])
   ]

  [; Point-wise csub, row row, (left undeclared)
   (side-condition ,(not (member (term l_2) (term [l_1 ...]))))
   (≲ [(l_1 : S_1) ... ?]
      [(l_3 : S_3) ... ?])
   --------------------------------------------------
   (≲ [(l_1 : S_1) ... ?]
      [(l_2 : S_2) (l_3 : S_3) ... ?])
   ]  
  )

(test-judgment-holds (≲ [?] [("l" : Int) ?]))

(test-equal (judgment-holds (≲ [("l" : Bool) ?] [("l" : Int) ?]))
            false)

(define-judgment-form GTFLcsub
  ; In Context
  #:mode (∈ I O I)
  #:contract (∈ x S Γ)
  [-------------------
   (∈ x S [(x ↦ S) Γ])]
  [(side-condition ,(not (equal? (term x_1) (term x_2))))
   (∈ x_1 S_1 Γ)
   -----------
   (∈ x_1 S_1 [(x_2 ↦ S_2) Γ])])

(define-judgment-form GTFLcsub
  ; Precision
  #:mode (⊑ I I)
  #:contract (⊑ S S)
  [-------
   (⊑ S ?)]

  [-----------
   (⊑ Int Int)]

  [-------------
   (⊑ Bool Bool)]

  [(⊑ S_11 S_21)
   (⊑ S_12 S_22)
   --------------
   (⊑ (S_11 → S_12)
      (S_21 → S_22))]

  [------
   (⊑ [] [])]

  [(⊑ S_2 S_4)
   (⊑ [(l_1 : S_1) ... (l_3 : S_3) ... ·]
      [(l_5 : S_5) ... ·])
   ------------------------------------------------
   (⊑ [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ·]
      [(l_2 : S_4) (l_5 : S_5) ... ·])]

  [----
   (⊑ [(l_1 : S_1) ... ?] [?])]

  [(⊑ S_2 S_4)
   (⊑ [(l_1 : S_1) ... (l_3 : S_3) ... ?]
      [(l_5 : S_5) ... ?])
   ------------------------------------------------
   (⊑ [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ?]
      [(l_2 : S_4) (l_5 : S_5) ... ?])]
  
  [-----
   (⊑ [(l_1 : S_1) ... ·] [?])]

  [(⊑ S_2 S_4)
   (⊑ [(l_1 : S_1) ... (l_3 : S_3) ... ·]
      [(l_5 : S_5) ... ?])
   ------------------------------------------------
   (⊑ [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ·]
      [(l_2 : S_4) (l_5 : S_5) ... ?])]
  
  )

(define-metafunction GTFLcsub
  ; Consistent Subtype Join
  ~⊔ : S S -> S ;partial
  [(~⊔ ? ?) ?]
  [(~⊔ Int Int) Int]
  [(~⊔ Int ?) Int]
  [(~⊔ ? Int) Int]
  
  [(~⊔ Bool Bool) Bool]
  [(~⊔ Bool ?) Bool]
  [(~⊔ ? Bool) Bool]

  [(~⊔ (S_11 → S_12) (S_21 → S_22))
   ((~⊓ S_11 S_21) → (~⊔ S_12 S_22))]
  [(~⊔ (S_11 → S_12) ?)
   ((~⊓ S_11 ?) → (~⊔ S_12 ?))]
  [(~⊔ ? (S_21 → S_22))
   ((~⊓ ? S_21) → (~⊔ ? S_22))]

  ; Dealing with ? and rows and records.
  [(~⊔ [(l_ : S_) ... ·] ?)
   (~⊔ [(l_ : S_) ... ·] [?])]
  [(~⊔ [(l_ : S_) ... ?] ?)
   (~⊔ [(l_ : S_) ... ?] [?])]
  [(~⊔ ?   [(l_ : S_) ... ·])
   (~⊔ [?] [(l_ : S_) ... ·])]
  [(~⊔ ?   [(l_ : S_) ... ?])
   (~⊔ [?] [(l_ : S_) ... ?])]

  ; Now dealing with record record.
  [(~⊔ [·] [(l : S) ... ·]) [·]]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ·]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ·])
   [(l_1 : (~⊔ S_1 S_4)) (l_6 : S_6) ... ·]
   (where [(l_6 : S_6) ... ·] (~⊔ [(l_2 : S_2) ... ·]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ·]))]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ·]
       [(l_3 : S_3) ... ·])
   (~⊔ [(l_2 : S_2) ... ·]
       [(l_3 : S_3) ... ·])
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]

  ; Now dealing with Row Record
  [(~⊔ [?] [(l : S) ... ·]) [·]]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ·])
   [(l_1 : (~⊔ S_1 S_4)) (l_6 : S_6) ... ·]
   (where [(l_6 : S_6) ... ·] (~⊔ [(l_2 : S_2) ... ·]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ·]))]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ·])
   (~⊔ [(l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ·])
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]

  ; Now dealing with Record Row by flipping.
  [(~⊔ [(l_1 : S_1) ... ·] [(l_2 : S_2) ... ?])
   (~⊔ [(l_1 : S_1) ... ?] [(l_2 : S_2) ... ·])]
   
  ; Now dealing with Row Row
  [(~⊔ [?] [(l_1 : S_1) ... ?]) [?]]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ?])
   [(l_1 : (~⊔ S_1 S_4)) (l_6 : S_6) ... ?]
   (where [(l_6 : S_6) ... ?] (~⊔ [(l_2 : S_2) ... ?]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ?]))]
  [(~⊔ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ?])
   (~⊔ [(l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ?])
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]
  )

(define-metafunction GTFLcsub
  ; Consistent Subtype Meet
  ~⊓ : S S -> S ;partial

  [(~⊓ ? ?) ?]
  [(~⊓ Int Int) Int]
  [(~⊓ Int ?) Int]
  [(~⊓ ? Int) Int]
  
  [(~⊓ Bool Bool) Bool]
  [(~⊓ Bool ?) Bool]
  [(~⊓ ? Bool) Bool]

  [(~⊓ (S_11 → S_12) (S_21 → S_22))
   ((~⊔ S_11 S_21) → (~⊓ S_12 S_22))]
  [(~⊓ (S_11 → S_12) ?)
   ((~⊔ S_11 ?) → (~⊓ S_12 ?))]
  [(~⊓ ? (S_21 → S_22))
   ((~⊔ ? S_21) → (~⊓ ? S_22))]

  ; Dealing with ? and rows and records.
  [(~⊓ [(l_ : S_) ... ·] ?)
   (~⊓ [(l_ : S_) ... ·] [?])]
  [(~⊓ [(l_ : S_) ... ?] ?)
   (~⊓ [(l_ : S_) ... ?] [?])]
  [(~⊓ ?   [(l_ : S_) ... ·])
   (~⊓ [?] [(l_ : S_) ... ·])]
  [(~⊓ ?   [(l_ : S_) ... ?])
   (~⊓ [?] [(l_ : S_) ... ?])]


  ; Now dealing with record record.
  [(~⊓ [·] [(l : S) ... ·]) [(l : S) ... ·]]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ·]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ·])
   [(l_1 : (~⊓ S_1 S_4)) (l_6 : S_6) ... ·]
   (where [(l_6 : S_6) ... ·] (~⊓ [(l_2 : S_2) ... ·]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ·]))]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ·]
       [(l_3 : S_3) ... ·])
   [(l_1 : S_1) (l_6 : S_6) ... ·]
   (where [(l_6 : S_6) ... ·] (~⊓ [(l_2 : S_2) ... ·]
                                  [(l_3 : S_3) ... ·]))
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]

  ; Now dealing with Row Record
  [(~⊓ [?] [(l_1 : S_1) ... ·])
   [(l_1 : (~⊓ S_1 ?)) ... ?]]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ·])
   [(l_1 : (~⊓ S_1 S_4)) (l_6 : S_6) ... ?]
   (where [(l_6 : S_6) ... ?] (~⊓ [(l_2 : S_2) ... ?]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ·]))]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ·])
   [(l_1 : S_1) (l_6 : S_6) ... ?]
   (where [(l_6 : S_6) ... ?] (~⊓ [(l_2 : S_2) ... ?]
                                  [(l_3 : S_3) ... ·]))
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]

  ; Now dealing with Record Row by flipping.
  [(~⊓ [(l_1 : S_1) ... ·] [(l_2 : S_2) ... ?])
   (~⊓ [(l_1 : S_1) ... ?] [(l_2 : S_2) ... ·])]
   
  ; Now dealing with Row Row
  [(~⊓ [?] [(l_1 : S_1) ... ?])
   [(l_1 : (~⊓ S_1 ?)) ... ?]]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... (l_1 : S_4) (l_5 : S_5) ... ?])
   [(l_1 : (~⊓ S_1 S_4)) (l_6 : S_6) ... ?]
   (where [(l_6 : S_6) ... ?] (~⊓ [(l_2 : S_2) ... ?]
                                  [(l_3 : S_3) ... (l_5 : S_5) ... ?]))]
  [(~⊓ [(l_1 : S_1) (l_2 : S_2) ... ?]
       [(l_3 : S_3) ... ?])
   [(l_1 : (~⊓ S_1 ?)) (l_6 : S_6) ... ?]
   (where [(l_6 : S_6) ... ?] (~⊓ [(l_2 : S_2) ... ?]
                                  [(l_3 : S_3) ... ?]))
   (side-condition (not (member (term l_1) (term (l_3 ...)))))]
  
  )

(define-judgment-form GTFLcsub
  ; Gradual Typing
  #:mode (GT I I O)
  #:contract (GT Γ t S)
  [(∈ x S Γ)
   --------- "Sx"
   (GT Γ x S)]

  [----------------- "Sn"
   (GT Γ number Int)]

  [------------------ "Sb"
   (GT Γ boolean Bool)]

  [(GT Γ t_1 S_1)
   (GT Γ t_2 S_2)
   (~dom S_1 S_3)
   (~cod S_1 S_4)
   (≲ S_2 S_3)
   ----------------------- "Sapp"
   (GT Γ (t_1 t_2) S_4)]

  [(GT Γ t_1 S_1)
   (GT Γ t_2 S_2)
   (≲ S_1 Int)
   (≲ S_2 Int)
   ---------------------- "S+"
   (GT Γ (t_1 + t_2) Int)]

  [(GT Γ t_1 S_1)
   (GT Γ t_2 S_2)
   (GT Γ t_3 S_3)
   (≲ S_1 Bool)
   ------------------- "Sif"
   (GT Γ (if t_1 then t_2 else t_3) (~⊔ S_2 S_3))]

  [(GT Γ t S)
   (~proj S l S_1)
   --------------------------- "Sproj"
   (GT Γ (t \. l) S_1)]

  [(GT [(x ↦ S_1) Γ] t S_2)
   ---------------------------------- "Sλ"
   (GT Γ (λ (x : S_1) t) (S_1 → S_2))]

  [(GT Γ t S)
   (≲ S S_1)
   --------------------- "S::"
   (GT Γ (t :: S_1) S_1)]

  [(GT Γ t_ S_)
   ...
   ------------------------------------- "Srec"
   (GT Γ [(l_ = t_) ...] [(l_ : S_) ... ·])]
  )

(test-judgment-holds (GT · ((λ (x : Int) x) 3) Int))
(test-judgment-holds (GT ·
                         [("l1" = 2) ("l2" = #f)]
                         [("l1" : Int) ("l2" : Bool) ·]))


; Now we can proceed to implement the runtime language.

(define-judgment-form Types
  #:mode (wf I I)
  #:contract (wf S S)
  [------------
   (wf Int Int)]
  [-------------
   (wf Bool Bool)]

  [-------
   (wf ? ?)]

  [(wf S_21 S_11)
   (wf S_12 S_22)
   --------------
   (wf (S_11 → S_12) (S_21 → S_22))]

  [-----
   (wf [(l_1 : S_1) ... ·] [·])]

  [(wf S_2 S_4)
   (wf [(l_1 : S_1) ... (l_3 : S_3) ... ·]
       [(l_5 : S_5) ... ·])
   -----
   (wf [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ·]
       [(l_2 : S_4) (l_5 : S_5) ... ·])]

  [-----
   (wf [(l_1 : S_1) ... ?] [·])]

  [(wf S_2 S_4)
   (wf [(l_1 : S_1) ... (l_3 : S_3) ... ?]
       [(l_5 : S_5) ... ·])
   -----
   (wf [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ?]
       [(l_2 : S_4) (l_5 : S_5) ... ·])]

  [-----
   (wf [(l_0 : S_0) (l_1 : S_1) ... ·] [?])]

  [(wf S_2 S_4)
   (wf [(l_1 : S_1) ... (l_3 : S_3) ... ·]
       [(l_5 : S_5) ... ?])
   -----
   (wf [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ·]
       [(l_2 : S_4) (l_5 : S_5) ... ?])]

  [-----
   (wf [(l_1 : S_1) ... ?] [?])]

  [(wf S_2 S_4)
   (wf [(l_1 : S_1) ... (l_3 : S_3) ... ?]
       [(l_5 : S_5) ... ?])
   -----
   (wf [(l_1 : S_1) ... (l_2 : S_2) (l_3 : S_3) ... ?]
       [(l_2 : S_4) (l_5 : S_5) ... ?])]

  
  )
  
(define-extended-language RL GTFLcsub
  [ε ::= ; Evidence Objects
     (side-condition {S_1 S_2}
                     (judgment-holds (wf S_1 S_2)))]

  [e ::= ; Runtime Terms
     number
     boolean
     x
     (λ (x) e)
     ((ε e) (ε e))
     ((ε e) + (ε e))
     (if (ε e) then (ε e) else (ε e))
     (side-condition [(l_ = e_) ...]
                     (unique? (term (l_ ...))))
     ((ε e) \. l)
     (ε e)]

  [u ::= ; Raw Values
     number
     boolean
     x
     (λ (x) e)
     (side-condition [(l_ = v_) ...]
                     (unique? (term (l_ ...))))]

  [v ::= ; Values
     u
     (ε u)]

  [E ::= ; Evaluation Contexts
     hole
     (ε E)
     [(l_1 = v_1) ... (l_2 = E) (l_3 = e_3) ...]
     (E + (ε e))
     ((ε u) + E)
     (E (ε e))
     ((ε u) E)
     (E \. l)
     (if E then (ε e) else (ε e))]

  [r ::=
     e
     error]
  )              

(define-judgment-form RL
  #:mode (idom I O)
  #:contract (idom ε ε)
  [(~dom S_2 S_3)
   (~dom S_1 S_4)
   -------------------------
   (idom {S_1 S_2} {S_3 S_4})])

(define-judgment-form RL
  #:mode (icod I O)
  #:contract (icod ε ε)
  [(~cod S_1 S_3)
   (~cod S_2 S_4)
   -------------------------
   (icod {S_1 S_2} {S_3 S_4})])

(define-judgment-form RL
  #:mode (iproj I I O)
  #:contract (iproj ε l ε)
  [(~proj S_1 l S_3)
   (~proj S_2 l S_4)
   -------------------------
   (iproj {S_1 S_2} l {S_3 S_4})])


(define (domain-union . args)
  (remove-duplicates (apply append args)))

; Of course these methods are terribly slow,
; but they'll do the trick until refactored.
(define (dom-eq? x y)
  (equal? (first x) (first y)))

(define (collect-over-dom dom l1 l2 l3 l4)
  (let ([l1 (map rest (filter (λ (x) (member x dom dom-eq?)) l1))]
        [l2 (map rest (filter (λ (x) (member x dom dom-eq?)) l2))]
        [l3 (map rest (filter (λ (x) (member x dom dom-eq?)) l3))]
        [l4 (map rest (filter (λ (x) (member x dom dom-eq?)) l4))])
    (map cons
         (map first dom)
         (map append l1 l2 l3 l4))))

(define (in-1234 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (member x l2 dom-eq?)
                                 (member x l3 dom-eq?)
                                 (member x l4 dom-eq?))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))
           
(define (in-123 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (member x l2 dom-eq?)
                                 (member x l3 dom-eq?)
                                 (not (member x l4 dom-eq?)))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))         
    
(define (in-12 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (member x l2 dom-eq?)
                                 (not (member x l3 dom-eq?))
                                 (not (member x l4 dom-eq?)))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (in-1 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (not (member x l2 dom-eq?))
                                 (not (member x l3 dom-eq?))
                                 (not (member x l4 dom-eq?)))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (in-13 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (not (member x l2 dom-eq?))
                                 (member x l3 dom-eq?)
                                 (member x l4 dom-eq?))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (in-134 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (not (member x l2 dom-eq?))
                                 (member x l3 dom-eq?)
                                 (member x l4 dom-eq?))) l1)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (in-3 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (not (member x l2 dom-eq?))
                                 (not (member x l1 dom-eq?))
                                 (not (member x l4 dom-eq?)))) l3)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (in-34 l1 l2 l3 l4)
  (let ([dom (filter (λ (x) (and (not (member x l2 dom-eq?))
                                 (not (member x l1 dom-eq?))
                                 (member x l4 dom-eq?))) l3)])
    (collect-over-dom dom l1 l2 l3 l4)))

(define (organize-mappings l1 l2 l3 l4)
  (let ([l1 (sort l1 string<? #:key first)]
        [l2 (sort l2 string<? #:key first)]
        [l3 (sort l3 string<? #:key first)]
        [l4 (sort l4 string<? #:key first)])
    (if (not (empty? (append (filter (λ (x) (not (member x l1 dom-eq?))) l2)
                             (filter (λ (x) (not (member x l3 dom-eq?))) l4))))
        #f
        (map (λ (f) (f l1 l2 l3 l4))
             ; DO NOT CHANGE ORDER HERE
             ; unless you want to reorder EVERY rule definition on \;
             in-1
             in-12
             in-123
             in-1234
             in-13
             in-134
             in-3
             in-34))))

; Personally, I'd prefer to use a metafunction instead of a judgment-form for
; composition, but metafunctions trigger runtime errors when they are not
; totally defined and there's no way to actually check whether the function is
; undefined for an argument, unlike the case for define-judgment-form.

; There might be lots of reshuffling as things are sorted and reordered, but the goal
; here is not efficiency, but instead fidelity to the original rules.

(define-judgment-form RL
  #:mode (⊕JNRK I I I I)
  #:contract (⊕JNRK (l ...) ;J
                    (l ...) ;N
                    (l ...) ;R
                    (l ...) ;K
                    )

  ;K empty, then J+N+R must be +. We do all permutations.
  [---
   (⊕JNRK (l_j1 l_j2  ...)
          (l_n ...)
          (l_r ...)
          ())]

  [---
   (⊕JNRK (l_j  ...)
          (l_n1 l_n2 ...)
          (l_r ...)
          ())]

  [---
   (⊕JNRK (l_j ...)
          (l_n ...)
          (l_r1 l_r2 ...)
          ())]
   
  [----
   ; if K is +, then it doesn't matter whether JNR are empty or not.
   (⊕JNRK (l_j ...)
          (l_n ...)
          (l_r ...)
          (l_1 l_2 ...))]
)

(define-judgment-form RL
  #:mode (\; I I O)
  ; We do not check the contract because the ellipses in records will attempt to form
  ; malformed evidence, and then instead of failing the case the whole judgment fails.
  ; We will have to add side-condition checking first that evidences are well-formed,
  ; Or find a better pattern approach.
  ;#:contract (\; ε ε ε)

  ; We follow now exactly the rules in the paper.

  ; Fig. 11 : Consistent Transitivity: Part 1
  [-----------------------
   (\; {? ?} {? ?} {? ?})]

  [-----------------------
   (\; {? ?} {B B} {B B})]

  [-----------------------
   (\; {B B} {? ?} {B B})]
  
  [(\; {(S_11 → S_12) (S_21 → S_22)} {(? → ?) (? → ?)} ε)
   -----
   (\; {(S_11 → S_12) (S_21 → S_22)} {? ?} ε)]

  [(\; {(? → ?) (? → ?)} {(S_11 → S_12) (S_21 → S_22)} ε)
   ----
   (\; {? ?} {(S_11 → S_12) (S_21 → S_22)} ε)]

  [(\; {[?] [?]} {[(l_i : S_i) ... *_1] [(l_j : S_j) ... *_2]} ε)
   ---
   (\; {? ?} {[(l_i : S_i) ... *_1] [(l_j : S_j) ... *_2]} ε)]

  [(\; {[(l_i : S_i) ... *_1] [(l_j : S_j) ... *_2]} {[?] [?]} ε)
   ---
   (\; {[(l_i : S_i) ... *_1] [(l_j : S_j) ... *_2]} {? ?} ε)]

  [----
   (\; {B B} {B B} {B B})]

  [(\; {S_41 S_31} {S_21 S_11} {S_61 S_51})
   (\; {S_12 S_22} {S_32 S_42} {S_52 S_62})
   --------
   (\; {(S_11 → S_12) (S_21 → S_22)}
       {(S_31 → S_32) (S_41 → S_42)}
       {(S_51 → S_52) (S_61 → S_62)})]

  [(where (() () ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () () ())
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
   -----
   (\; {[(l_1 : S_1) ... ·] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... *_3] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ... ·] [(l_i : S_i6) ... ·]})]

  [(where (() () ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () () ())
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
   -----
   (\; {[(l_1 : S_1) ... ?] [(l_2 : S_2) ... ?]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... ?]}
       {[(l_i : S_i5) ... ?] [(l_i : S_i6) ... ?]})]

   [(where (() () ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () () ())
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
   -----
   (\; {[(l_1 : S_1) ... ?] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... *_3] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ... ?] [(l_i : S_i6) ... ·]})]

   [(where (() () ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () () ())
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
   -----
   (\; {[(l_1 : S_1) ... ·] [(l_2 : S_2) ... ?]}
       {[(l_3 : S_3) ... *_3] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ... ·] [(l_i : S_i6) ... ?]})]

  [(where (() ((l_j1 : S_j11 S_j12) (l_j : S_j1 S_j2) ...) ; + restriction in rule made explicit.
              ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () () ())
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {[(l_i : S_i1) ... (l_j1 : S_j11) (l_j : S_j1) ... *_1]
        [(l_i : S_i2) ... (l_j1 : S_j12) (l_j : S_j2) ... *_2]}
       {[(l_i : S_i3) ... (l_j1 : ?) (l_j : ?) ... ?]
        [(l_i : S_i4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})
   ---------
   (\; {[(l_1 : S_1) ... *_1] [(l_2 : S_2) ... *_2]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})]

  [(where (() () ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () ()
              ((l_k1 S_k13 S_k14) (l_k S_k3 S_k4) ... )) ; Forcing + in rule
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {[(l_i : S_i1) ... (l_k1 : ?) (l_k : ?) ... ?] [(l_i : S_i2) ... (l_k1 : ?) (l_k : ?) ... ?]}
       {[(l_i : S_i3) ... (l_k1 : S_k13) (l_k : S_k3) ... *_3] [(l_i : S_i4) ... (l_k1 : S_k14) (l_k : S_k4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})
   -----
   (\; {[(l_1 : S_1) ... ?] [(l_2 : S_2) ... ?]}
       {[(l_3 : S_3) ... *_3] [(l_4 : S_4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})]

  [(where (() ((l_j1 : S_j11 S_j12) (l_j : S_j1 S_j2) ...) ; + restriction in rule made explicit.
              ()
              ((l_i S_i1 S_i2 S_i3 S_i4) ...)
              () () ()
              ((l_k1 S_k13 S_k14) (l_k S_k3 S_k4) ... )) ; Forcing + in rule
          (organize-mappings (term ((l_1 S_1) ...))
                             (term ((l_2 S_2) ...))
                             (term ((l_3 S_3) ...))
                             (term ((l_4 S_4) ...))))
   (\; {[(l_i : S_i1) ... (l_j1 : S_j11) (l_j : S_j1) ... (l_k1 : ?) (l_k : ?) ... ?]
        [(l_i : S_i2) ... (l_j1 : S_j12) (l_j : S_j2) ... (l_k1 : ?) (l_k : ?) ... ?]}
       {[(l_i : S_i3) ... (l_j1 : ?) (l_k1  : S_k13) (l_k : S_k3) ... (l_j : ?) ... ?]
        [(l_i : S_i4) ... (l_k1 : S_k14) (l_k : S_k4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})
   ---------
   (\; {[(l_1 : S_1) ... ?] [(l_2 : S_2) ... ?]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})]

  ; Fig. 12 : Consistent Transivity : Part 2.

   [(where (((l_k S_k) ...)
            ()
            ((l_j S_j1 S_j2 S_j3) ...)
            ((l_i S_i1 S_i2 S_i3 S_i4) ...)
            () () ()
            ()) ; Forcing + in rule
           (organize-mappings (term ((l_1 S_1) ...))
                              (term ((l_2 S_2) ...))
                              (term ((l_3 S_3) ...))
                              (term ((l_4 S_4) ...))))
    (⊕JNRK (l_j ...) () () (l_k ...))
    (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
    (\; {S_j1 S_j2} {S_j3 S_j3} {S_j5 S_j6}) ...
   ---------
   (\; {[(l_1 : S_1) ... *_1] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... ·] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ... (l_j : S_j5) ... (l_k : S_k) ... *_1]
        [(l_i : S_i6) ... *_4]})]

  [(where (((l_k S_k) ...)
            ((l_q S_q1 S_q2) ...)
            ((l_j S_j1 S_j2 S_j3) ...)
            ((l_i S_i1 S_i2 S_i3 S_i4) ...)
            () () ()
            ()) ; Forcing + in rule
           (organize-mappings (term ((l_1 S_1) ...))
                              (term ((l_2 S_2) ...))
                              (term ((l_3 S_3) ...))
                              (term ((l_4 S_4) ...))))
    (⊕JNRK (l_j ...) () () (l_k ...))
    (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
    (\; {S_j1 S_j2} {S_j3 S_j3} {S_j5 S_j6}) ...
   ---------
   (\; {[(l_1 : S_1) ... *_1] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ... (l_j : S_j5) ... (l_q : S_q1) ... (l_k : S_k) ... *_1]
        [(l_i : S_i6) ... *_4]})]

  ; Rule 3 in the figure must be split in two, because of the last side condition
  ; *_1 = ? if {l_p, l_r^{⊕r}} ≠ ∅

   [(where (((l_k S_k) ...)
            () ; Curously, no q's on this rule.
            ((l_j S_j1 S_j2 S_j3) ...)
            ((l_i S_i1 S_i2 S_i3 S_i4) ...)
            ((l_n S_n1 S_n3) ...)
            ((l_m S_m1 S_m3 S_m4) ...)
            ((l_r S_r3) ...)
            ((l_p S_p3 S_p4) ...)) 
           (organize-mappings (term ((l_1 S_1) ...))
                              (term ((l_2 S_2) ...))
                              (term ((l_3 S_3) ...))
                              (term ((l_4 S_4) ...))))
    (⊕JNRK (l_j ...) (l_n ...) (l_r ...) (l_k ...))
    (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
    (\; {S_j1 S_j2} {S_j3 S_j3} {S_j5 S_j6}) ...
    (\; {S_m1 ?} {S_m3 S_m4} {S_m5 S_m6}) ...
    (\; {S_n1 ?} {S_n3 S_n3} {S_n5 S_n6}) ...
    (\; {? ?} {S_p3 S_p4} {S_p5 S_p6}) ...
    (\; {? ?} {S_r3 S_r3} {S_r5 S_r6}) ...
    ; side condition:
    (where (l_match l_plus ...)
     (term (l_p ... l_r ...)))
   ---------
   (\; {[(l_1 : S_1) ... ?] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ...
         (l_m : S_m5) ...
         (l_p : S_p5) ...
         (l_j : S_j5) ...
         (l_n : S_n5) ...
         (l_r : S_r5) ...
         (l_k : S_k) ... ?]
        [(l_i : S_i6) ...
         (l_m : S_m6) ...
         (l_p : S_p6) ... *_4]})]


   [(where (((l_k S_k) ...)
            () ; Curiously, no q's on this rule.
            ((l_j S_j1 S_j2 S_j3) ...)
            ((l_i S_i1 S_i2 S_i3 S_i4) ...)
            ((l_n S_n1 S_n3) ...)
            ((l_m S_m1 S_m3 S_m4) ...)
            ; p's and r's are empty
            ()
            ()) 
           (organize-mappings (term ((l_1 S_1) ...))
                              (term ((l_2 S_2) ...))
                              (term ((l_3 S_3) ...))
                              (term ((l_4 S_4) ...))))
    (⊕JNRK (l_j ...) (l_n ...) () (l_k ...))
    (\; {S_i1 S_i2} {S_i3 S_i4} {S_i5 S_i6}) ...
    (\; {S_j1 S_j2} {S_j3 S_j3} {S_j5 S_j6}) ...
    (\; {S_m1 ?} {S_m3 S_m4} {S_m5 S_m6}) ...
    (\; {S_n1 ?} {S_n3 S_n3} {S_n5 S_n6}) ...
   ---------
   (\; {[(l_1 : S_1) ... *_1] [(l_2 : S_2) ... ·]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_i : S_i5) ...
         (l_m : S_m5) ...
         (l_j : S_j5) ...
         (l_n : S_n5) ...
         (l_k : S_k) ... *_1]
        [(l_i : S_i6) ...
         (l_m : S_m6) ... *_4]})]

  ; And the very last rule, which only does domain propagation:
  [(where (((l_k S_k) ...)
            ((l_q1 S_q11 S_q12) (l_q S_q1 S_q2) ...)
            ((l_j S_j1 S_j2 S_j3) ...)
            ((l_i S_i1 S_i2 S_i3 S_i4) ...)
            ((l_n S_n1 S_n3) ...)
            ((l_m S_m1 S_m3 S_m4) ...)
            ((l_r S_r3) ...)
            ((l_p S_p3 S_p4) ...)) 
           (organize-mappings (term ((l_1 S_1) ...))
                              (term ((l_2 S_2) ...))
                              (term ((l_3 S_3) ...))
                              (term ((l_4 S_4) ...))))
    (⊕JNRK (l_j ...) (l_n ...) (l_r ...) (l_k ...))

    (\; {[(l_i : S_i1) ...
          (l_m : S_m1) ...
          (l_j : S_j1) ...
          (l_n : S_n1) ...
          (l_q1 : S_q11) (l_q : S_q1) ...
          (l_k : S_k) ...
          *_1]
         [(l_i : S_i2) ...
          (l_j : S_j2) ...
          (l_q1 : S_q12) (l_q : S_q2) ...
          ?]}
        {[(l_i : S_i3) ...
          (l_m : S_m3) ...
          (l_p : S_p3) ...
          (l_j : S_j3) ...
          (l_n : S_n3) ...
          (l_r : S_r3) ...
          (l_q1 : ?) (l_q : ?) ...
          ?]
         [(l_i : S_i4) ...
          (l_m : S_m4) ...
          (l_p : S_p4) ...
          *_4]}
        {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})
    
   ---------
   (\; {[(l_1 : S_1) ... *_1] [(l_2 : S_2) ... ?]}
       {[(l_3 : S_3) ... ?] [(l_4 : S_4) ... *_4]}
       {[(l_5 : S_5) ... *_5] [(l_6 : S_6) ... *_6]})]

)

(define
  ⟶
  (reduction-relation
   RL
   #:domain e
   #:codomain r
   
   [--> (in-hole E ((ε_1 number_1) + (ε_2 number_2)))
        (in-hole E number_3)
        "+"
        (where number_3 ,(+ (term number_1) (term number_2)))]

   [--> (in-hole E (if (ε_1 #t) then (ε_2 e_2) else (ε_3 e_3)))        
        (in-hole E (ε_2 e_2))
        "if#t"]

   [--> (in-hole E (if (ε_1 #f) then (ε_2 e_2) else (ε_3 e_3)))
        (in-hole E (ε_3 e_3))
        "if#f"]

   [--> (in-hole E ((ε [(l_i = v_i) ...]) \. l_j))
        error
        "proj-label-missing"
        (side-condition (not (member (term l_j) (term (l_i ...)))))]

   [--> (in-hole E ((ε_j [(l_i = v_i) ...]) \. l_j))
        error
        "proj-ev-malformed"
        (side-condition (not (judgment-holds (iproj ε_j l_j ε))))]
   
   [--> (in-hole E ((ε [(l_i = v_i) ... (l_j = v_j) (l_k = v_k) ...]) \. l_j))
        (ε_j v_j)
        "proj-ok"
        (judgment-holds (iproj ε l_j ε_j))]
   
   [--> (in-hole E ((ε_1 (λ (x) e)) (ε_2 u)))
        error
        "app-ev-malformed"
        (side-condition (not (or (judgment-holds (idom ε_1 ε))
                                 (judgment-holds (icod ε_1 ε)))))]
   
   [--> (in-hole E ((ε_1 (λ (x) e)) (ε_2 u)))
        error
        "app-;-undefined"
        (judgment-holds (idom ε_1 ε_d))
        (side-condition (not (judgment-holds (\; ε_2 ε_d ε))))]

   [--> (in-hole E ((ε_1(λ (x) e)) (ε_2 u)))
        (in-hole E (ε_c (substitute e x (ε_3 u))))
        "app-β"
        (judgment-holds (idom ε_1 ε_d))
        (judgment-holds (icod ε_1 ε_c))
        (judgment-holds (\; ε_2 ε_d ε_3))]

   [--> (in-hole E (ε_1 (ε_2 u)))
        (in-hole E (ε_3 u))
        "coercion-ok"
        (judgment-holds (\; ε_2 ε_1 ε_3))]

   [--> (in-hole E (ε_1 (ε_2 u)))
        error
        "coercion-fail"
        (side-condition (empty? (judgment-holds (\; ε_2 ε_1 ε_3) ε_3)))]
   ))

; The example on the paper that breaks internally.
; Though it intuitively "should" produce an error, this program
; can't because of gradual rows.  The definition of '\;' is complete
; enough to show this fact.

(apply-reduction-relation* ⟶
                           (term (({([("m" : Int) ·] → [("n" : Bool) ?])
                                    ([("m" : Int) ·] → [("n" : Bool) ?])}
                                   (λ (x) ({[("n" : Bool) ?] [("n" : Bool) ?]}
                                           ({[("m" : Int) ·] [?]} x))))
                                  ({[("m" : Int) ("n" : Bool) ·]
                                    [("m" : Int) ·]}
                                   [("m" = 1) ("n" = #t)]))))
(test-results)