Set Bullet Behavior "Strict Subproofs".

Require Import PoplLibraries.Math.
Require Import PoplLibraries.Recursion.
Require Import FunctionalExtensionality.

Module Type mut_fix_template.
  Parameter A : Type.
  Parameter B : Type.

  Parameter size_A : A -> nat.
  Parameter size_B : B -> nat.

  Parameter P_A : A -> Type.
  Parameter P_B : B -> Type.

  Parameter F_A : forall (x : A) (rec_call_A : (forall y : A, lt (size_A y) (size_A x) -> P_A y)) (rec_call_B : (forall y : B, lt (size_B y) (size_A x) -> P_B y)) , P_A x.
  Parameter F_B : forall (x : B) (rec_call_A : (forall y : A, lt (size_A y) (size_B x) -> P_A y)) (rec_call_B : (forall y : B, lt (size_B y) (size_B x) -> P_B y)) , P_B x.
End mut_fix_template.

Module Wf_mut_fix (args : mut_fix_template).
  Import args.

  Fixpoint Fix_F_A (x : A) (a : Acc lt (size_A x)) {struct a}: P_A x := 
    F_A x
        (fun (y : A) (H : lt (size_A y) (size_A x)) => Fix_F_A y (Acc_inv a H))
        (fun (y : B) (H : lt (size_B y) (size_A x)) => Fix_F_B y (Acc_inv a H))
  with Fix_F_B (x : B) (b : Acc lt (size_B x)) {struct b} : P_B x := 
         F_B x
             (fun (y : A) (H : lt (size_A y) (size_B x)) => Fix_F_A y (Acc_inv b H))
             (fun (y : B) (H : lt (size_B y) (size_B x)) => Fix_F_B y (Acc_inv b H)).
  
  Lemma Fix_F_A_eq (x : A) (a : Acc lt (size_A x)):
    F_A x
        (fun (y : A) (H : lt (size_A y) (size_A x)) => Fix_F_A y (Acc_inv a H))
        (fun (y : B) (H : lt (size_B y) (size_A x)) => Fix_F_B y (Acc_inv a H))
    = Fix_F_A x a.
  Proof.
    destruct a.
    reflexivity.
  Qed.
  
  Lemma Fix_F_B_eq (x : B) (b : Acc lt (size_B x)):
    F_B x
        (fun (y : A) (H : lt (size_A y) (size_B x)) => Fix_F_A y (Acc_inv b H))
        (fun (y : B) (H : lt (size_B y) (size_B x)) => Fix_F_B y (Acc_inv b H))
    = Fix_F_B x b.
  Proof.
    destruct b.
    reflexivity.
  Qed.
  
  Definition Fix_A (x : A) := Fix_F_A x (lt_wf (size_A x)).
  Definition Fix_B (x : B) := Fix_F_B x (lt_wf (size_B x)).

  Lemma Fix_F_A_inv : forall (x : A) (r s : Acc lt (size_A x)),
      Fix_F_A x r = Fix_F_A x s
  with Fix_F_B_inv : forall (x : B) (r s : Acc lt (size_B x)),
      Fix_F_B x r = Fix_F_B x s.
  Proof.
    - intros.
      destruct r.
      destruct s.
      simpl.
      f_equal.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_A_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_B_inv.
    - intros.
      destruct r.
      destruct s.
      simpl.
      f_equal.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_A_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_B_inv.
  Qed.        
      
  Lemma Fix_A_eq (x : A) :
    Fix_A x = F_A x (fun (y : A) (a : lt (size_A y) (size_A x)) => Fix_A y) (fun (y : B) (a : lt (size_B y) (size_A x)) => Fix_B y).
  Proof.
    unfold Fix_A.
    rewrite <- Fix_F_A_eq.
    f_equal.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_A_inv.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_B_inv.    
  Qed.

  Lemma Fix_B_eq (x : B) :
    Fix_B x = F_B x (fun (y : A) (a : lt (size_A y) (size_B x)) => Fix_A y) (fun (y : B) (a : lt (size_B y) (size_B x)) => Fix_B y).
  Proof.
    unfold Fix_B.
    rewrite <- Fix_F_B_eq.
    f_equal.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_A_inv.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_B_inv.    
  Qed.

End Wf_mut_fix.

Module Type four_double_template.
  Parameter A1 : Type.
  Parameter A2 : Type.
  Parameter B1 : Type.
  Parameter B2 : Type.
  Parameter C1 : Type.
  Parameter C2 : Type.
  Parameter D1 : Type.
  Parameter D2 : Type.

  Parameter size_A : A1 -> A2 -> nat.
  Parameter size_B : B1 -> B2 -> nat.
  Parameter size_C : C1 -> C2 -> nat.
  Parameter size_D : D1 -> D2 -> nat.

  Parameter P_A : A1 -> A2 -> Type.
  Parameter P_B : B1 -> B2 -> Type.
  Parameter P_C : C1 -> C2 -> Type.
  Parameter P_D : D1 -> D2 -> Type.

  Parameter F_A : forall (x : A1) (x' : A2)
                         (rec_call_A : (forall (y : A1) (y' : A2), lt (size_A y y') (size_A x x') -> P_A y y'))
                         (rec_call_B : (forall (y : B1) (y' : B2), lt (size_B y y') (size_A x x') -> P_B y y'))
                         (rec_call_C : (forall (y : C1) (y' : C2), lt (size_C y y') (size_A x x') -> P_C y y'))
                         (rec_call_D : (forall (y : D1) (y' : D2), lt (size_D y y') (size_A x x') -> P_D y y'))
    , P_A x x'.
  Parameter F_B : forall (x : B1) (x' : B2)
                         (rec_call_A : (forall (y : A1) (y' : A2), lt (size_A y y') (size_B x x') -> P_A y y'))
                         (rec_call_B : (forall (y : B1) (y' : B2), lt (size_B y y') (size_B x x') -> P_B y y'))
                         (rec_call_C : (forall (y : C1) (y' : C2), lt (size_C y y') (size_B x x') -> P_C y y'))
                         (rec_call_D : (forall (y : D1) (y' : D2), lt (size_D y y') (size_B x x') -> P_D y y'))
    , P_B x x'.
  Parameter F_C : forall (x : C1) (x' : C2)
                         (rec_call_A : (forall (y : A1) (y' : A2), lt (size_A y y') (size_C x x') -> P_A y y'))
                         (rec_call_B : (forall (y : B1) (y' : B2), lt (size_B y y') (size_C x x') -> P_B y y'))
                         (rec_call_C : (forall (y : C1) (y' : C2), lt (size_C y y') (size_C x x') -> P_C y y'))
                         (rec_call_D : (forall (y : D1) (y' : D2), lt (size_D y y') (size_C x x') -> P_D y y'))
    , P_C x x'.
  Parameter F_D : forall (x : D1) (x' : D2)
                         (rec_call_A : (forall (y : A1) (y' : A2), lt (size_A y y') (size_D x x') -> P_A y y'))
                         (rec_call_B : (forall (y : B1) (y' : B2), lt (size_B y y') (size_D x x') -> P_B y y'))
                         (rec_call_C : (forall (y : C1) (y' : C2), lt (size_C y y') (size_D x x') -> P_C y y'))
                         (rec_call_D : (forall (y : D1) (y' : D2), lt (size_D y y') (size_D x x') -> P_D y y'))
    , P_D x x'.

End four_double_template.

Module four_double_fix (args : four_double_template).
  Import args.
  
  Fixpoint Fix_F_A (x : A1) (x': A2) (a : Acc lt (size_A x x')) {struct a}: P_A x x' := 
    F_A x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_A x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_A x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_A x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_A x x')) => Fix_F_D y y' (Acc_inv a H))
  with Fix_F_B (x : B1) (x': B2) (a : Acc lt (size_B x x')) {struct a}: P_B x x' := 
    F_B x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_B x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_B x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_B x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_B x x')) => Fix_F_D y y' (Acc_inv a H))
  with Fix_F_C (x : C1) (x': C2) (a : Acc lt (size_C x x')) {struct a}: P_C x x' := 
    F_C x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_C x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_C x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_C x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_C x x')) => Fix_F_D y y' (Acc_inv a H))
  with Fix_F_D (x : D1) (x': D2) (a : Acc lt (size_D x x')) {struct a}: P_D x x' := 
    F_D x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_D x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_D x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_D x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_D x x')) => Fix_F_D y y' (Acc_inv a H)).

  Lemma Fix_F_A_eq (x : A1) (x' : A2 )(a : Acc lt (size_A x x')) :
    F_A x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_A x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_A x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_A x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_A x x')) => Fix_F_D y y' (Acc_inv a H))
    = Fix_F_A x x' a.
  Proof.
    destruct a.
    reflexivity.
  Qed.

  Lemma Fix_F_B_eq (x : B1) (x' : B2 )(a : Acc lt (size_B x x')) :
    F_B x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_B x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_B x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_B x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_B x x')) => Fix_F_D y y' (Acc_inv a H))
    = Fix_F_B x x' a.
  Proof.
    destruct a.
    reflexivity.
  Qed.
  
  Lemma Fix_F_C_eq (x : C1) (x' : C2)(a : Acc lt (size_C x x')) :
    F_C x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_C x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_C x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_C x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_C x x')) => Fix_F_D y y' (Acc_inv a H))
    = Fix_F_C x x' a.
  Proof.
    destruct a.
    reflexivity.
  Qed.

  Lemma Fix_F_D_eq (x : D1) (x' : D2 )(a : Acc lt (size_D x x')) :
    F_D x x'
        (fun (y : A1) (y' : A2) (H : lt (size_A y y') (size_D x x')) => Fix_F_A y y' (Acc_inv a H))
        (fun (y : B1) (y' : B2) (H : lt (size_B y y') (size_D x x')) => Fix_F_B y y' (Acc_inv a H))
        (fun (y : C1) (y' : C2) (H : lt (size_C y y') (size_D x x')) => Fix_F_C y y' (Acc_inv a H))
        (fun (y : D1) (y' : D2) (H : lt (size_D y y') (size_D x x')) => Fix_F_D y y' (Acc_inv a H))
    = Fix_F_D x x' a.
  Proof.
    destruct a.
    reflexivity.
  Qed.

  Definition Fix_A (x : A1) (x' : A2) := Fix_F_A x x' (lt_wf (size_A x x')).
  Definition Fix_B (x : B1) (x' : B2) := Fix_F_B x x' (lt_wf (size_B x x')).
  Definition Fix_C (x : C1) (x' : C2) := Fix_F_C x x' (lt_wf (size_C x x')).
  Definition Fix_D (x : D1) (x' : D2) := Fix_F_D x x' (lt_wf (size_D x x')).

  Lemma Fix_F_A_inv : forall (x : A1) (x' : A2) (r s : Acc lt (size_A x x')),
      Fix_F_A x x' r = Fix_F_A x x' s
  with Fix_F_B_inv : forall (x : B1) (x' : B2) (r s : Acc lt (size_B x x')),
      Fix_F_B x x' r = Fix_F_B x x' s
  with Fix_F_C_inv : forall (x : C1) (x' : C2) (r s : Acc lt (size_C x x')),
      Fix_F_C x x' r = Fix_F_C x x' s
  with Fix_F_D_inv : forall (x : D1) (x' : D2) (r s : Acc lt (size_D x x')),
      Fix_F_D x x' r = Fix_F_D x x' s.
  Proof.
    all: intros.
    all: destruct r.
    all: destruct s.
    all: simpl.
    all: f_equal.
    all: do 3 (eapply functional_extensionality_dep ;intros).        
    all: first [eapply Fix_F_A_inv |
                eapply Fix_F_B_inv |
                eapply Fix_F_C_inv |
                eapply Fix_F_D_inv ].    
  Qed.        
      
  Lemma Fix_A_eq (x : A1) (x' : A2):
    Fix_A x x' = F_A x x' (fun (y : A1) (y' : A2) (a : lt (size_A y y') (size_A x x')) => Fix_A y y')
                     (fun (y : B1) (y' : B2) (a : lt (size_B y y') (size_A x x')) => Fix_B y y')
                     (fun (y : C1) (y' : C2) (a : lt (size_C y y') (size_A x x')) => Fix_C y y')
                     (fun (y : D1) (y' : D2) (a : lt (size_D y y') (size_A x x')) => Fix_D y y').
  Proof.
    unfold Fix_A.
    rewrite <- Fix_F_A_eq.
    f_equal.
    all: do 3 (eapply functional_extensionality_dep ;intros).        
    eapply Fix_F_A_inv.
    eapply Fix_F_B_inv.
    eapply Fix_F_C_inv.
    eapply Fix_F_D_inv.
  Qed.

  Lemma Fix_B_eq (x : B1) (x' : B2):
    Fix_B x x' = F_B x x' (fun (y : A1) (y' : A2) (a : lt (size_A y y') (size_B x x')) => Fix_A y y')
                     (fun (y : B1) (y' : B2) (a : lt (size_B y y') (size_B x x')) => Fix_B y y')
                     (fun (y : C1) (y' : C2) (a : lt (size_C y y') (size_B x x')) => Fix_C y y')
                     (fun (y : D1) (y' : D2) (a : lt (size_D y y') (size_B x x')) => Fix_D y y').
  Proof.
    unfold Fix_B.
    rewrite <- Fix_F_B_eq.
    f_equal.
    all: do 3 (eapply functional_extensionality_dep ;intros).        
    eapply Fix_F_A_inv.
    eapply Fix_F_B_inv.
    eapply Fix_F_C_inv.
    eapply Fix_F_D_inv.
  Qed.

  Lemma Fix_C_eq (x : C1) (x' : C2):
    Fix_C x x' = F_C x x' (fun (y : A1) (y' : A2) (a : lt (size_A y y') (size_C x x')) => Fix_A y y')
                     (fun (y : B1) (y' : B2) (a : lt (size_B y y') (size_C x x')) => Fix_B y y')
                     (fun (y : C1) (y' : C2) (a : lt (size_C y y') (size_C x x')) => Fix_C y y')
                     (fun (y : D1) (y' : D2) (a : lt (size_D y y') (size_C x x')) => Fix_D y y').
  Proof.
    unfold Fix_C.
    rewrite <- Fix_F_C_eq.
    f_equal.
    all: do 3 (eapply functional_extensionality_dep ;intros).        
    eapply Fix_F_A_inv.
    eapply Fix_F_B_inv.
    eapply Fix_F_C_inv.
    eapply Fix_F_D_inv.
  Qed.

    Lemma Fix_D_eq (x : D1) (x' : D2):
    Fix_D x x' = F_D x x' (fun (y : A1) (y' : A2) (a : lt (size_A y y') (size_D x x')) => Fix_A y y')
                     (fun (y : B1) (y' : B2) (a : lt (size_B y y') (size_D x x')) => Fix_B y y')
                     (fun (y : C1) (y' : C2) (a : lt (size_C y y') (size_D x x')) => Fix_C y y')
                     (fun (y : D1) (y' : D2) (a : lt (size_D y y') (size_D x x')) => Fix_D y y').
  Proof.
    unfold Fix_D.
    rewrite <- Fix_F_D_eq.
    f_equal.
    all: do 3 (eapply functional_extensionality_dep ;intros).        
    eapply Fix_F_A_inv.
    eapply Fix_F_B_inv.
    eapply Fix_F_C_inv.
    eapply Fix_F_D_inv.
  Qed.
  
  
End four_double_fix.



(* Following John Wiegleys' suggestion on Joey's SO question
   https://stackoverflow.com/questions/42302300/which-vector-library-to-use-in-coq
 *)

Definition Vec (A : Type) : nat -> Type :=
  fix vec n := match n with
               | O => unit
               | S n => prod A (vec n)
               end.

Definition proj_vec {A : Type} {n : nat} (v : Vec A n) (m : nat) : m < n -> A .
  generalize dependent m.
  induction n; intros.
  pose proof (Nat.nlt_0_r m).
  contradiction.
  simpl in v.
  destruct v.
  destruct m.
  exact a.
  apply IHn with (m:=m).
  apply v.
  apply lt_S_n.
  apply H.
Defined.

Definition vec_functor {A : Type} { n : nat} (v1 : Vec A n) (f : A -> Type) : Vec Type n.
  induction n.
  exact tt.
  destruct v1.
  constructor.
  eapply f.
  exact a.
  eapply IHn.
  exact v.
Defined.  
  
Definition dependent_Vec {A: Type} {n : nat} (v1 : Vec A n) (f : A -> Type) : Type.
  induction n.
  exact unit.
  simpl in *.
  destruct v1.
  apply prod.
  apply f.
  exact a.
  apply IHn.
  exact v.
Defined.  

Definition proj_dvec {A : Type} {n : nat} {v1 : Vec A n} {f : A -> Type} (v2 : dependent_Vec v1 f) : forall (o : nat) (H : o < n), (f (proj_vec v1 o H)).
  induction n; intros.
  pose proof (Nat.nlt_0_r (o)).
  contradiction.
  simpl in v1.
  destruct v1.
  simpl in v2.
  destruct v2.
  destruct o.
  simpl.
  apply f0.
  simpl.
  apply IHn.
  apply d.
Defined.

(* forall x : dom, lt (size x) BOUND -> cod x *)
Definition recursive_calls {n : nat} {dom_types : Vec Type n} (sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type))%type)) (BOUND : nat) : Type.
  induction n.
  exact unit.
  destruct dom_types as (dom, dom_types).
  destruct sizes_and_cods as ((size, cod), sizes_and_cods).
  eapply prod.
  2 : eapply (IHn dom_types sizes_and_cods).
  exact (forall (x : dom),
            lt (size x) BOUND ->
            cod x).
Defined.      

Definition Fix_templates_base {iterator n : nat} {dom_types : Vec Type n} {dom_types_iterator : Vec Type iterator} (sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type)) % type)) (sizes_and_cods_iterator : dependent_Vec dom_types_iterator (fun T => ((T -> nat) * (T -> Type)) % type))  : Type.
  generalize dependent n.
  induction iterator; intros.
  exact unit.
  destruct dom_types_iterator as (dom, dom_types_iterator).
  destruct sizes_and_cods_iterator as ((size, cod) , sizes_and_cods_iterator).
  eapply prod.
  2 : {
    
    eapply IHiterator.
    eapply sizes_and_cods_iterator.
    exact sizes_and_cods.
  }
  exact (forall (x : dom),
            recursive_calls sizes_and_cods (size x) ->
            cod x).
Defined.

Definition Fix_templates {n : nat} {dom_types : Vec Type n} (sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type)) % type)) : Type :=
  (Fix_templates_base sizes_and_cods sizes_and_cods).

Definition extract_template_base {iterator n : nat} {dom_types : Vec Type n} {dom_types_iterator : Vec Type iterator} 
           {sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type)) % type)}
           {sizes_and_cods_iterator : dependent_Vec dom_types_iterator (fun T => ((T -> nat) * (T -> Type)) % type)}
           (F : Fix_templates_base sizes_and_cods sizes_and_cods_iterator)
           (k : nat) (H : k < iterator)  : (forall (x : proj_vec dom_types_iterator k H),
                                               recursive_calls sizes_and_cods ((fst (proj_dvec sizes_and_cods_iterator k  H)) x) ->
                                              (snd (proj_dvec sizes_and_cods_iterator k H)) x). 
  generalize dependent k.
  induction iterator; intros k H.
  pose proof (Nat.nlt_0_r (k)).
  contradiction.
  destruct dom_types_iterator as (dom, dom_types_iterator).
  destruct sizes_and_cods_iterator as ((size, cod) , sizes_and_cods_iterator).
  destruct F.
  destruct k.
  exact c.
  specialize (IHiterator _ _ f).
  apply (IHiterator k).
Defined.

Definition extract_template
           {n : nat}
           {dom_types : Vec Type n}
           {sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type)) % type)}
           (F : Fix_templates sizes_and_cods) (k : nat) (H : k < n) : (forall (x : proj_vec dom_types k H),
                                               recursive_calls sizes_and_cods ((fst (proj_dvec sizes_and_cods k  H)) x) ->
                                               (snd (proj_dvec sizes_and_cods k H)) x) :=
  (extract_template_base F k H).

   
Module Type n_ary_template.
  Parameter n : nat.

  (* First the argument type, then the size function and then the codomain type *)

  Parameter dom_types : Vec Type n.

  Parameter sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T-> Type))%type).

  Parameter templates : Fix_templates sizes_and_cods.
End n_ary_template.

Module arbitrary_mutual (args : n_ary_template).
  Import args.
  
  Definition Fix_F_Types {n : nat} {dom_types : Vec Type n} (sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat) * (T -> Type)) % type)) : Type.
    induction n.
    exact unit.
    destruct dom_types as (dom, dom_types).
    destruct sizes_and_cods as ((size, cod), sizes_and_cods).
    eapply prod.
    2 : eapply IHn.
    2 : eapply sizes_and_cods.
    exact (forall (x : dom) (a : Acc lt (size x)), cod x).
  Defined.
(*
  Definition Fix_F {m n: nat} {dom_types_m : Vec Type m}{dom_types : Vec Type n} {sizes_and_cods : dependent_Vec dom_types (fun T => ((T -> nat ) * (T -> Type)) %type)}{sizes_and_cods_m : dependent_Vec dom_types_m (fun T => ((T -> nat ) * (T -> Type)) %type)}
             (templates : Fix_templates_base sizes_and_cods sizes_and_cods_m) : Fix_F_Types sizes_and_cods.
    generalize dependent m.
    induction n; intros.
    exact tt.
    destruct dom_types as (dom, dom_types).
    destruct sizes_and_cods as ((size, cod), sizes_and_cods).
    destruct m.
    simpl in *.
    (*TODO ANOTHER DAY *)
    
  Fixpoint Fix_F_A (x : A) (a : Acc lt (size_A x)) {struct a}: P_A x := 
    F_A x
        (fun (y : A) (H : lt (size_A y) (size_A x)) => Fix_F_A y (Acc_inv a H))
        (fun (y : B) (H : lt (size_B y) (size_A x)) => Fix_F_B y (Acc_inv a H))
        (fun (y : C) (H : lt (size_C y) (size_A x)) => Fix_F_C y (Acc_inv a H))
  with Fix_F_B (x : B) (b : Acc lt (size_B x)) {struct b} : P_B x := 
         F_B x
             (fun (y : A) (H : lt (size_A y) (size_B x)) => Fix_F_A y (Acc_inv b H))
             (fun (y : B) (H : lt (size_B y) (size_B x)) => Fix_F_B y (Acc_inv b H))
             (fun (y : C) (H : lt (size_C y) (size_B x)) => Fix_F_C y (Acc_inv b H)) 
  with Fix_F_C (x : C) (c : Acc lt (size_C x)) {struct c} : P_C x := 
         F_C x
             (fun (y : A) (H : lt (size_A y) (size_C x)) => Fix_F_A y (Acc_inv c H))
             (fun (y : B) (H : lt (size_B y) (size_C x)) => Fix_F_B y (Acc_inv c H))
             (fun (y : C) (H : lt (size_C y) (size_C x)) => Fix_F_C y (Acc_inv c H)) 
  .
  
  Lemma Fix_F_A_eq (x : A) (a : Acc lt (size_A x)):
    F_A x
        (fun (y : A) (H : lt (size_A y) (size_A x)) => Fix_F_A y (Acc_inv a H))
        (fun (y : B) (H : lt (size_B y) (size_A x)) => Fix_F_B y (Acc_inv a H))
        (fun (y : C) (H : lt (size_C y) (size_A x)) => Fix_F_C y (Acc_inv a H))
    = Fix_F_A x a.
  Proof.
    destruct a.
    reflexivity.
  Qed.
  
  Lemma Fix_F_B_eq (x : B) (b : Acc lt (size_B x)):
    F_B x
        (fun (y : A) (H : lt (size_A y) (size_B x)) => Fix_F_A y (Acc_inv b H))
        (fun (y : B) (H : lt (size_B y) (size_B x)) => Fix_F_B y (Acc_inv b H))
        (fun (y : C) (H : lt (size_C y) (size_B x)) => Fix_F_C y (Acc_inv b H))
    = Fix_F_B x b.
  Proof.
    destruct b.
    reflexivity.
  Qed.

  Lemma Fix_F_C_eq (x : C) (c : Acc lt (size_C x)):
    F_C x
        (fun (y : A) (H : lt (size_A y) (size_C x)) => Fix_F_A y (Acc_inv c H))
        (fun (y : B) (H : lt (size_B y) (size_C x)) => Fix_F_B y (Acc_inv c H))
        (fun (y : C) (H : lt (size_C y) (size_C x)) => Fix_F_C y (Acc_inv c H))
    = Fix_F_C x c.
  Proof.
    destruct c.
    reflexivity.
  Qed.
  
  Definition Fix_A (x : A) := Fix_F_A x (lt_wf (size_A x)).
  Definition Fix_B (x : B) := Fix_F_B x (lt_wf (size_B x)).
  Definition Fix_C (x : C) := Fix_F_C x (lt_wf (size_C x)).

  Lemma Fix_F_A_inv : forall (x : A) (r s : Acc lt (size_A x)),
      Fix_F_A x r = Fix_F_A x s
  with Fix_F_B_inv : forall (x : B) (r s : Acc lt (size_B x)),
      Fix_F_B x r = Fix_F_B x s
  with Fix_F_C_inv : forall (x : C) (r s : Acc lt (size_C x)),
      Fix_F_C x r = Fix_F_C x s.
  Proof.
    - intros.
      destruct r.
      destruct s.
      simpl.
      f_equal.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_A_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_B_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_C_inv.
    - intros.
      destruct r.
      destruct s.
      simpl.
      f_equal.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_A_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_B_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_C_inv.
    - intros.
      destruct r.
      destruct s.
      simpl.
      f_equal.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_A_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_B_inv.
      + do 2 (eapply functional_extensionality_dep ;intros).        
        eapply Fix_F_C_inv.
  Qed.        
      
  Lemma Fix_A_eq (x : A) :
    Fix_A x = F_A x (fun (y : A) (a : lt (size_A y) (size_A x)) => Fix_A y) (fun (y : B) (a : lt (size_B y) (size_A x)) => Fix_B y) (fun (y : C) (a : lt (size_C y) (size_A x)) => Fix_C y).
  Proof.
    unfold Fix_A.
    rewrite <- Fix_F_A_eq.
    f_equal.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_A_inv.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_B_inv.    
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_C_inv.    
  Qed.

  Lemma Fix_B_eq (x : B) :
    Fix_B x = F_B x (fun (y : A) (a : lt (size_A y) (size_B x)) => Fix_A y) (fun (y : B) (a : lt (size_B y) (size_B x)) => Fix_B y) (fun (y : C) (a : lt (size_C y) (size_B x)) => Fix_C y).
  Proof.
    unfold Fix_B.
    rewrite <- Fix_F_B_eq.
    f_equal.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_A_inv.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_B_inv.    
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_C_inv.    
  Qed.

  Lemma Fix_C_eq (x : C) :
    Fix_C x = F_C x (fun (y : A) (a : lt (size_A y) (size_C x)) => Fix_A y) (fun (y : B) (a : lt (size_B y) (size_C x)) => Fix_B y) (fun (y : C) (a : lt (size_C y) (size_C x)) => Fix_C y).
  Proof.
    unfold Fix_C.
    rewrite <- Fix_F_C_eq.
    f_equal.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_A_inv.
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_B_inv.    
    + do 2 (eapply functional_extensionality_dep ;intros).        
      eapply Fix_F_C_inv.    
  Qed.

End triple_fix.
 *)
End arbitrary_mutual.

