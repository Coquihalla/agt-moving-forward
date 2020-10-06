Set Bullet Behavior "Strict Subproofs".

(* This system is intended to model more closely the presentation on the paper on how to generally define an AGT language,
   based on the original galois connection proofs *)
Require Import PoplLibraries.Math.
Require Import PoplLibraries.Setoid_library.
Require Import PoplLibraries.Recursion.
(* This file contains the Galois Connection proofs *)
Require Import AGT.AGT_Spec. 

(* This module is an example of using things.
   Of course, to make anything of use, you want to replace all the axioms.
*)

Module Example_AGT <: AGT_Inputs.
  Axiom ST : Set.

  Axiom ST_eq : relation ST.

  Axiom ST_eq_refl : Reflexive ST_eq.
  Axiom ST_eq_sym : Symmetric ST_eq.
  Axiom ST_eq_trans : Transitive ST_eq.

  Hint Resolve ST_eq_refl ST_eq_sym ST_eq_trans : setoids.
  
  Add Parametric Relation : ST ST_eq
      reflexivity  proved by ST_eq_refl
      symmetry     proved by ST_eq_sym
      transitivity proved by ST_eq_trans
  as ST_eq_rel.
     
  (* And a definition of Gradual Types. Our model is parameterized by these. *)
  Axiom GT : Set.

  Axiom GT_eq : relation GT.
  Axiom GT_eq_refl : Reflexive GT_eq.
  Axiom GT_eq_sym : Symmetric GT_eq.
  Axiom GT_eq_trans : Transitive GT_eq.

  Hint Resolve GT_eq_refl GT_eq_sym GT_eq_trans : setoids.
  
  Add Parametric Relation : GT GT_eq
      reflexivity  proved by GT_eq_refl
      symmetry     proved by GT_eq_sym
      transitivity proved by GT_eq_trans
        as GT_eq_rel.
  
  (* We follow the "from scratch" approach, where concretization is defined by recursion on the structure of gradual types,
     and where then the precision relation is inferred. *)
  
  Axiom gamma : GT -> Ensemble ST. (* Note, Ensembles, are a representation of Sets in Coq *)

  Axiom gamma_compat :
    forall x x' : GT,
      GT_eq x x' ->
      Seteq ST_eq (gamma x) (gamma x').

  Hint Resolve gamma_compat : setoids.
  

  Axiom gamma_compat_dual :
    forall x x' : GT,
      Seteq ST_eq (gamma x) (gamma x') ->
      GT_eq x x'.
  
  Add Parametric Morphism : gamma
      with signature GT_eq ==> (Seteq ST_eq) as gamma_mor.
  Proof.
    exact gamma_compat.
  Qed.

  Add Parametric Relation : (Ensemble ST) (Seteq ST_eq)
      reflexivity  proved by (Seteq_refl ST_eq_refl)
      symmetry     proved by (Seteq_sym)
      transitivity proved by (Seteq_trans ST_eq_trans)
  as Ensemble_ST_eq_rel.

  Add Parametric Relation : (Ensemble GT) (Seteq GT_eq)
      reflexivity  proved by (Seteq_refl GT_eq_refl)
      symmetry     proved by (Seteq_sym)
      transitivity proved by (Seteq_trans GT_eq_trans)
  as Ensemble_GT_eq_rel.
                                            
  Axiom gamma_spec : forall x,
      exists y, SetIn ST_eq (gamma x) y.
  
  Definition less_imprecise (S_1 S_2 : GT) :=
    Subseteq ST_eq (gamma S_1) (gamma S_2). (* Proposition 3.1 *)

  Add Parametric Relation : (Ensemble GT) (Subseteq GT_eq)
      reflexivity  proved by (subseteq_refl GT_eq_refl)
      transitivity proved by (subseteq_trans GT_eq_trans)
        as Ensemble_GT_subseteq_rel.

  Add Parametric Relation : (Ensemble ST) (Subseteq ST_eq)
      reflexivity  proved by (subseteq_refl ST_eq_refl)
      transitivity proved by (subseteq_trans ST_eq_trans)
        as Ensemble_ST_subseteq_rel.  
  
  (* While we could have followed a "define alpha as well" approach,
     we will try here to be as consistent with the paper as possible,
     which relies instead on a definition of meet and generates for you a definition of alpha, which is the one we will use.
   *)

  Axiom meet : GT -> GT -> option GT.

  (* Might be necessary, but not yet.
     Axiom meet_sym : forall (S_1 S_2 : GT),
      meet S_1 S_2 = meet S_2 S_1.
   *)
  Parameter meet_compat :
    forall x x' : GT,
      GT_eq x x' ->
      forall y y' : GT,
        GT_eq y y' ->
        option_eq GT_eq (meet x y) (meet x' y').

  Hint Resolve meet_compat : setoids.
  
  Add Parametric Morphism : meet
      with signature GT_eq ==> GT_eq ==> option_eq GT_eq as meet_mor.
  Proof.
    exact meet_compat.
  Qed.
  
  Axiom meet_spec_1 : forall (S_1 S_2 S_3: GT),
      option_eq GT_eq (meet S_1 S_2) (Some S_3) ->
      Seteq ST_eq (gamma S_3)
            (Intersection ST_eq (gamma S_1) (gamma S_2)).

  Axiom meet_spec_2 : forall S_1 S_2,
      option_eq GT_eq (meet S_1 S_2) None ->
      Seteq ST_eq (Empty_set _)
            (Intersection ST_eq (gamma S_1) (gamma S_2)).
  
  (* Our spec for alpha is according to the paper : *)

  (* These definitions of lower_bound and greatest lower bound are 
     not necessary, but I keep them here for reference : *)

  Definition all_bigger_types (C : Ensemble ST) : Ensemble GT := (fun X => Subseteq ST_eq C (gamma X)).

  Add Parametric Morphism : all_bigger_types
      with signature (Seteq ST_eq) ==> (Seteq GT_eq) as all_bigger_types_mor.
  Proof with eauto with setoids.
    intros.
    unfold all_bigger_types.
    split.
    all: intro x'.
    all: unfold In.
    all: intros.
    - eapply SetIn_seteq_mor...
      eapply Seteq_extensionality...
      intros.
      eapply SetIn_mor...
      intros a b H'...
      rewrite H'.
      rewrite H.
      reflexivity.
    - eapply SetIn_seteq_mor...
      eapply Seteq_extensionality...
      intros.
      eapply SetIn_mor...
      intros a b H'...
      rewrite H'.
      rewrite H.
      reflexivity.
  Qed.
  
    (* Backtracking : I need to go back and make better and stronger use of the generalized rewriting features.  In particular, I do need stuff to work in previous cases (For example, subseteq must be made a morphism, etc. *)
  
  Definition lower_bound (S : Ensemble GT) (a : GT) : Prop :=
    forall (x : GT), SetIn GT_eq S x -> less_imprecise a x.
  
  Definition greatest_lower_bound (S : Ensemble GT) (a : GT) : Prop :=
    (lower_bound S a) /\ (forall k, lower_bound S k -> less_imprecise k a).
  
  
  (* I think this is a key that we have not expressed before. *)
  Axiom all_bigger_types_has_greatest_lower_bound :
    forall (C : Ensemble ST),
    exists a,
      (greatest_lower_bound (all_bigger_types C) a)
  .

  (* This is a nice paper title: "Minimum AGT", or "AGT at Least is sound"*)
    
  Axiom glb_is_minimum : forall (C : Ensemble ST),
      forall a,
        (greatest_lower_bound (all_bigger_types C) a) ->
        SetIn GT_eq (all_bigger_types C) a.
  
  Inductive alpha : Ensemble ST -> GT -> Prop :=
  | alpha_constructor :
      forall C out,
        (* out is a lower bound *)
        Ensembles.Inhabited _ C ->
        greatest_lower_bound (all_bigger_types C) out ->
        alpha C out.

  Hint Constructors alpha : setoids.

  Add Parametric Morphism : less_imprecise
      with signature GT_eq ==> GT_eq ==> iff as less_imprecise_mor.
  Proof.
    intros.
    split; intros; unfold less_imprecise in *.
    rewrite <- H.
    rewrite <- H0.
    eauto.
    rewrite H.
    rewrite H0.
    eauto.
  Qed.    
  
  Add Parametric Morphism : lower_bound
      with signature (Seteq GT_eq) ==> GT_eq ==> iff as lower_bound_mor.
  Proof with eauto with setoids.
    intros.
    split; intros.
    all: unfold lower_bound in *.
    all: intros.
    all: apply H in H2.
    all: apply H1 in H2.
    - rewrite H0 in H2...
    - rewrite <- H0 in H2...
  Qed.      
    
  Add Parametric Morphism : greatest_lower_bound
      with signature (Seteq GT_eq) ==> GT_eq ==> iff as greatest_lower_bound_mor.
  Proof with eauto with setoids.
    intros.
    split; intros...
    all: inversion H1.
    all: constructor.
    - rewrite <- H.
      rewrite <- H0...
    - intros.
      rewrite <- H0.
      eapply H3.
      rewrite H...
    - rewrite H.
      rewrite H0...
    - intros.
      rewrite H0.
      eapply H3.
      rewrite <- H...
  Qed.
  
  Add Parametric Morphism : alpha 
      with signature (Seteq ST_eq) ==> GT_eq ==> iff as alpha_mor.
  Proof with eauto with setoids.
    intros.
    split.
    all: intros.
    all: inversion H1.
    all: subst.
    - econstructor.
      inversion H2.
      apply In_SetIn with (eqb:=ST_eq) in H4...
      apply H in H4.
      repeat destruct H4...
      econstructor; apply H5.

      rewrite <- H.
      rewrite <- H0...
    - econstructor.
      inversion H2.
      apply In_SetIn with (eqb:=ST_eq) in H4...
      apply H in H4.
      repeat destruct H4.
      econstructor; apply H5.

      rewrite H.
      rewrite H0...
  Qed.
    
  (* Now we introduce a predicate over static types *)

  Axiom static_pred : ST -> ST -> Prop.

  Axiom static_pred_refl : forall x,
      static_pred x x.

  Axiom static_pred_trans : forall x_1 x_2 x_3,
      static_pred x_1 x_2 ->
      static_pred x_2 x_3 ->
      static_pred x_1 x_3.

  Hint Resolve static_pred_refl static_pred_trans : setoids.

  Add Parametric Relation : ST static_pred
      reflexivity  proved by (static_pred_refl)
      transitivity proved by (static_pred_trans)
        as static_pred_rel.  
 
  Definition gradual_pred (S_1 S_2 : GT) : Prop :=
    exists T_1 T_2,
      SetIn ST_eq (gamma S_1) T_1 /\
      SetIn ST_eq (gamma S_2) T_2 /\
      static_pred T_1 T_2. (* Proposition 2.2 *)

  
  Theorem gc_soundness : forall C S,
      alpha C S ->
      Subseteq ST_eq C (gamma S).
  Proof.
    intros.
    inversion H; subst.
    inversion H1.
    unfold lower_bound in H2.
    eapply glb_is_minimum in H1.
    repeat destruct H1.
    rewrite H1.
    eauto.
  Qed.

  Hint Resolve gc_soundness : setoids.
  
  Axiom Ev : Set.

  (* While we could do Evidence equivalence a parameter, I instead define it in terms of projections, as that seems to be the most useful at this point *)
  Axiom proj1_ev : Ev -> GT.
  Axiom proj2_ev : Ev -> GT.
  
  Inductive Ev_eq : relation Ev :=
  | Ev_eq_intro : forall e e',
      GT_eq (proj1_ev e) (proj1_ev e') ->
      GT_eq (proj2_ev e) (proj2_ev e') ->
      Ev_eq e e'.

  Hint Constructors Ev_eq : setoids.
  Lemma Ev_eq_refl : Reflexive Ev_eq.
  Proof.
    econstructor;
    eauto with setoids.
  Qed.    

  Lemma Ev_eq_sym : Symmetric Ev_eq.
  Proof.
    econstructor; inversion H;
    eauto with setoids.
  Qed.    

  Lemma Ev_eq_trans : Transitive Ev_eq.
  Proof.
    econstructor; inversion H; inversion H0;
    eauto with setoids.
  Qed.    

  Hint Resolve Ev_eq_refl Ev_eq_sym Ev_eq_trans : setoids.
  
  Add Parametric Relation : Ev Ev_eq
      reflexivity  proved by Ev_eq_refl
      symmetry     proved by Ev_eq_sym
      transitivity proved by Ev_eq_trans
  as Ev_eq_rel.

  Axiom static_pred_compat : 
      forall x x' : ST,
        ST_eq x x' ->
        forall y y' : ST,
          ST_eq y y' ->
          (static_pred x y <-> static_pred x' y').

  Hint Resolve static_pred_compat : setoids.

  Add Parametric Morphism : static_pred
      with signature ST_eq ==> ST_eq ==> iff as static_pred_mor.
  Proof.
    exact static_pred_compat.
  Qed.

  Definition Ev_static_set := Ensemble { x : ST * ST | static_pred (fst x) (snd x) }.
  
  Axiom gamma_ev : Ev -> Ev_static_set.

  Axiom gamma_ev_compat:
    forall e e' : Ev,
      Ev_eq e e' ->
      Seteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev e) (gamma_ev e').

  Axiom gamma_ev_compat_dual :
    forall e e' : Ev,
      Seteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev e) (gamma_ev e') ->
      Ev_eq e e'.
  
  
  Hint Resolve gamma_ev_compat : setoids.
  
  Add Parametric Morphism : gamma_ev
      with signature Ev_eq ==> (Seteq (sig_eq (pair_eq ST_eq ST_eq))) as gamma_ev_mor.
  Proof.
    exact gamma_ev_compat.
  Qed.
      
  Axiom gamma_ev_spec_l : forall ev x,
      SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) x ->
      SetIn ST_eq (gamma (proj1_ev ev)) (fst (proj1_sig x)).

  Axiom gamma_ev_spec_r : forall ev x,
      SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) x ->
      SetIn ST_eq (gamma (proj2_ev ev)) (snd (proj1_sig x)).
  
  Axiom alpha_ev : Ensemble { x : ST * ST | static_pred (fst x) (snd x) } -> Ev -> Prop.

  Axiom alpha_ev_compat : forall (s1 s2 : Ensemble { x : ST * ST | static_pred (fst x) (snd x) }),
      Seteq (sig_eq (pair_eq ST_eq ST_eq)) s1 s2 ->
      forall (e1 e2 : Ev),
        Ev_eq e1 e2 ->
        (alpha_ev s1 e1 <-> alpha_ev s2 e2).

  Hint Resolve gamma_ev_spec_l gamma_ev_spec_r alpha_ev_compat : setoids.
  
  Add Parametric Morphism : alpha_ev
      with signature (Seteq (sig_eq (pair_eq ST_eq ST_eq)) ==> Ev_eq ==> iff) as alpha_ev_mor.
  Proof.
    exact alpha_ev_compat.
  Qed.
    
  (* There's a note on page 18 defining interior as follows: *)

  Axiom static_pred_dec : forall T_1 T_2,
      {static_pred T_1 T_2} + {~ static_pred T_1 T_2}.
  
  Definition interior : GT -> GT -> Ev -> Prop :=
    fun (S_1 S_2 : GT) (ev : Ev) =>
      alpha_ev
        (fun (X : {x : ST * ST | static_pred (fst x) (snd x)}) =>
           SetIn ST_eq (gamma S_1) (fst (proj1_sig X)) /\
           SetIn ST_eq (gamma S_2) (snd (proj1_sig X))
                 (* Note: There is a proof of static_pred carried in the input,
                    so I don't need to check for it here *)
        )
                 ev.

  Axiom ev_self_interior : forall (e : Ev),
      interior (proj1_ev e) (proj2_ev e) e.

  Hint Resolve ev_self_interior : setoids.

  (* This definition must make use of equality relations over A as well. *)
  
  Definition relational_composition {A : Type} {P : A * A -> Prop}
             (eq : relation A)
             (R1 : Ensemble {x : A * A | P x})
             (R2 : Ensemble {x : A * A | P x}) : Ensemble {x : A * A | P x} :=
    fun (elem : {x : A * A | P x}) =>
      exists T_2 T'_l T'_r (W_l : P T'_l) (W_r : P T'_r),
        SetIn (sig_eq (pair_eq eq eq)) R1 (exist _ T'_l W_l) /\
        SetIn (sig_eq (pair_eq eq eq)) R2 (exist _ T'_r W_r) /\
        (pair_eq eq eq (fst (proj1_sig elem), T_2) T'_l) /\
        (pair_eq eq eq (T_2, (snd (proj1_sig elem))) T'_r) .
    
  Definition consistent_transitivity (e1 e2 e3 : Ev) : Prop :=
    (* Id+ is implicit through the requirement of inhabitance in alpha *)
    alpha_ev (relational_composition ST_eq (gamma_ev e1) (gamma_ev e2)) e3.
  
  Axiom gamma_completeness : forall e1 e2 e3,
      consistent_transitivity e1 e2 e3 ->
      (Seteq (sig_eq (pair_eq ST_eq ST_eq))
             (relational_composition ST_eq (gamma_ev e1) (gamma_ev e2))
       (gamma_ev e3)).

  Axiom gc_ev_optimality : forall C S,
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) C (gamma_ev S) ->
      forall S',
        alpha_ev C S' ->
        Subseteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev S') (gamma_ev S).
  
  Axiom gc_ev_soundness : forall C S,
      alpha_ev C S ->
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) C (gamma_ev S).

  Axiom proj1_ev_spec : forall ev x,
      SetIn ST_eq (gamma (proj1_ev ev)) x ->
      exists (x' : ST) (H : static_pred x x'),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev)
              (exist _ (x, x') H).
  
  Axiom proj2_ev_spec : forall ev x,
      SetIn ST_eq (gamma (proj2_ev ev)) x ->
      exists (x' : ST) (H : static_pred x' x),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev)
              (exist _ (x', x) H).

  Axiom closedness : forall ( AB BC : Ev),
      forall (proj_based : Ev),
        interior (proj1_ev AB) (proj2_ev BC) proj_based ->
        (Subseteq (sig_eq (pair_eq ST_eq ST_eq))
                  (gamma_ev proj_based)
                  (relational_composition ST_eq (gamma_ev AB) (gamma_ev BC))).
  
  Axiom gamma_ev_spec' : forall ev x,
      SetIn ST_eq (gamma (proj1_ev ev)) (fst x) ->
      SetIn ST_eq (gamma (proj2_ev ev)) (snd x) ->
      forall (H : static_pred (fst x) (snd x)),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) (exist _ x H).
End Example_AGT.


Module AGT_Proofs := AGT_Spec Example_AGT.
