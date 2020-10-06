Set Bullet Behavior "Strict Subproofs".

(* This system is intended to model more closely the presentation on the paper on how to generally define an AGT language,
   based on the original galois connection proofs *)

Require Import PoplLibraries.Math.
Require Import PoplLibraries.Setoid_library.
(* This file contains the Galois Connection proofs *)

Require Import Classical.

Module Type AGT_Inputs.
  (* This definuition is based upon the section "The Essence of AGT" and is intended to mirror it. *)

  (* We require a definition of Static Types *)
  Parameter ST : Set.

  Parameter ST_eq : relation ST.

  Parameter ST_eq_refl : Reflexive ST_eq.
  Parameter ST_eq_sym : Symmetric ST_eq.
  Parameter ST_eq_trans : Transitive ST_eq.

  Hint Resolve ST_eq_refl ST_eq_sym ST_eq_trans : setoids.
  
  Add Parametric Relation : ST ST_eq
      reflexivity  proved by ST_eq_refl
      symmetry     proved by ST_eq_sym
      transitivity proved by ST_eq_trans
  as ST_eq_rel.
     
  (* And a definition of Gradual Types. Our model is parameterized by these. *)
  Parameter GT : Set.

  Parameter GT_eq : relation GT.
  Parameter GT_eq_refl : Reflexive GT_eq.
  Parameter GT_eq_sym : Symmetric GT_eq.
  Parameter GT_eq_trans : Transitive GT_eq.

  Hint Resolve GT_eq_refl GT_eq_sym GT_eq_trans : setoids.
  
  Add Parametric Relation : GT GT_eq
      reflexivity  proved by GT_eq_refl
      symmetry     proved by GT_eq_sym
      transitivity proved by GT_eq_trans
        as GT_eq_rel.
  
  (* We follow the "from scratch" approach, where concretization is defined by recursion on the structure of gradual types,
     and where then the precision relation is inferred. *)
  
  Parameter gamma : GT -> Ensemble ST. (* Note, Ensembles, are a representation of Sets in Coq *)

  Parameter gamma_compat :
    forall x x' : GT,
      GT_eq x x' ->
      Seteq ST_eq (gamma x) (gamma x').

  Hint Resolve gamma_compat : setoids.
  
  Parameter gamma_compat_dual :
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
                                            
  Parameter gamma_spec : forall x,
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

  Parameter meet : GT -> GT -> option GT.


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

  
  Parameter meet_spec_1 : forall (S_1 S_2 S_3: GT),
      option_eq GT_eq (meet S_1 S_2) (Some S_3) ->
      Seteq ST_eq (gamma S_3)
            (Intersection ST_eq (gamma S_1) (gamma S_2)).

  Parameter meet_spec_2 : forall S_1 S_2,
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
  
  Parameter all_bigger_types_has_greatest_lower_bound :
    forall (C : Ensemble ST),
    exists a,
      (greatest_lower_bound (all_bigger_types C) a)
  .
    
  Parameter glb_is_minimum : forall (C : Ensemble ST),
      forall a,
        (greatest_lower_bound (all_bigger_types C) a) ->
        SetIn GT_eq (all_bigger_types C) a.
  
  Inductive alpha : Ensemble ST -> GT -> Prop :=
  | alpha_constructor :
      forall C out,
        (* out is a lower bound *)
        Inhabited _ C ->
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

  Parameter static_pred : ST -> ST -> Prop.

  Parameter static_pred_refl : forall x,
      static_pred x x.

  Parameter static_pred_trans : forall x_1 x_2 x_3,
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
  
  Parameter Ev : Set.

  (* While we could do Evidence equivalence a parameter, I instead define it in terms of projections, as that seems to be the most useful at this point *)
  Parameter proj1_ev : Ev -> GT.
  Parameter proj2_ev : Ev -> GT.
  
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

  Parameter static_pred_compat : 
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


  
  Parameter gamma_ev : Ev -> Ev_static_set.

  Parameter gamma_ev_compat:
    forall e e' : Ev,
      Ev_eq e e' ->
      Seteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev e) (gamma_ev e').

  Parameter gamma_ev_compat_dual :
    forall e e' : Ev,
      Seteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev e) (gamma_ev e') ->
      Ev_eq e e'.
  
  
  Hint Resolve gamma_ev_compat : setoids.
  
  Add Parametric Morphism : gamma_ev
      with signature Ev_eq ==> (Seteq (sig_eq (pair_eq ST_eq ST_eq))) as gamma_ev_mor.
  Proof.
    exact gamma_ev_compat.
  Qed.
      
  Parameter gamma_ev_spec_l : forall ev x,
      SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) x ->
      SetIn ST_eq (gamma (proj1_ev ev)) (fst (proj1_sig x)).

  Parameter gamma_ev_spec_r : forall ev x,
      SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) x ->
      SetIn ST_eq (gamma (proj2_ev ev)) (snd (proj1_sig x)).
  
  Parameter alpha_ev : Ensemble { x : ST * ST | static_pred (fst x) (snd x) } -> Ev -> Prop.

  Parameter alpha_ev_compat : forall (s1 s2 : Ensemble { x : ST * ST | static_pred (fst x) (snd x) }),
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
    

  Parameter static_pred_dec : forall T_1 T_2,
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

  Parameter ev_self_interior : forall (e : Ev),
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
  
  Parameter gamma_completeness : forall e1 e2 e3,
      consistent_transitivity e1 e2 e3 ->
      (Seteq (sig_eq (pair_eq ST_eq ST_eq))
             (relational_composition ST_eq (gamma_ev e1) (gamma_ev e2))
       (gamma_ev e3)).

  Parameter gc_ev_optimality : forall C S,
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) C (gamma_ev S) ->
      forall S',
        alpha_ev C S' ->
        Subseteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev S') (gamma_ev S).
  
  Parameter gc_ev_soundness : forall C S,
      alpha_ev C S ->
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) C (gamma_ev S).

  Parameter proj1_ev_spec : forall ev x,
      SetIn ST_eq (gamma (proj1_ev ev)) x ->
      exists (x' : ST) (H : static_pred x x'),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev)
              (exist _ (x, x') H).
  
  Parameter proj2_ev_spec : forall ev x,
      SetIn ST_eq (gamma (proj2_ev ev)) x ->
      exists (x' : ST) (H : static_pred x' x),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev)
              (exist _ (x', x) H).

  Parameter closedness : forall ( AB BC : Ev),
      forall (proj_based : Ev),
        interior (proj1_ev AB) (proj2_ev BC) proj_based ->
        (Subseteq (sig_eq (pair_eq ST_eq ST_eq))
                  (gamma_ev proj_based)
                  (relational_composition ST_eq (gamma_ev AB) (gamma_ev BC))).

  (* This parameter is sort of a proof irrelevance parameter. *)
  Parameter gamma_ev_spec' : forall ev x,
      SetIn ST_eq (gamma (proj1_ev ev)) (fst x) ->
      SetIn ST_eq (gamma (proj2_ev ev)) (snd x) ->
      forall (H : static_pred (fst x) (snd x)),
        SetIn (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev ev) (exist _ x H).

  Hint Resolve gamma_completeness gc_ev_optimality gc_ev_soundness proj1_ev_spec proj2_ev_spec : setoids.

End AGT_Inputs.

Module AGT_Spec (AGT : AGT_Inputs).
  Import AGT.

  Instance exist_iff_morphism :
    Proper ((pair_eq ST_eq ST_eq) >==> { x & y } ((fun H H0 => ST_eq (fst x) (fst y) /\ ST_eq (snd x) (snd y)) >==> { _ & _ } (@sig_eq _ (fun x => static_pred (fst x) (snd x)) (pair_eq ST_eq ST_eq))))
           (@exist (ST*ST)%type (fun x => static_pred (fst x) (snd x))).
  Proof.
    simpl_relation.
  Qed.
  
  Theorem meet_assoc : forall (S_1 S_2 S_3 : GT),
      option_eq GT_eq (match (meet S_1 S_2) with
                 | Some S_12 => meet S_12 S_3
                 | None => None
                 end)
                (match (meet S_2 S_3) with
                 | Some S_23 => meet S_1 S_23
                 | None => None
                 end).
  Proof with eauto with setoids.
    intros.

    repeat match goal with
           | [ |- context[meet ?A ?B]] =>
             let H' := fresh in destruct (meet A B) eqn:H';
             (let H := fresh in pose proof (option_eq_refl GT_eq_refl (meet A B)) as H;
                                 rewrite H' in H at 2;
                                 clear H')
           end.

      
    all: repeat match goal with
                | [ H : _ _ _ (Some _) |- _ ]=> apply meet_spec_1 in H
                | [ H : _ _ _ None |- _]  => apply meet_spec_2 in H
                end.

    all: try reflexivity.
    
    - econstructor.
      eapply gamma_compat_dual.
      rewrite H1.
      rewrite H3.
      rewrite H0.
      rewrite H2.
      rewrite Intersection_assoc...
      reflexivity.
    - rewrite H0 in H1.
      rewrite H2 in H3.
      rewrite Intersection_assoc in H3...
      rewrite <- H1 in H3.
      destruct (gamma_spec g0).
      apply H3 in H.
      repeat destruct H.
      eapply except.
      eapply (Noone_in_empty _ x0)...
    - rewrite H0 in H1.
      destruct (gamma_spec g0).
      rewrite <- Intersection_assoc in H1...
      apply H1 in H.
      repeat destruct H.
      inversion H3.
      subst.
      apply H2 in H5.
      repeat destruct H5.
      eapply except.
      eapply (Noone_in_empty _ x1)...
    - rewrite H0 in H1.
      rewrite H2 in H3.
      rewrite Intersection_assoc in H3...
      rewrite <- H1 in H3.
      destruct (gamma_spec g1).
      apply H3 in H.
      repeat destruct H.
      eapply except.
      eapply (Noone_in_empty _ x0)...
    - rewrite H1 in H2.
      rewrite Intersection_assoc in H2...
      rewrite <- H0 in H2.
      destruct (gamma_spec g0).
      apply H2 in H.
      repeat destruct H.
      inversion H3.
      subst.
      repeat destruct H4.
      eapply except.
      eapply (Noone_in_empty _ x1)...
  Qed.  

  (* Proposition 3.2 should follow *)
  Theorem gc_optimality : forall C S,
      Subseteq ST_eq C (gamma S) ->
      forall S',
        alpha C S' ->
        less_imprecise S' S.
  Proof with eauto with setoids.
    intros.
    inversion H0.
    subst.
    unfold all_bigger_types in H2.
    inversion H2.
    subst.
    unfold lower_bound in H3.
    intros elem; intros.
    eapply H3 in H5...
    inversion H1.
    eexists. split.
    2 : { 
      unfold Ensembles.In.
      eassumption.
    }
    reflexivity.
  Qed.    
  
  Theorem alpha_ev_li : forall R_1 R_2 S_1 S_2,
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) R_1 R_2 ->
      alpha_ev R_1 S_1 ->
      alpha_ev R_2 S_2 ->
      Subseteq (sig_eq (pair_eq ST_eq ST_eq)) (gamma_ev S_1)
               (gamma_ev S_2).
  Proof.
    intros.
    eapply gc_ev_optimality; try eassumption.
    eapply gc_ev_soundness in H1.
    etransitivity; eassumption.
  Qed.    
      
  (* Here to prove proposition 3.3 *)  

  (* <S1, S21> ; <S22, S3> =
     I ⟦ π1 ( I ⟦S1 ≲ (S21 ⊓ S22)⟧) ≲
         π2 ( I ⟦(S21 ⊓ S22) ≲ S3⟧) ⟧
   *)

  (* This theorem is unused, maybe will be relevant later. *)
  Theorem glb_membership : forall A T,
      greatest_lower_bound A T ->
      forall y ,  SetIn GT_eq A y ->
                  Subseteq ST_eq (gamma T) (gamma y).
  Proof with eauto with setoids.
    intros.
    inversion H.
    apply H1 in H0...
  Qed.        

  Lemma meet_left : forall S_1 S_2 S_3,
      option_eq GT_eq (meet S_1 S_2) (Some S_3) ->
      less_imprecise S_3 S_1.
  Proof with eauto with setoids.
    intros.
    eapply meet_spec_1 in H.
    unfold less_imprecise.
    rewrite H.
    intros elem.
    intros.
    inversion H0.
    destruct H1.
    inversion H2; subst...
    rewrite H1...
  Qed.    

  Lemma meet_right : forall S_1 S_2 S_3,
      option_eq GT_eq (meet S_1 S_2) (Some S_3) ->
      less_imprecise S_3 S_2.
  Proof with eauto with setoids.
    intros.
    eapply meet_spec_1 in H.
    unfold less_imprecise.
    rewrite H.
    intros elem.
    intros.
    inversion H0.
    destruct H1.
    inversion H2; subst...
    rewrite H1...
  Qed.

  Instance sigeq_rel_sym (E : Type) (P : E -> Prop) (rel : relation E) (Rec : Symmetric rel)  : Symmetric (@sig_eq _ P rel).
  eapply sig_eq_sym.
  eauto.
  Defined.
  Instance sigeq_rel_equiv (E : Type) (P : E -> Prop) (rel : relation E) (Rec : Equivalence rel)  : Equivalence (@sig_eq _ P rel).
  Proof with eauto with setoids.
    inversion Rec...
  Defined.
  Add Parametric Morphism : (relational_composition ST_eq )
      with signature (Subseteq (sig_eq (pair_eq ST_eq ST_eq))) ==>
                     (Subseteq (sig_eq (pair_eq ST_eq ST_eq))) ==>
                     (Subseteq (@sig_eq _ (fun x => static_pred (fst x) (snd x)) (pair_eq ST_eq ST_eq))) as relational_composition_static_pred_mor_subset.
  Proof with eauto with setoids.
    intros.
    all: intro elem.
    all: intros.
    all: repeat destruct  H1.
    all: inversion H2.
    all: do 5 destruct H3.
    all: destruct H4.
    all: destruct H5.
    all: simpl in *.
    - apply In_SetIn with (eqb := (sig_eq (pair_eq ST_eq ST_eq))) in H2...
      rewrite H1.
      eexists.
      split.
      reflexivity.
      apply H in H3.
      apply H0 in H4.
      inversion H3.
      inversion H4.
      destruct H7.
      destruct H8.
      inversion H5.
      inversion H6.
      subst.
      destruct x7.
      destruct x8.
      repeat eexists.
      all: try match goal with
               | [ |- Ensembles.In _ _ _ ] => eassumption
               end.
      all: simpl in *...
      Unshelve.
      all: simpl in *...
  Qed.
  Add Parametric Morphism : (relational_composition ST_eq )
      with signature (Seteq (sig_eq (pair_eq ST_eq ST_eq))) ==>
                     (Seteq (sig_eq (pair_eq ST_eq ST_eq))) ==>
                     (Seteq (@sig_eq _ (fun x => static_pred (fst x) (snd x)) (pair_eq ST_eq ST_eq))) as relational_composition_static_pred_mor.
  Proof with eauto with setoids.
    intros.
    econstructor.
    all: intro elem.
    all: intros.
    all: repeat destruct  H1.
    all: inversion H2.
    all: do 5 destruct H3.
    all: destruct H4.
    all: destruct H5.
    all: simpl in *.
    - apply In_SetIn with (eqb := (sig_eq (pair_eq ST_eq ST_eq))) in H2...
      rewrite H1.
      eexists.
      split.
      reflexivity.
      rewrite H in H3.
      rewrite H0 in H4.
      inversion H3.
      inversion H4.
      destruct H7.
      destruct H8.
      inversion H5.
      inversion H6.
      subst.
      destruct x7.
      destruct x8.
      repeat eexists.
      all: try match goal with
               | [ |- Ensembles.In _ _ _ ] => eassumption
               end.
      all: simpl in *...
    - apply In_SetIn with (eqb := (sig_eq (pair_eq ST_eq ST_eq))) in H2...
      rewrite H1.
      eexists.
      split.
      reflexivity.
      rewrite <- H in H3.
      rewrite <- H0 in H4.
      inversion H3.
      inversion H4.
      destruct H7.
      destruct H8.
      inversion H5.
      inversion H6.
      subst.
      destruct x7.
      destruct x8.
      repeat eexists.
      all: try match goal with
               | [ |- Ensembles.In _ _ _ ] => eassumption
               end.
      all: simpl in *...

      Unshelve.
      all: simpl in *...
  Qed.      

  (* Todo: Move to Setoid_library *)
  Lemma SetIn_and {A : Type} {eqa : relation A} `{Equivalence A eqa}:
    forall (P Q : A -> Prop) (H' : (eqa ==> iff)%signature P Q) x,
      SetIn eqa (fun X => P X /\ Q X) x <->
      (SetIn eqa P x) /\ (SetIn eqa Q x).
  Proof with eauto with setoids.
    intros.
    split; intros...
    - inversion H0...
      unfold Ensembles.In in H1.
      destruct H1.
      destruct H2.
      split; exists x0...
    - inversion H0.
      inversion H1.
      inversion H2.
      destruct H3.
      destruct H4.
      exists x.
      unfold Ensembles.In.
      split.
      reflexivity.
      split;
      eapply H'...
      symmetry...
  Qed.      
  
  (* Consistent transitivity and interior definition are equivalent. 
   *)

  Axiom static_pred_tele : forall s1 s2 s3,
      static_pred s1 s2 ->
      static_pred s1 s3 ->
      (static_pred s2 s3 \/ static_pred s3 s2).

  
  Theorem ct_via_interior_def : forall T_1 T_2 T_3 T_4 ev1 ev2 ev3,
      interior T_1 T_2 ev1 ->
      interior T_3 T_4 ev2 ->
      consistent_transitivity ev1 ev2 ev3 ->
      forall m ev4 ev5 ev6,
        option_eq GT_eq (meet (proj2_ev ev1) (proj1_ev ev2)) (Some m) ->
        interior (proj1_ev ev1) m ev4 ->
        interior m (proj2_ev ev2) ev5 ->
        interior (proj1_ev ev4) (proj2_ev ev5) ev6 ->
        Ev_eq ev3 ev6.
  Proof with eauto with setoids.
    intros.
    eapply gamma_ev_compat_dual.
    split; intros.
    -  apply meet_spec_1 in H2.
       eapply gamma_completeness in H1.
       erewrite <- H1.
       eapply subseteq_trans...

       intros elem; intros...
       repeat destruct H6.
       rewrite H6.
       inversion H7.
       do 5 destruct H8.
       destruct H9.
       destruct H10.

       (* What the proof needs to obtain now is that the first projection of x is on the left and the second projection is on the right. *)
       econstructor.
       split.
       reflexivity.
       unfold Ensembles.In.
       split.
       + apply gc_ev_soundness in H3.
         inversion H10; subst.
         rewrite H14.
         change a' with
             (fst (proj1_sig (exist (fun x => static_pred (fst x) (snd x)) (a', b') x3))).
         eapply gamma_ev_spec_l.
         eapply H3.
         eexists.
         split.
         reflexivity.
         unfold Ensembles.In.
         split.
         * apply gamma_ev_spec_l in H8...
         * rewrite H2.
           simpl.
           eapply Intersection_SetIn...
           -- eapply gamma_ev_spec_r in H8...
           -- rewrite <- H16.
              inversion H11; subst...
              rewrite H15.
              eapply gamma_ev_spec_l in H9...
       + apply gc_ev_soundness in H4.
         inversion H11; subst.
         rewrite H16.
         change b' with
             (snd (proj1_sig (exist (fun x => static_pred (fst x) (snd x)) (a', b') x4))).
         eapply gamma_ev_spec_r.
         eapply H4.
         eexists.
         split.
         reflexivity.
         unfold Ensembles.In.
         split.
         * rewrite H2.
           simpl.
           eapply Intersection_SetIn...
           -- rewrite <- H14.
              inversion H10; subst...
              rewrite H18.
              eapply gamma_ev_spec_r in H8...
           -- eapply gamma_ev_spec_l in H9...
         * apply gamma_ev_spec_r in H9...
    -  apply gamma_completeness in H1.
      apply meet_spec_1 in H2.
      eapply gc_ev_optimality...
      rewrite <- H1.
      eapply subseteq_trans with (y:= (relational_composition ST_eq (gamma_ev ev4) (gamma_ev ev5)))...
       +
         eapply subseteq_trans...          
          eapply closedness...
       + eapply gc_ev_optimality with (S:= ev1) in H3.
         eapply gc_ev_optimality with (S:= ev2) in H4.
         eapply relational_composition_static_pred_mor_subset...
         all: intros elem.
         all: intros.
         all: do 2 destruct H6.
         all: destruct elem; destruct x; simpl in *.
         all: destruct H7.
         all: simpl in *.
         rewrite H2 in H7.
         2: rewrite H2 in H8.
         apply Intersection_SetIn_inv in H7...
         2: apply Intersection_SetIn_inv in H8...
         destruct H7.
         2: destruct H8.
         all: eapply gamma_ev_spec'.
         all: destruct H6.
         all: simpl in *; subst...
         all: try rewrite H6...
         all: rewrite H10...
Qed.         
  
  Theorem rc_assoc : forall (s1 s2 s3 : Ev_static_set),
      Seteq (sig_eq (pair_eq ST_eq ST_eq))
            (relational_composition ST_eq (relational_composition ST_eq s1 s2) s3)
            (relational_composition ST_eq s1 (relational_composition ST_eq s2 s3)).

  Proof with eauto with setoids.
    intros.
    split; intros elem; intros.
    - inversion H.
      destruct H0.
      exists x; split...
      clear H0.
      clear H.
      clear elem.
      inversion H1.
      clear H1.
      do 5 destruct H.
      destruct H0.
      destruct H1.
      (* Now I need to find the point in between, the one that escapes s1. *)
      inversion H.
      clear H.
      destruct H3.
      inversion H3.
      clear H3.
      destruct H4.
      do 4 destruct H3.
      destruct H4.
      destruct H5.
      (* Now's the key. *)
      unfold Ensembles.In.
      unfold relational_composition at 1.
      unfold sig_eq in H.
      destruct x5.
      inversion H; inversion H1; inversion H2; subst...
      inversion H14; subst; simpl in *.
      clear H14.
      inversion H6.
      inversion H5.
      subst.
      simpl in *.
      do 5 eexists.
      split.
      eassumption.
      split.
      2 : {
        split.
        etransitivity;[|eassumption].
        econstructor.
        etransitivity...
        symmetry.
        reflexivity.
        reflexivity.
      }
      eexists (exist _ (_, _) _).
      split.
      2 : {
        exists x0.
        do 5 eexists.
        eassumption.
        split.
        eassumption.
        split.
        all: econstructor.
        all: simpl in *.
        3 : eassumption.
        etransitivity;[|eassumption].
        reflexivity.
        all: try eassumption.
        etransitivity...
      }
      unfold sig_eq.
      reflexivity.
    -inversion H.
      destruct H0.
      exists x; split...
      clear H0.
      clear H.
      clear elem.
      inversion H1.
      clear H1.
      do 5 destruct H.
      destruct H0.
      destruct H1.
      (* Now I need to find the point in between, the one that escapes s1. *)
      inversion H0.
      clear H0.
      destruct H3.
      inversion H3.
      clear H3.
      destruct H4.
      do 4 destruct H3.
      destruct H4.
      destruct H5.
      (* Now's the key. *)
      unfold Ensembles.In.
      unfold relational_composition at 1.
      unfold sig_eq in H0.
      destruct x5.
      inversion H0; inversion H1; inversion H2; subst...
      inversion H19; subst; simpl in *.
      clear H19.
      inversion H6.
      inversion H5.
      subst.
      simpl in *.
      do 5 eexists.
      split.
      eapply In_SetIn.
      idtac...
      econstructor.
      2 : {
        split.
        eassumption.
        split.
        reflexivity.
        econstructor...
      }
      do 5 eexists.
      eassumption.
      split.
      eassumption.
      split.
      all: econstructor.
      all: simpl in *.
      all: try eassumption.
      etransitivity...

      Unshelve.
      all: simpl in *.
      rewrite H20.
      etransitivity;[|eassumption].
      rewrite H11.
      rewrite <- H18.
      rewrite H15.
      rewrite H8.
      rewrite H14...

      rewrite H11.
      rewrite H20.
      etransitivity;[|eassumption].
      rewrite <- H18.
      rewrite H15.
      rewrite H8.
      rewrite H14...

      rewrite H13.
      etransitivity;[eassumption|].
      rewrite <- H15.
      rewrite H18.
      rewrite H22.
      rewrite H7.
      rewrite H19...
Qed.      

  Theorem ct_assoc : forall (e1 e2 e3 e12 e23 el er: Ev),
      consistent_transitivity e1 e2 e12 ->
      consistent_transitivity e2 e3 e23 ->
      consistent_transitivity e12 e3 el ->
      consistent_transitivity e1 e23 er ->
      Ev_eq el er.
  Proof.
    intros.
    eapply gamma_completeness in H.
    eapply gamma_completeness in H0.
    eapply gamma_completeness in H1.
    eapply gamma_completeness in H2.
    eapply gamma_ev_compat_dual.
    rewrite <- H2.
    rewrite <- H0.
    rewrite <- H1.
    rewrite <- H.
    eapply rc_assoc.
  Qed.

  (* Sanity Checks : ec_l_exists:
                     Check that if e1 o (e2 o e3) is defined,
                     Then also (e1 o e2) is defined.
                     Thus the ec_assoc does not have
                     counterexamples because of "too strong assumptions in premises"
                     (Also must do symmetric check, in ec_r_exists)
   *)
  (* These were parameters but now they fall out by other parameters that are simpler to declare. *)
  Theorem alpha_complete : forall S, (*Required for sanity checks only *)
      Inhabited _ S ->
      exists G, alpha S G.
  Proof.
    intros.
    destruct (all_bigger_types_has_greatest_lower_bound S).
    exists x.
    econstructor; eauto.
  Qed.    
    
  Theorem alpha_implies_inhabited : forall S G, (* Required for sanity checks only *)
      alpha S G ->
      Inhabited _ S.
  Proof.
    intros.
    inversion H.
    eauto.
  Qed.
  
End AGT_Spec.


    (* Local Variables: *)
    (* mode: coq; *)
    (* coq-compile-before-require: t; *)
    (* End: *)
