Set Bullet Behavior "Strict Subproofs".

(* This system is intended to model more closely the presentation on the paper on how to generally define an AGT language,
   based on the original galois connection proofs *)

Require Import PoplLibraries.Math.
Require Import PoplLibraries.Setoid_library.
(* This file contains the Galois Connection proofs *)
   
Module Type AGT_Inputs.
  (* This definuition is based upon the section "The Essence of AGT" and is intended to mirror it. *)

  (* We require a definition of Static Types *)
  Parameter ST : Set.
     
  (* And a definition of Gradual Types. Our model is parameterized by these. *)
  Parameter GT : Set.
  
  (* We follow the "from scratch" approach, where concretization is defined by recursion on the structure of gradual types,
     and where then the precision relation is inferred. *)
  
  Parameter gamma : GT -> Ensemble ST. (* Note, Ensembles, are a representation of Sets in Coq *)
  
  Parameter meet : GT -> GT -> option GT.
    
  Parameter meet_spec_1 : forall (S_1 S_2 S_3: GT),
      (meet S_1 S_2) = (Some S_3) ->
      (gamma S_3) =
            (Ensembles.Intersection _ (gamma S_1) (gamma S_2)).

  Parameter meet_spec_2 : forall S_1 S_2,
      (meet S_1 S_2) = None ->
      (Empty_set _) =
      (Ensembles.Intersection _ (gamma S_1) (gamma S_2)).
  
  (* The definition of alpha is not needed for the mechanized portion, which depends only on the alpha for evidence. *)

    
  (* To get there, we introduce a predicate over static types *)

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
   
  Parameter Ev : Set.

  (* While we could do Evidence equivalence a parameter, I instead define it in terms of projections, as that seems to be the most useful at this point *)
  Parameter proj1_ev : Ev -> GT.
  Parameter proj2_ev : Ev -> GT.

  Definition Ev_static_set := Ensemble { x : ST & {y : ST | static_pred x y }}.
  
  Parameter gamma_ev : Ev -> Ev_static_set.

  Inductive Ev_eq : relation Ev :=
  | Ev_eq_intro : forall e e',
      Same_set _ (gamma_ev e) (gamma_ev e') ->
      Ev_eq e e'.

  Hint Constructors Ev_eq : setoids.

  Lemma Ev_eq_refl : Reflexive Ev_eq.
  Proof with eauto.
    econstructor;
    eauto with setoids.
    split; intros elem H...
  Qed.    

  Lemma Ev_eq_sym : Symmetric Ev_eq.
  Proof with eauto with setoids.
    econstructor; inversion H.
    inversion H0; subst.
    split...
  Qed.    

  Lemma Ev_eq_trans : Transitive Ev_eq.
  Proof with eauto with setoids.
    econstructor; inversion H; inversion H0...
    all: subst.
    all: inversion H1; inversion H4.
    split;
    transitivity (gamma_ev y)...
  Qed.    

  Hint Resolve Ev_eq_refl Ev_eq_sym Ev_eq_trans : setoids.
  
  Add Parametric Relation : Ev Ev_eq
      reflexivity  proved by Ev_eq_refl
      symmetry     proved by Ev_eq_sym
      transitivity proved by Ev_eq_trans
  as Ev_eq_rel.
    
  Parameter gamma_ev_spec_l : forall ev x,
      Ensembles.In _ (gamma_ev ev) x ->
      Ensembles.In _ (gamma (proj1_ev ev)) (projT1 x).

  Parameter gamma_ev_spec_r : forall ev x,
      Ensembles.In _  (gamma_ev ev) x ->
      Ensembles.In _ (gamma (proj2_ev ev)) (proj1_sig (projT2 x)).
  
  Parameter alpha_ev : Ensemble { x : ST & {y : ST | static_pred x y}} -> Ev -> Prop.

  Hint Resolve gamma_ev_spec_l gamma_ev_spec_r : setoids.
      
  (* There's a note on page 18 defining interior as follows: *)
  
  Definition interior : GT -> GT -> Ev -> Prop :=
    fun (S_1 S_2 : GT) (ev : Ev) =>
      alpha_ev
        (fun (X : {x : ST & { y : ST | static_pred x y}}) =>
           Ensembles.In _ (gamma S_1) (projT1 X) /\
           Ensembles.In _ (gamma S_2) (proj1_sig (projT2 X))
                 (* Note: There is a proof of static_pred carried in the input,
                    so I don't need to check for it here *)
        )
        ev.
  
  Definition relational_composition {A : Type} {P : A -> A -> Prop}
             (R1 : Ensemble {x : A & {y : A | P x y}})
             (R2 : Ensemble {x : A & {y : A | P x y}}) : Ensemble {x : A & { y : A | P x y }} :=
    fun (elem : {x : A & {y : A | P x y}}) =>
      exists T_2 (W_l : P (projT1 elem) T_2) (W_r : P T_2 (proj1_sig (projT2 elem))),
        Ensembles.In _ R1 (existT _ _ (exist _ _ W_l)) /\
        Ensembles.In _ R2 (existT _ _ (exist _ _ W_r)).
  
  Definition consistent_transitivity (e1 e2 e3 : Ev) : Prop :=
    alpha_ev (relational_composition (gamma_ev e1) (gamma_ev e2)) e3.
  
  Parameter forward_completeness : forall e1 e2 e3,
      consistent_transitivity e1 e2 e3 ->
      (relational_composition (gamma_ev e1) (gamma_ev e2)) =
       (gamma_ev e3).

  Parameter gc_ev_optimality : forall C S,
      Included _ C (gamma_ev S) ->
      forall S',
        alpha_ev C S' ->
        Included _ (gamma_ev S') (gamma_ev S).
  
  Parameter gc_ev_soundness : forall C S,
      alpha_ev C S ->
      Included _ C (gamma_ev S).

  Parameter proj1_ev_spec : forall ev x,
      Ensembles.In _ (gamma (proj1_ev ev)) x ->
      exists (x' : ST) (H : static_pred x x'),
        Ensembles.In _ (gamma_ev ev)
              (existT _ _ (exist _ _ H)).
  
  Parameter proj2_ev_spec : forall ev x,
      Ensembles.In _ (gamma (proj2_ev ev)) x ->
      exists (x' : ST) (H : static_pred x' x),
        Ensembles.In _  (gamma_ev ev)
              (existT _ _ (exist _ _ H)).

  Parameter closedness:
    forall S1 S2 e1 e2 e3 (H : static_pred (projT1 e1) (proj1_sig (projT2 e2))),
      Ensembles.In _ S1 e1 ->
      Ensembles.In _ S2 e2 ->      
      sigT2_eq eq eq (existT _ _ (exist _ _ H)) e3 ->
      Ensembles.In _ (relational_composition S1 S2) e3.
  
  (* This parameter is sort of a proof irrelevance parameter. *)
  Parameter gamma_ev_proof_irrelevance : forall ev x y,
      Ensembles.In _ (gamma (proj1_ev ev)) x ->
      Ensembles.In _ (gamma (proj2_ev ev)) y ->
      forall (H : static_pred x y),
        Ensembles.In _ (gamma_ev ev) (existT _ _ (exist _ _ H)).

  Hint Resolve forward_completeness gc_ev_optimality gc_ev_soundness proj1_ev_spec proj2_ev_spec : setoids.

End AGT_Inputs.

Module AGT_Spec_simpl (AGT : AGT_Inputs).
  Import AGT.

  Hint Constructors Ensembles.Intersection : setoids.
  Hint Resolve  Intersection_Empty_set_r Intersection_Empty_set_l : setoids.
  Lemma Intersection_assoc {A : Type}: forall x y z,
      Ensembles.Intersection A x (Ensembles.Intersection _ y z) =
      Ensembles.Intersection _ (Ensembles.Intersection _ x y) z.
  Proof with eauto with setoids.
    intros.
    eapply Extensionality_Ensembles.
    split; intros elem H; inversion H; subst...
    inversion H1; subst...
    inversion H0; subst...
  Qed.    
  
  Theorem alpha_ev_li : forall R_1 R_2 S_1 S_2,
      Included _ R_1 R_2 ->
      alpha_ev R_1 S_1 ->
      alpha_ev R_2 S_2 ->
      Included _ (gamma_ev S_1)
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

  Add Parametric Morphism A P: (@relational_composition A P)
      with signature (Included {x : A & {y : A | P x y}}) ==>
                     (Included {x : A & {y : A | P x y}}) ==>
                     (Included {x : A & {y : A | P x y}}) as relational_composition_static_pred_mor_subset.
  Proof with eauto with setoids.
    intros.
    all: intro elem.
    all: intros.
    all: repeat destruct  H1.
    econstructor.
    exists x2.
    exists x3.
    split...
  Qed.    

  Add Parametric Morphism A P: (@relational_composition A P)
      with signature (Same_set {x : A & {y : A | P x y}}) ==>
                     (Same_set {x : A & {y : A | P x y}}) ==>
                     (Same_set {x : A & {y : A | P x y}}) as relational_composition_static_pred_mor.
  Proof with eauto with setoids.
    intros.
    econstructor.
    all: intro elem.
    all: intros.
    all: repeat destruct  H1.
    all: econstructor.
    all: exists x2.
    all: exists x3.
    all: split...
    eapply H...
    eapply H0...
    eapply H...
    eapply H0...
  Qed.      
  
  Theorem ct_via_interior_def : forall T_1 T_2 T_3 T_4 ev1 ev2 ev3,
      interior T_1 T_2 ev1 ->
      interior T_3 T_4 ev2 ->
      consistent_transitivity ev1 ev2 ev3 ->
      forall m ev4 ev5 ev6,
        (meet (proj2_ev ev1) (proj1_ev ev2)) = (Some m) ->
        interior (proj1_ev ev1) m ev4 ->
        interior m (proj2_ev ev2) ev5 ->
        interior (proj1_ev ev4) (proj2_ev ev5) ev6 ->
        Ev_eq ev3 ev6.
  Proof with eauto with setoids.
    intros.
    econstructor.
    split; intros.
    -  apply meet_spec_1 in H2.
       eapply forward_completeness in H1.
       erewrite <- H1.
       etransitivity...
       intros elem; intros...
       repeat destruct H6.
       split.
       + apply gc_ev_soundness in H3.
         change (projT1 elem) with (projT1 (existT (fun x => {y | static_pred x y}) (projT1 elem) (exist _ _ x0))).
         eapply gamma_ev_spec_l.
         eapply H3.
         split.
         * eapply gamma_ev_spec_l in H6...
         * rewrite H2.
           econstructor.
           -- eapply gamma_ev_spec_r in H6...
           -- eapply gamma_ev_spec_l in H7...
       + apply gc_ev_soundness in H4.
         change (proj1_sig (projT2 elem))
                with (proj1_sig (projT2 (existT (fun x => {y | static_pred x y}) _ (exist _ _ x1)))).
         eapply gamma_ev_spec_r.
         eapply H4.
         split...
         rewrite H2.
         econstructor.
         * eapply gamma_ev_spec_r in H6...
         * eapply gamma_ev_spec_l in H7...
    - apply meet_spec_1 in H2.
      apply forward_completeness in H1.
      eapply gc_ev_optimality...
      rewrite <-H1.
      clear H1.
      clear H5.
      intros elem Hin.
      destruct Hin.
      destruct elem.
      destruct s.      
      eapply proj1_ev_spec in H1.
      do 2 destruct H1.
      eapply gc_ev_optimality with (S:=ev1) in H1.
      (*3 : eapply ev_self_interior.*)
      3 : eapply H3.
      eapply proj2_ev_spec in H5.
      do 2 destruct H5.
      eapply gc_ev_optimality with (S:=ev2) in H5.
      (*3 : eapply ev_self_interior.*)
      3 : eapply H4.
      + eapply closedness...
        unfold sigT2_eq...
        Unshelve.
        transitivity x...
      + intros elem Hin.
        destruct Hin.
        destruct elem.
        destruct s0.
        eapply gamma_ev_proof_irrelevance...
        rewrite H2 in H6.
        inversion H6...
      + intros elem Hin.
        destruct Hin.
        destruct elem.
        destruct s0.
        eapply gamma_ev_proof_irrelevance...
        rewrite H2 in H7.
        inversion H7...
Qed.         
  
  Theorem rc_assoc : forall (s1 s2 s3 : Ev_static_set),
      Same_set
        _
        (relational_composition (relational_composition s1 s2) s3)
        (relational_composition s1 (relational_composition s2 s3)).
  Proof with eauto with setoids.
    intros.
    split; intros elem; intros.
    - inversion H.
      destruct H0.
      do 5 destruct H0.
      destruct H0.
      (* Now I need to find the point in between, the one that escapes s1. *)
      simpl in *.
      exists x2.
      exists x3.
      exists (static_pred_trans _ _ _ x4 x1).
      split...
      exists x.
      simpl.
      exists x4.
      exists x1.
      split...
    - inversion H.
      do 3 destruct H0.
      do 4 destruct H1.
      simpl in *.
      exists x2.
      exists (static_pred_trans _ _ _ x0 x3).
      exists x4.
      split...
      exists x.
      simpl.
      exists x0.
      exists x3.
      split...
  Qed.

  Theorem ct_assoc : forall (e1 e2 e3 e12 e23 el er: Ev),
      consistent_transitivity e1 e2 e12 ->
      consistent_transitivity e2 e3 e23 ->
      consistent_transitivity e12 e3 el ->
      consistent_transitivity e1 e23 er ->
      Ev_eq el er.
  Proof.
    intros.
    eapply forward_completeness in H.
    eapply forward_completeness in H0.
    eapply forward_completeness in H1.
    eapply forward_completeness in H2.
    econstructor.
    rewrite <- H2.
    rewrite <- H0.
    rewrite <- H1.
    rewrite <- H.
    eapply rc_assoc.
  Qed.

End AGT_Spec_simpl.


    (* Local Variables: *)
    (* mode: coq; *)
    (* coq-compile-before-require: t; *)
    (* End: *)
