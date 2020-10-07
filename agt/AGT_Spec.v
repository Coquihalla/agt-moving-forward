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
  
  (*Parameter gamma_compat_dual :
    forall x x' : GT,
      (gamma x) = (gamma x') ->
      x = x'.*)
  (*
  Definition partial_gamma (x : option GT) : Ensemble ST :=
    match x with
    | Some x => gamma x
    | None => Empty_set _
    end.
    *)  
  (*Definition less_imprecise (S_1 S_2 : GT) :=
    Included _ (gamma S_1) (gamma S_2). (* Proposition 3.1 *)
  *)
  (* While we could have followed a "define alpha as well" approach,
     we will try here to be as consistent with the paper as possible,
     which relies instead on a definition of meet and generates for you a definition of alpha, which is the one we will use.
   *)

  Parameter meet : GT -> GT -> option GT.

  (* Might be necessary, but not yet.
     Parameter meet_sym : forall (S_1 S_2 : GT),
      meet S_1 S_2 = meet S_2 S_1.
   *)
    
  Parameter meet_spec_1 : forall (S_1 S_2 S_3: GT),
      (meet S_1 S_2) = (Some S_3) ->
      (gamma S_3) =
            (Ensembles.Intersection _ (gamma S_1) (gamma S_2)).

  Parameter meet_spec_2 : forall S_1 S_2,
      (meet S_1 S_2) = None ->
      (Empty_set _) =
      (Ensembles.Intersection _ (gamma S_1) (gamma S_2)).
  
  (* Our spec for alpha is according to the paper : *)

  (* These definitions of lower_bound and greatest lower bound are 
     not necessary, but I keep them here for reference : *)
(*
  Definition all_bigger_types (C : Ensemble ST) : Ensemble GT := (fun X => Included _ C (gamma X)).
  
    (* Backtracking : I need to go back and make better and stronger use of the generalized rewriting features.  In particular, I do need stuff to work in previous cases (For example, subseteq must be made a morphism, etc. *)
  
  Definition lower_bound (S : Ensemble GT) (a : GT) : Prop :=
    forall (x : GT), Ensembles.In _ S x -> less_imprecise a x.
  
  Definition greatest_lower_bound (S : Ensemble GT) (a : GT) : Prop :=
    (lower_bound S a) /\ (forall k, lower_bound S k -> less_imprecise k a).
*)
  (*
  (* I think this is a key that we have not expressed before. *)
  Parameter all_bigger_types_has_greatest_lower_bound :
    forall (C : Ensemble ST),
    exists a,
      (greatest_lower_bound (all_bigger_types C) a)
  .*)
    
  (*Parameter glb_is_minimum : forall (C : Ensemble ST),
      forall a,
        (greatest_lower_bound (all_bigger_types C) a) ->
        Ensembles.In _ (all_bigger_types C) a.*)
  
  (*Inductive alpha : Ensemble ST -> GT -> Prop :=
  | alpha_constructor :
      forall C out,
        (* out is a lower bound *)
        Inhabited _ C ->
        greatest_lower_bound (all_bigger_types C) out ->
        alpha C out.

  Hint Constructors alpha : setoids.*)
    
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
 
  (*Definition gradual_pred (S_1 S_2 : GT) : Prop :=
    exists T_1 T_2,
      Ensembles.In _ (gamma S_1) T_1 /\
      Ensembles.In _ (gamma S_2) T_2 /\
      static_pred T_1 T_2. (* Proposition 2.2 *)
*)
  
  (*Theorem gc_soundness : forall C S,
      alpha C S ->
      Included _ C (gamma S).
  Proof.
    intros.
    inversion H; subst.
    inversion H1.
    unfold lower_bound in H2.
    eapply glb_is_minimum in H1.
    eauto.
  Qed.*)

  (*Hint Resolve gc_soundness : setoids.*)
  
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
    
  (*Hint Resolve gamma_ev_compat : setoids.*)
  (*
  Add Parametric Morphism : gamma_ev
      with signature Ev_eq ==> eq as gamma_ev_mor.
  Proof.
    exact gamma_ev_compat.
  Qed.*)

  Parameter gamma_ev_spec_l : forall ev x,
      Ensembles.In _ (gamma_ev ev) x ->
      Ensembles.In _ (gamma (proj1_ev ev)) (projT1 x).

  Parameter gamma_ev_spec_r : forall ev x,
      Ensembles.In _  (gamma_ev ev) x ->
      Ensembles.In _ (gamma (proj2_ev ev)) (proj1_sig (projT2 x)).
  
  Parameter alpha_ev : Ensemble { x : ST & {y : ST | static_pred x y}} -> Ev -> Prop.

  (*Parameter alpha_ev_compat : forall (s1 s2 : Ensemble { x : ST & { y : ST | static_pred  x y }}),
      s1 = s2 ->
      forall (e1 e2 : Ev),
        Ev_eq e1 e2 ->
        (alpha_ev s1 e1 <-> alpha_ev s2 e2).*)

  Hint Resolve gamma_ev_spec_l gamma_ev_spec_r : setoids.
  
  (*Add Parametric Morphism : alpha_ev
      with signature (eq ==> Ev_eq ==> iff) as alpha_ev_mor.
  Proof.
    intros.
    eapply alpha_ev_compat; auto.
  Qed.*)
    
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

  (*Parameter ev_self_interior : forall (e : Ev),
      interior (proj1_ev e) (proj2_ev e) e.

  Hint Resolve ev_self_interior : setoids.*)

  (* This definition must make use of equality relations over A as well. *)
  
  Definition relational_composition {A : Type} {P : A -> A -> Prop}
             (R1 : Ensemble {x : A & {y : A | P x y}})
             (R2 : Ensemble {x : A & {y : A | P x y}}) : Ensemble {x : A & { y : A | P x y }} :=
    fun (elem : {x : A & {y : A | P x y}}) =>
      exists T_2 (W_l : P (projT1 elem) T_2) (W_r : P T_2 (proj1_sig (projT2 elem))),
        Ensembles.In _ R1 (existT _ _ (exist _ _ W_l)) /\
        Ensembles.In _ R2 (existT _ _ (exist _ _ W_r)).
  
  Definition consistent_transitivity (e1 e2 e3 : Ev) : Prop :=
    (* Id+ is implicit through the requirement of inhabitance in alpha *)
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

  (* Note: This line is the likely the most advanced use of Generalized Rewriting and morphisms that we have so far,
     BECAUSE WE NEED TO INTRODUCE DEPENDENCY FOR STATIC_PRED!
     Thus we cannot just use ==>, which is syntactic sugar for non-dependent "respectful"        morphisms.
     (See re spectful in Coq.Classes.Morphisms)
     
     Thus we must instead use here directly a respectful_hetero *)

  (* Key for this is understanding the following expansion.

     R ==> R' expands to (where R : relation A and R': relation B, producing relation (A -> B))
     (@respectful _ _ (R %signature) (R'%signature)), which expands to
     Eval compute in @respectful_hetero A A (fun _ => B) (fun _ => B) R (fun _ _ => R').
   
   Therefore, what originally should have been something like
   (pair_eq ST_eq ST_eq) ==> //dependent relation on static_pred over the terms of pair_eq// ==> (@sig_eq ...)

   Becomes: *)

(*  Instance exist_iff_morphism :
    Proper (@respectful_hetero _ _
                               (*(fun x => (static_pred (fst x) (snd x)) -> {x : ST * ST | static_pred (fst x) (snd x)})*) _
                               (*(fun x => (static_pred (fst x) (snd x)) -> {x : ST * ST | static_pred (fst x) (snd x)})*) _
                               (pair_eq ST_eq ST_eq)
                               (** must have type
                                   forall x y : ST * ST,
                                   (fun x0 : ST * ST => static_pred (fst x0) (snd x0) -> {x1 : ST * ST | static_pred (fst x1) (snd x1)}) x ->
                                   (fun x0 : ST * ST => static_pred (fst x0) (snd x0) -> {x1 : ST * ST | static_pred (fst x1) (snd x1)}) y -> Prop
                                **)
                               (fun x y =>
                                  (**
                                     (sig_eq (pair_eq ST_eq ST_eq)) is the destination type we want, we need to make by hand, something of the likes of
                                     iff ==> (sig_eq (pair_eq ST_eq ST_eq))... I thus need to write something lie
                                   **)
                                  (@respectful_hetero _ _ _ _ (fun H H0 => ST_eq (fst x) (fst y) /\ ST_eq (snd x) (snd y))
                                                      (fun _ _ => (sig_eq (pair_eq ST_eq ST_eq)))))
           )
           (@exist (ST*ST)%type (fun x => static_pred (fst x) (snd x))) .*)

(*  Instance exist_iff_morphism :
    Proper ((pair_eq ST_eq ST_eq) >==> { x & y } ((fun H H0 => ST_eq (fst x) (fst y) /\ ST_eq (snd x) (snd y)) >==> { _ & _ } (@sig_eq _ (fun x => static_pred (fst x) (snd x)) (pair_eq ST_eq ST_eq))))
           (@exist (ST*ST)%type (fun x => static_pred (fst x) (snd x))).
  Proof.
    simpl_relation.
  Qed.
 *)

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

  (*
  Theorem meet_assoc : forall (S_1 S_2 S_3 : GT),
      partial_gamma (match (meet S_1 S_2) with
                     | Some S_12 => meet S_12 S_3
                     | None => None
                     end)
      =
      partial_gamma (match (meet S_2 S_3) with
                     | Some S_23 => meet S_1 S_23
                     | None => None
                     end).
  Proof with eauto with setoids.
    intros.

    repeat match goal with
           | [ |- context[meet ?A ?B]] =>
             let H' := fresh in destruct (meet A B) eqn:H'(*;*)
             (*let H := fresh in pose proof (option_eq_refl GT_eq_refl (meet A B)) as H;
                                 rewrite H' in H at 2;
                                 clear H'*)
           end.

      
    all: repeat match goal with
                | [ H : _ _ _ (Some _) |- _ ]=> apply meet_spec_1 in H
                | [ H : _ _ _ None |- _]  => apply meet_spec_2 in H
                end.

    all: try reflexivity.
    all: simpl.
    - rewrite H0.
      rewrite H2.
      rewrite H.
      rewrite H1.
      rewrite Intersection_assoc...
    - rewrite H0.
      rewrite H2.
      rewrite H.
      rewrite H1.
      rewrite Intersection_assoc...
    - rewrite H0.
      rewrite H.
      rewrite <- Intersection_assoc...
      rewrite <- H1...
    - rewrite H2.
      rewrite H1.
      rewrite Intersection_assoc...
      rewrite H in H0...
    - rewrite H1.
      rewrite H0.
      rewrite Intersection_assoc...
      rewrite <- H...
  Qed.  
  *)
  (*(* Proposition 3.2 should follow *)
  Theorem gc_optimality : forall C S,
      Included _ C (gamma S) ->
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
  Qed.    *)
  
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

  (* This theorem is unused, maybe will be relevant later. *)
  (*Theorem glb_membership : forall A T,
      greatest_lower_bound A T ->
      forall y ,  Ensembles.In _ A y ->
                  Included _ (gamma T) (gamma y).
  Proof with eauto with setoids.
    intros.
    inversion H.
    apply H1 in H0...
  Qed.        
  *)
  (*Lemma meet_left : forall S_1 S_2 S_3,
      (meet S_1 S_2) = (Some S_3) ->
      less_imprecise S_3 S_1.
  Proof with eauto with setoids.
    intros.
    eapply meet_spec_1 in H.
    unfold less_imprecise.
    rewrite H.
    intros elem.
    intros.
    inversion H0...
  Qed.    

  Lemma meet_right : forall S_1 S_2 S_3,
      (meet S_1 S_2) = (Some S_3) ->
      less_imprecise S_3 S_2.
  Proof with eauto with setoids.
    intros.
    eapply meet_spec_1 in H.
    unfold less_imprecise.
    rewrite H.
    intros elem.
    intros.
    inversion H0...
  Qed.*)

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

  (* (* I am not sure what this note was for anymore, but I'll keep it for now in case I remember: *)
     Now, after we have done the equivalence proof, we can revisit the
     "gamma completeness suffices for associativity" proof : 

     BIG NOTE: I might be able to get away WITHOUT having to prove alpha is partial function
     If I keep defining evidence equivalence as extensionality of gammas.
*)
  
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

  (* Sanity Checks : ec_l_exists:
                     Check that if e1 o (e2 o e3) is defined,
                     Then also (e1 o e2) is defined.
                     Thus the ec_assoc does not have
                     counterexamples because of "too strong assumptions in premises"
                     (Also must do symmetric check, in ec_r_exists)

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

    

  Theorem ec_r_exists : forall e1 e2 e12 e3 e4,
      consistent_transitivity e1 e2 e12 ->
      consistent_transitivity e12 e3 e4 ->
      exists e5, consistent_transitivity e2 e3 e5.
  Proof with eauto with setoids.
    intros.
    unfold consistent_transitivity in *.
    unfold relational_composition in H0.
    apply gc_ev_optimality with (S:=e2) in H.
    enough (exists e, alpha_ev (relational_composition (gamma_ev e12) (gamma_ev e3)) e).
    - destruct H1.
      pose proof (gc_ev_soundness) as sound.
      pose proof (gc_ev_optimality) as opt.
      eapply gc_ev_soundness in H1.
      
    
    

    
    inversion H.
    
    apply forward_completeness in H.
    apply forward_completeness in H0.
    subst.
    enough (Inhabited _ (relational_composition (gamma_ev e2) (gamma_ev e3))).
    unfold consistent_transitivity.
    destruct (all_bigger_types_has_greatest_lower_bound
         (SetMap (relational_composition (gamma_ev e2) (gamma_ev e3))
                 (fun x : {x : ST & {y : ST | static_pred x y}} =>
                    match x with
                     | existT _ x0 _ => x0
                    end))).
    destruct (all_bigger_types_has_greatest_lower_bound
      (SetMap (relational_composition (gamma_ev e2) (gamma_ev e3))
                 (fun x : {x : ST & {y : ST | static_pred x y}} =>
                    match x with
                    | existT _ _ (exist _ x1 _) => x1
                    end))).
    econstructor.
    inversion H2.

    
      econstructor.

    - (* Use forward_completeness here *)
      
      simpl in *.
      inversion H6.
      inversion H1.
      destruct x.
      repeat destruct H.
      simpl in *.
      rewrite rc_assoc in H4.
      inversion H4.
      repeat destruct H.
      econstructor; eauto.
      Unshelve.
      eassumption.
      simpl.
      econstructor; eauto.
      inversion H4.
      destruct x1.
      repeat econstructor; eauto.
      econstructor; eauto.
      inversion H4.
      destruct x1.
      repeat econstructor; eauto.
  Qed.
    
  Theorem ec_l_exists : forall e1 e2 e3 e23 e4,
      consistent_transitivity e2 e3 e23 ->
      consistent_transitivity e1 e23 e4 ->
      exists e5, consistent_transitivity e1 e2 e5.
  Proof.
    intros.
    inversion H.
    inversion H0.
    pose proof (forward_completeness _ _ _ H).
    pose proof (forward_completeness _ _ _ H0).
    clear H.
    clear H0.
    (* Note: It's necessary to do this BEFORE the substitution !*)
    clear H10.
    rewrite <- H11 in H6.
    rewrite <- rc_assoc in H6.
    subst.
    enough (Inhabited _ (relational_composition (gamma_ev e1) (gamma_ev e2))).
    destruct (all_bigger_types_has_greatest_lower_bound
      (SetPMap (relational_composition (gamma_ev e1) (gamma_ev e2))
         (fun x : {x : ST * ST | static_pred (fst x) (snd x)} =>
          let (x0, _) := x in Some (fst x0)))).
    destruct (all_bigger_types_has_greatest_lower_bound
      (SetPMap (relational_composition (gamma_ev e1) (gamma_ev e2))
         (fun x : {x : ST * ST | static_pred (fst x) (snd x)} =>
          let (x0, _) := x in Some (snd x0)))).

    econstructor.
    econstructor.
    inversion H6.
    - unfold In in H.
      unfold relational_composition at 1 in H.
      destruct x.
      destruct H.
      destruct H.
      destruct H.
      destruct H.
      econstructor; eauto.
      Unshelve.
      eassumption.
      simpl.
      econstructor; eauto.
      inversion H.
      destruct x1.
      repeat econstructor; eauto.
      econstructor; eauto.
      inversion H.
      destruct x1.
      repeat econstructor; eauto.
Qed.
*)
    
End AGT_Spec_simpl.


    (* Local Variables: *)
    (* mode: coq; *)
    (* coq-compile-before-require: t; *)
    (* End: *)
