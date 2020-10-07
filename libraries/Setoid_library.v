Require Export Coq.Sets.Powerset_facts.
Require Export Setoid.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Lists.List.
Export Coq.Lists.List.ListNotations.
Require Export Relation_Definitions.

Create HintDb setoids discriminated.

(* Setoid library *)

(* This development introduces a series of parametric setoids that can be used as "setoid combinators" to generate more general Equivalences. *)

(* Option_eq : generates an equivalence for type option A based on an equivalence on A (Nones are equivalent and the equivalence "passes through" Some)
 *)

Inductive option_eq {A : Type} (eq : relation A ) : relation (option A) :=
| op_eq_some : forall a b,
    eq a b ->
    option_eq eq (Some a) (Some b)
| op_eq_none : option_eq eq None None.

(* Equivalence lemmas for option_eq : *)

Lemma option_eq_refl {E : Type} {eq : relation E} :
  (Reflexive eq) -> Reflexive (option_eq eq).
Proof.
  intros.
  intros x.
  destruct x; econstructor.
  eauto.
Qed.

Lemma option_eq_sym {E : Type} {eq : relation E} :
  (Symmetric eq) -> Symmetric (option_eq eq).
Proof.
  intros.
  intros x y.
  intros.
  inversion H0; subst;
    econstructor; eauto.
Qed.

Lemma option_eq_trans {E : Type} {eq : relation E} :
  (Transitive eq) -> Transitive (option_eq eq).
Proof.
  intros.
  intros x y z.
  intros.
  inversion H0; inversion H1; subst; try congruence; 
    econstructor; eauto.
  inversion H6; subst; eauto.
Qed.

Hint Resolve option_eq_refl option_eq_sym option_eq_trans : setoids.

Hint Constructors Equivalence option_eq: setoids.

Instance option_eq_rel (E : Type) (rel : relation E) (Equiv : Equivalence rel)  : Equivalence (option_eq rel).
inversion Equiv.
eauto with setoids.
Defined.

Add Parametric Morphism A eqA: Some
    with signature eqA ==> (@option_eq A eqA) as option_eq_mor.
Proof with eauto with setoids.
  intros...
Qed.

(* pair_rel is an equivalence relation on pairs parameterized on an equivalence on each of the pair elements: *)

Inductive pair_eq { A B : Type} (eqA : relation A) (eqB: relation B) : relation (A * B) :=
| pair_eq_intro:
    forall (a a' : A) (b b' : B),
      eqA a a' ->
      eqB b b' ->
      pair_eq eqA eqB (a,b) (a',b').

Hint Constructors pair_eq : setoids.

Lemma pair_eq_refl {A B : Type} (eqA : relation A) (eqB : relation B) :
  Reflexive eqA ->
  Reflexive eqB ->
  Reflexive (pair_eq eqA eqB).
Proof.
  intros.
  intro x.
  destruct x.
  eauto with setoids.
Qed.

Lemma pair_eq_sym {A B : Type} (eqA : relation A) (eqB : relation B) :
  Symmetric eqA ->
  Symmetric eqB ->
  Symmetric (pair_eq eqA eqB).
Proof.
  intros.
  intros x y H'.
  inversion H'.
  eauto with setoids.
Qed.


Lemma pair_eq_trans {A B : Type} (eqA : relation A) (eqB : relation B) :
  Transitive eqA ->
  Transitive eqB ->
  Transitive (pair_eq eqA eqB).
Proof.
  intros.
  intros x y z.
  destruct x;
    destruct y;
    destruct z.
  intros.
  inversion H1.
  inversion H2.
  subst.
  eauto with setoids.
Qed.    

Hint Resolve pair_eq_refl pair_eq_sym pair_eq_trans : setoids.

Instance pair_eq_rel (A B : Type) (relA : relation A) (relB : relation B) (Equiv_a : Equivalence relA) (Equiv_b : Equivalence relB)  : Equivalence (pair_eq relA relB).
inversion Equiv_a.
inversion Equiv_b.
eauto with setoids.
Defined.

Hint Constructors prod : setoids.

Add Parametric Morphism A B rel1 rel2 : pair
    with signature rel1 ==> rel2 ==> @pair_eq A B rel1 rel2 as pair_mor.
Proof with eauto with setoids.
  intros...
Qed.


(* Definitions of Set containment and equivalence compatible with an equivalence among members. *)

Definition SetIn {E : Type} (eq : relation E) (set : Ensemble E) (elem : E) : Prop :=
  exists y, eq elem y /\ Ensembles.In _ set y.

Definition Subseteq {E : Type} (eq : relation E) : relation (Ensemble E) :=
  fun (A B : Ensemble E) =>   (forall x, SetIn eq A x -> SetIn eq B x).

Lemma subseteq_refl {E : Type} {eq : relation E} :
  Reflexive eq -> Reflexive (Subseteq eq).
Proof.
  intros.
  intro x.
  intro x'.
  intros.
  inversion H0...
  exists x0; eauto.
Qed.    

Lemma subseteq_trans {E : Type} {eq : relation E } :
  Transitive eq -> Transitive (Subseteq eq).
Proof with eauto.
  intros.
  intros x y z.
  intros.
  intro x'.
  intros...
Qed.    

Hint Resolve subseteq_refl subseteq_trans : setoids.

Instance subseteq_refl_rel {E : Type} {eqe : relation E} {refl : Reflexive eqe} : Reflexive (Subseteq eqe).
Proof with eauto with setoids.
  intros...
Qed.

Instance subseteq_trans_rel {E : Type} {eqe : relation E} {refl : Transitive eqe} : Transitive (Subseteq eqe).
Proof with eauto with setoids.
  intros...
Qed.

(* Note : This definition is equivalent to a Setoid-compatible Extensionality_Ensembles Axiom.  If you use Seteq, you do not need the axiom of course. *)
Definition Seteq {E : Type} (eq : relation E) : relation (Ensemble E) :=
  fun ( A B : Ensemble E) =>
    (Subseteq eq A B) /\ (Subseteq eq B A).

(* Subset is compatible with set equality: *)
Add Parametric Morphism E e `{Transitive E e}: ( @Subseteq E e) 
    with signature (Seteq e) ==> (Seteq e) ==> iff as subseteq_eq_mor.
Proof with eauto with setoids.
  intros.
  split; intros; intro z ; intros.
  - apply H0 in H3.
    apply H2 in H3.
    apply H1 in H3...
  - apply H0 in H3.
    apply H2 in H3.
    eapply H1 in H3...
Qed.      

(* SetIn is compatible with Seteq *)
Add Parametric Morphism E e `{Equivalence E e} : (@SetIn E e)
  with signature (Subseteq e) ==> e ==> (fun A B : Prop=> A -> B) as SetIn_subseteq_mor.
Proof with eauto with setoids.
  intros.
  apply H0 in H2; symmetry in H1...
  inversion H2.
  destruct H3.
  econstructor.
  split;[| eassumption].
  etransitivity...
Qed.  
  
Add Parametric Morphism E e `{Equivalence E e} : (@SetIn E e)
  with signature (Seteq e) ==> e ==> iff as SetIn_seteq_mor.
Proof with eauto with setoids.
  intros.
  split; intros.
  all: eapply SetIn_subseteq_mor...
  all: inversion H0...
  symmetry...
Qed.  


Lemma Seteq_refl {E : Type} {eq : relation E} :
  (Reflexive eq) -> Reflexive (Seteq eq).
Proof with eauto with setoids.
  intros.
  intros x.
  split;
    intro x'...
Qed.

Lemma Seteq_sym {E : Type} {eq : relation E} :
  Symmetric (Seteq eq).
Proof with eauto with setoids.
  intros.
  intros x y.
  split; eapply H...
Qed.

Lemma Seteq_trans {E : Type} {eq : relation E} :
  Transitive eq -> Transitive (Seteq eq).
Proof with eauto with setoids.
  intros.
  intros x y z.
  intros.
  split; intros x'; intros...
  - apply H0 in H2.
    apply H1 in H2...
  - apply H1 in H2.
    apply H0 in H2...
Qed.

Hint Resolve Seteq_refl Seteq_sym Seteq_trans : setoids.

Instance Seteq_rel (E : Type) (rel : relation E) (Equiv : Equivalence rel)  : Equivalence (Seteq rel).
Proof with eauto with setoids.
  inversion Equiv...
Defined.

Add Parametric Morphism A eq (Equiv: Equivalence eq): (@Seteq A eq)
    with signature (eq ==> iff) ==> (eq ==> iff) ==> iff as Seteq_fun_mor.
Proof with (eauto with setoids).
  intros.
  split; intros.
  all: split.
  all: intros elem; intros.
  all: repeat destruct H2.
  - apply H in H2.
    apply H2 in H3.
    assert (SetIn eq x elem) by
        (eexists; split;[| eassumption]; reflexivity).
    apply H1 in H4.
    repeat destruct H4.
    symmetry in H4.
    apply H0 in H4.
    apply H4 in H5.
    eexists; split;[|eassumption]; reflexivity.
  - apply H0 in H2.
    apply H2 in H3.
    assert (SetIn eq x0 elem) by
        (eexists; split;[| eassumption]; reflexivity).
    apply H1 in H4.
    repeat destruct H4.
    symmetry in H4.
    apply H in H4.
    apply H4 in H5.
    eexists;split;[reflexivity | eassumption].
  - symmetry in H2.
    apply H in H2.
    apply H2 in H3.
    assert (SetIn eq y elem) by
        (eexists; split;[| eassumption]; reflexivity).
    apply H1 in H4.
    repeat destruct H4.
    apply H0 in H4.
    apply H4 in H5.
    eexists; split;[|eassumption]; reflexivity.    
  - symmetry in H2.
    apply H0 in H2.
    apply H2 in H3.
    assert (SetIn eq y0 elem) by
        (eexists; split;[| eassumption]; reflexivity).
    apply H1 in H4.
    repeat destruct H4.
    apply H in H4.
    apply H4 in H5.
    eexists; split;[|eassumption]; reflexivity.    
Qed.

Hint Resolve iff_equivalence : setoids.

(* Just like map works over lists, SetMap works over Ensembles. *)

Inductive SetMap {A B : Type} (st : Ensemble A) (f : A -> B): Ensemble B :=
| setmap_intro : forall x, Ensembles.In _ st x -> Ensembles.In _ (SetMap st f) (f x).

Hint Constructors SetMap : setoids.

Theorem SetMap_In {A B : Type} {st : Ensemble A} {f : A -> B} (eqA : relation A) (eqB: relation B) `{Reflexive A eqA} `{Reflexive B eqB} :
  (forall x y, eqA x y -> eqB (f x) (f y)) ->
  forall x,
    SetIn eqA st x ->
    SetIn eqB (SetMap st f) (f x).
Proof with eauto with setoids.
  intros.
  repeat destruct H2...
  eexists.
  split;[|econstructor; eassumption]...
Qed.  

Hint Resolve SetMap_In : setoids.

Add Parametric Morphism A B (eqA : relation A) (eqB :relation B) (equiv_A : Equivalence eqA) (equiv_B : Equivalence eqB): (@SetMap A B )
    with signature (Subseteq eqA) ==> (eqA ==> eqB) ==> (Subseteq eqB) as SetMap_subset_mor.
Proof with eauto with setoids.
  intros.
  intros elem; intros.
  inversion H1.
  destruct H2.
  inversion H3.
  subst.
  assert (SetIn eqA x x2) by (eexists;split;[reflexivity|eauto with setoids]).
  apply H in H5.
  repeat destruct H5.
  econstructor.
  split;[|econstructor; eassumption]...
  etransitivity...
Qed.      

Add Parametric Morphism A B (eqA : relation A) (eqB :relation B) (equiv_A : Equivalence eqA) (equiv_B : Equivalence eqB): (@SetMap A B )
    with signature (Seteq eqA) ==> (eqA ==> eqB) ==> (Seteq eqB) as SetMap_mor.
Proof with eauto with setoids.
  intros.
  split; eapply SetMap_subset_mor...
  all: inversion H...
  intros elem; intros...
  symmetry.
  eapply H0.
  symmetry...
Qed.    

Inductive SetMap2 {A : Type} (f : A -> A -> A) (dom cod : Ensemble A) : Ensemble A :=
| setmap2_intro :
    forall x y, Ensembles.In _ dom x -> Ensembles.In _ cod y  -> Ensembles.In _ (SetMap2 f dom cod) (f x y).


Theorem SetMap2_In {A: Type} {st st' : Ensemble A} {f : A -> A -> A} (eqA : relation A) `{Reflexive A eqA} :
  (forall x x' y y', eqA x x' -> eqA y y' -> eqA (f x y) (f x' y')) ->
  forall x y,
    SetIn eqA st x ->
    SetIn eqA st' y ->
    SetIn eqA (SetMap2 f st st') (f x y).
Proof with eauto with setoids.
  intros.
  repeat destruct H1...
  repeat destruct H2...
  eexists.
  split;[|econstructor; eassumption]...
Qed.  

Hint Resolve SetMap2_In : setoids.

Lemma In_SetIn {E : Type} (eqb: relation E) `{Reflexive E eqb} :
  forall s e,
    Ensembles.In _ s e ->
    SetIn eqb s e.
Proof.
  intros.
  eexists.
  split;[| eassumption].
  reflexivity.
Qed.


Add Parametric Morphism A (eqA : relation A) (equiv_A : Equivalence eqA) : (@SetMap2 A)
    with signature (eqA ==> eqA ==> eqA) ==> (Subseteq eqA) ==> (Subseteq eqA) ==> (Subseteq eqA) as SetMap2_subset_mor.
Proof with eauto with setoids.
  intros.
  intros elem.
  intros.
  repeat destruct H2.
  inversion H3;
  subst.
  assert (eqA x3 x3)by reflexivity.
  assert (eqA y2 y2) by reflexivity.
  inversion equiv_A.
  rewrite H2.
  apply In_SetIn with (eqb := eqA) in H5...
  apply In_SetIn with (eqb := eqA)in H4...
  apply H0 in H4.
  apply H1 in H5.
  apply H in H6.
  apply H6 in H7.
  rewrite H7.
  repeat destruct H4.
  repeat destruct H5.
  eexists.
  split.
  2 : {
    econstructor...
  } 
  rewrite <- H7.
  eapply H...
Qed.    

Add Parametric Morphism A (eqA : relation A) (equiv_A : Equivalence eqA) : (@SetMap2 A)
    with signature (eqA ==> eqA ==> eqA) ==> (Seteq eqA) ==> (Seteq eqA) ==> (Seteq eqA) as SetMap2_mor.
Proof with eauto.
  intros.
  split.
  all: eapply SetMap2_subset_mor...
  inversion H0...
  inversion H1...
  intros elema.
  intros.
  intros elemb.
  intros.
  symmetry.
  eapply H; symmetry; eauto.
  inversion H0...
  inversion H1...
Qed.    

  
(* Note: This definition of intersection is "up to equivalence".  We need this. *)
Inductive Intersection {U : Type} (eq : relation U) (B C : Ensemble U) : Ensemble U :=
| Intersection_intro : forall x : U,
    SetIn eq B x ->
    SetIn eq C x ->
    Ensembles.In U (Intersection eq B C) x.

Hint Constructors Intersection : setoids.

Theorem Intersection_SetIn { U : Type} (eq : relation U) `{Reflexive U eq} (B C : Ensemble U) : forall x,
    SetIn eq B x ->
    SetIn eq C x ->
    SetIn eq (Intersection eq B C) x.
Proof.
  intros.
  econstructor.
  split.
  reflexivity...
  eauto with setoids...
Qed.

Theorem Intersection_SetIn_inv { U : Type} (eq : relation U) `{Transitive U eq} (B C : Ensemble U) : forall x,
    SetIn eq (Intersection eq B C) x ->
    SetIn eq B x /\
    SetIn eq C x.
Proof with eauto with setoids.
  intros.
  repeat destruct H0...
  inversion H1...
  subst.
  split.
  repeat destruct H2.
  2: repeat destruct H3.
  all: econstructor.
  all: split;[|eassumption]...
Qed.
  
(* TODO: While I might need more detailed lemmas, as there's about a page of lemmas for intersection that are proven in the standard library, I will only prove the ones I need as I go. *)

Add Parametric Morphism T eq `{Equivalence T eq} : (@Intersection T eq)
    with signature (Seteq eq) ==> (Seteq eq) ==> (Seteq eq) as Intersection_mor.
Proof with eauto with setoids.
  intros.
  econstructor.
  all: intros member.
  all: intros InHyp.
  all: inversion InHyp.
  all: subst.
  all: repeat destruct H2.
  all: eapply Intersection_SetIn...
  all: try solve [ inversion H; eauto with setoids].
  all: rewrite H2.
  all: inversion H3.
  all: subst.
  rewrite <- H0...
  rewrite <- H1...
  rewrite H0...
  rewrite H1...
Qed.      

Lemma Intersection_assoc { U : Type} (eq : relation U) `{Equivalence U eq}:
  forall x y z,
    Seteq eq
          (Intersection eq x (Intersection eq y z))
          (Intersection eq (Intersection eq x y) z).
Proof with eauto with setoids.
  intros.
  econstructor.
  all: intros elem.
  all: intros InHyp.
  all: inversion InHyp.
  all: clear InHyp.
  all: subst.
  all: repeat destruct H0.
  all: repeat destruct H1.
  all: inversion H.
  - apply Intersection_SetIn_inv in H2...
    destruct H2.
    assert (SetIn eq x x0) by (eexists;split; eauto).
    eapply Intersection_SetIn...
    eapply Intersection_SetIn...
    all: rewrite H0...
  - inversion H3.
    subst.
    rewrite H1 in H2.
    rewrite <- H0 in *.
    rewrite <- H1 in *.
    eapply Intersection_SetIn...
    eapply Intersection_SetIn...
Qed.

Definition sig_eq {A : Type} {P : A -> Prop} (eq : relation A)
  : relation {x : A | P x}.
  intros x.
  intros x'.
  destruct x.
  destruct x'.
  exact (eq x x0).
Defined.

Lemma sig_eq_refl {A : Type} {P : A -> Prop} (eq : relation A) :
  Reflexive eq ->
  Reflexive (@sig_eq A P eq).
Proof.
  intros.
  intro x.
  unfold sig_eq.
  destruct x.
  eauto.
Qed.

Lemma sig_eq_sym {A : Type} { P : A -> Prop} (eq : relation A) :
  Symmetric eq ->
  Symmetric (@sig_eq A P eq).
Proof.
  intros.
  intros x y H'.
  destruct x.
  destruct y.
  unfold sig_eq in *.
  eauto.
Qed.    

Lemma sig_eq_trans {A : Type} {P : A -> Prop} (eq : relation A) :
  Transitive eq ->
  Transitive (@sig_eq A P eq).
Proof.
  intros.
  intros x y z.
  intros.
  unfold sig_eq in *.
  destruct x.
  destruct y.
  destruct z.
  eauto.
Qed.  

Hint Resolve sig_eq_refl sig_eq_sym sig_eq_trans : setoids.

  Instance sigeq_rel_refl (E : Type) (P : E -> Prop) (rel : relation E) (Rec : Reflexive rel)  : Reflexive (@sig_eq _ P rel).
  eapply sig_eq_refl.
  eauto.
  Defined.

  Instance sigeq_rel_trans (E : Type) (P : E -> Prop) (rel : relation E) (Rec : Transitive rel)  : Transitive (@sig_eq _ P rel).
  eapply sig_eq_trans.
  eauto.
  Defined.


Instance sig_eq_rel (A : Type) (P : A -> Prop) (relA : relation A)  (Equiv_a : Equivalence relA)   : Equivalence (@sig_eq A P relA).
inversion Equiv_a.
eauto with setoids.
Defined.


Definition sigT2_eq {A B : Type} {P : A -> B -> Prop} (eqA : relation A) (eqB : relation B)
  : relation {x : A & {y : B | P x y}}.
  intros x.
  intros x'.
  destruct x.
  destruct x'.
  destruct s.
  destruct s0.
  exact (eqA x x0 /\ eqB x1 x2).
Defined.

Lemma sigT2_eq_refl {A B : Type} {P : A -> B -> Prop} (eqA : relation A) (eqB : relation B) :
  Reflexive eqA ->
  Reflexive eqB ->
  Reflexive (@sigT2_eq A B P eqA eqB).
Proof.
  intros.
  intro x.
  unfold sigT2_eq.
  destruct x.
  destruct s.
  eauto.
Qed.

Lemma sigT2_eq_sym {A B : Type} { P : A -> B -> Prop} (eqA : relation A) (eqB : relation B):
  Symmetric eqA ->
  Symmetric eqB ->
  Symmetric (@sigT2_eq A B P eqA eqB).
Proof.
  intros.
  intros x y H'.
  destruct x.
  destruct y.
  destruct s.
  destruct s0.
  unfold sigT2_eq in *.
  destruct H'.
  eauto.
Qed.    

Lemma sigT2_eq_trans {A B : Type} {P : A -> B -> Prop} (eqA : relation A) (eqB : relation B):
  Transitive eqA ->
  Transitive eqB ->
  Transitive (@sigT2_eq A B P eqA eqB).
Proof.
  intros.
  intros x y z.
  intros.
  unfold sigT2_eq in *.
  destruct x.
  destruct y.
  destruct z.
  destruct s.
  destruct s0.
  destruct s1.
  destruct H1.
  destruct H2.
  eauto.
Qed.  

Hint Resolve sigT2_eq_refl sigT2_eq_sym sigT2_eq_trans : setoids.

Instance sigT2_eq_rel_refl (A B : Type) (P : A -> B -> Prop) (relA : relation A) (relB : relation B) (RecA : Reflexive relA) (RecB : Reflexive relB) : Reflexive (@sigT2_eq _ _ P relA relB).
eapply sigT2_eq_refl;
  eauto.
Defined.

Instance sigT2_eq_rel_trans (A B : Type) (P : A -> B -> Prop) (relA : relation A) (relB : relation B) (RecA : Transitive relA) (RecB : Transitive relB)  : Transitive (@sigT2_eq _ _ P relA relB).
  eapply sigT2_eq_trans;
  eauto.
  Defined.


Instance sigT2_eq_rel (A B : Type) (P : A -> B -> Prop) (relA : relation A) (relB : relation B) (Equiv_a : Equivalence relA) (Equiv_b : Equivalence relB)  : Equivalence (@sigT2_eq A B P relA relB).
inversion Equiv_a.
inversion Equiv_b.
eauto with setoids.
Defined.


Add Parametric Morphism A eqs `{Equivalence _ eqs}: (@Singleton A )
    with signature eqs ==> Seteq eqs as Singleton_mor.
Proof with (eauto with setoids).
  intros...
  split; intro elem; intros...
  all: repeat destruct H1.
  all: inversion H2; subst.
  all: eexists;split.
  etransitivity...
  econstructor.
  symmetry in H0.
  etransitivity...
  econstructor.
Qed.


Add Parametric Morphism A eqs `{Equivalence A eqs}: (@Union A)
    with signature (Seteq eqs) ==> (Seteq eqs) ==> (Seteq eqs) as Union_mor.  
Proof with (eauto with setoids).
  intros.
  split.
  all: intros elem; intros.
  all: repeat destruct H2.
  all: inversion H3; subst.
  - eapply In_SetIn in H4...
    apply H0 in H4.
    repeat destruct H4.
    eexists; split;[|left; eassumption]...
    etransitivity...
    inversion H...
  - eapply In_SetIn in H4...
    apply H1 in H4.
    repeat destruct H4.
    eexists; split;[|right; eassumption]...
    etransitivity...
    inversion H...
  - eapply In_SetIn in H4...
    apply H0 in H4.
    repeat destruct H4.
    eexists; split;[|left; eassumption]...
    etransitivity...
    inversion H...
  - eapply In_SetIn in H4...
    apply H1 in H4.
    repeat destruct H4.
    eexists; split;[|right; eassumption]...
    etransitivity...
    inversion H...
Qed.    


(* While there exists a list_eq setoid, we want to be able to fill up with a default for some Coq developments.  We are expressing that fact via list_max_eq. *)

(* This max_eq should not need to be dependent. *)
Inductive list_max_eq {A : Type} (eq : relation A) (d : A) : relation (list A) :=
| lme_nil : list_max_eq eq d nil nil
| lme_d_r : forall hd tl,
    eq hd d ->
    list_max_eq eq d tl nil ->
    list_max_eq eq d (cons hd tl) nil
| lme_d_l : forall hd tl,
    eq d hd ->
    list_max_eq eq d nil tl ->
    list_max_eq eq d nil (cons hd tl)
| lme_cons : forall hd1 hd2 tl1 tl2,
    eq hd1 hd2 ->
    list_max_eq eq d tl1 tl2 ->
    list_max_eq eq d (cons hd1 tl1) (cons hd2 tl2).

Lemma list_max_eq_refl {E : Type} {eq : relation E} {d : E}:
  (Reflexive eq) -> Reflexive  (list_max_eq eq d).
Proof.
  intros.
  intros x.
  induction x; econstructor;
    eauto with setoids.
Qed.

Lemma list_max_eq_sym {E : Type} {eq : relation E} {d : E}:
  (Symmetric eq) -> Symmetric  (list_max_eq eq d).
Proof.
  intros.
  intros x y.
  intros.
  induction H0; subst; econstructor; eauto.
Qed.

Hint Constructors list_max_eq : setoids.

Lemma list_max_eq_trans {E : Type} {eq : relation E} {d : E} :
  (Transitive eq) ->
  Transitive (list_max_eq eq d).
Proof with eauto with setoids.
  intros.
  intros x y z H'.
  generalize dependent z.
  induction H'; intros...
  all: inversion H1...
Qed.  

Hint Resolve list_max_eq_refl list_max_eq_sym list_max_eq_trans : setoids.


Instance list_max_eq_rel (E : Type) (rel : relation E) (Equiv : Equivalence rel) (d : E ) : Equivalence (list_max_eq rel d).
inversion Equiv.
eauto with setoids.
Defined.

(* We introduce a new notation for dependent respectful_hetero. *)

Notation "R >==> { x & y } R'" := (@respectful_hetero _ _ _ _ R%signature (fun x y => R'%signature)) (at level 100, right associativity).

Add Parametric Morphism A eqs `{Equivalence _ eqs}: (@list_max_eq A eqs)
    with signature eqs ==> eq ==> eq ==> (fun (A B : Prop) => A -> B) as list_max_eq_if_mor.
Proof with (simpl; eauto with setoids).
  intros.
  induction H2...
  all: econstructor...
  etransitivity...
  symmetry in H0.
  etransitivity...
Qed.

Add Parametric Morphism A eqs `{Equivalence _ eqs} : (@list_max_eq A eqs)
    with signature eqs ==> eq ==> eq ==> iff as list_max_eq_iff_mor.
Proof with (simpl; eauto with setoids).
  intros.    
  split; intros; induction H1...
  all: econstructor...
  etransitivity...
  symmetry in H0; etransitivity...
  symmetry in H0; etransitivity...
  etransitivity...
Qed.

(* We define the following pointwise membership for elements of a list *)

(* Side-note: we used to have the following definition as a Fixpoint :
Fixpoint pointwise_member {T : Type} (default_l2 : Ensemble T) (default_l1 : T) (eq : relation T) (l2 : list (Ensemble T)) (l1 : list T)  {struct l1} : Prop:=
  match l1 with
  | nil => (fold_right and True (map (fun X => exists y, eq default_l1 y /\ Ensembles.In _ X y) l2))
  | hd_el :: tl_el =>
    match l2 with
    | nil => (exists y, eq hd_el y /\ Ensembles.In _ default_l2 y) /\ pointwise_member default_l2 default_l1 eq l2 tl_el 
    | hd_set :: tl_set => (exists y, eq hd_el y /\ Ensembles.In _ hd_set y) /\
                          pointwise_member default_l2 default_l1 eq tl_set tl_el
    end
  end.
 *)

(* But instead we choose to write the following equivalent Inductive definition: *)

Inductive pointwise_member {T : Type} (eqT : relation T) (default_l2 : Ensemble T) (default_l1 : T)  : list (Ensemble T) -> list T -> Prop :=
| pwm_nil_r : forall l,
    Forall (fun X => SetIn eqT X default_l1) l ->
    Ensembles.In _ (pointwise_member eqT default_l2 default_l1  l) []
| pwm_nil_l : forall l,
    Forall (fun X => SetIn eqT default_l2 X) l ->
    Ensembles.In _ (pointwise_member eqT default_l2 default_l1 []) l
| pwm_cons : forall hd1 tl1 hd2 tl2,
    (SetIn eqT hd1 hd2) ->
    Ensembles.In _ (pointwise_member eqT default_l2 default_l1  tl1) tl2 ->
    Ensembles.In _ (pointwise_member eqT default_l2 default_l1  (hd1 :: tl1)) (hd2 :: tl2).


(* This definition of pointwise_member should much simplify the rest of the assumpti
ons and the development itself. *)

Hint Constructors pointwise_member : setoids.

Hint Constructors Forall : setoids.

Add Parametric Morphism A (eqs : relation A) d0 : (@Forall A)
    with signature
    (fun f g =>
       f d0 /\ g d0 /\  
    (eqs ==> iff)%signature f g) ==> list_max_eq eqs d0 ==> iff as Forall_lme_mor.
Proof with eauto with setoids.
  intros.
  induction H0...
  split...
  split...
  intros.
  eapply IHlist_max_eq in H2.
  econstructor...
  destruct H.
  destruct H3.
  eapply H4...

  split...
  intros.
  eapply IHlist_max_eq in H2.
  econstructor...
  destruct H.
  destruct H3.
  eapply H4...

  split...
  intros.
  inversion H2; subst...
  eapply IHlist_max_eq in H6.
  econstructor...
  destruct H.
  destruct H3.
  eapply H4...
  intros.
  inversion H2; subst...
  eapply IHlist_max_eq in H6.
  econstructor...
  destruct H.
  destruct H3.
  eapply H4...
Qed.  
  
  
Instance pointwise_member_mor_l A eqs (H: Equivalence eqs) d0 d1 (H_membership : Ensembles.In _ d0 d1):
  Proper ((fun A B => (Seteq eqs) A d0 /\ (Seteq eqs) B d0)
            ==>
            (fun A B => eqs A d1 /\ eqs B d1)
            ==>
            (list_max_eq (Seteq eqs) d0)
            ==>
            (list_max_eq eqs d1)
            ==>
            iff)
         (@pointwise_member A eqs). 
Proof with (simpl; eauto with setoids).
  simpl_relation.
  (* I will have to do induction on the lists here *)
  generalize dependent H3.
  generalize dependent y2.
  generalize dependent x2.
  induction H2...
  all: intros...
  - induction H3...
    split; intros...
    econstructor...
    econstructor...
    split; econstructor...
    econstructor...
    rewrite H2.
    rewrite H0.
    eapply In_SetIn...
    induction H...

    eapply IHlist_max_eq in H6...
    inversion H6...

    split; econstructor...
    econstructor...
    rewrite H5.
    rewrite <- H2.
    eapply In_SetIn...
    induction H...

    eapply IHlist_max_eq in H6...
    inversion H6...

    split; econstructor...
    inversion H6; subst.
    + inversion H7; subst.
      econstructor.
      rewrite H5.
      rewrite <- H0.
      rewrite <- H2...
      eapply pwm_nil_l in H11.
      eapply IHlist_max_eq in H11.
      inversion H11...
    + inversion H6; subst.
      inversion H7; subst.
      econstructor.
      rewrite H0.
      rewrite <- H5.
      rewrite H2...
      eapply pwm_nil_l in H11.
      eapply IHlist_max_eq in H11.
      inversion H11...
  - split; intros.
    + inversion H7; subst...
      eapply IHlist_max_eq...
      inversion H8; subst...
      econstructor...
      inversion H6; subst...
      eapply IHlist_max_eq in H12...
      econstructor.
      econstructor.
      rewrite H5.
      rewrite <- H2.
      rewrite <- H11...
      eapply IHlist_max_eq in H14...
      eapply H14 in H12...
      inversion H12...
    + induction H6...
      * econstructor...
        econstructor...
        rewrite H2.
        rewrite H1.
        eapply In_SetIn...
        inversion H...
        eapply IHlist_max_eq in H7...
        inversion H7...
      * econstructor...
        rewrite H6.
        rewrite H2.
        eapply In_SetIn...
        inversion H...

        eapply IHlist_max_eq...
      * econstructor...
        econstructor...
        rewrite H2.
        rewrite H1.
        eapply In_SetIn...
        inversion H...
        inversion H7; subst...
        inversion H9; subst.
        eapply pwm_nil_l in H13.
        eapply IHlist_max_eq0 in H13.
        inversion H13; subst.
        inversion H10...
      * econstructor...
        inversion H7; subst...
        inversion H9; subst...
        rewrite H2.
        rewrite <- H5.
        rewrite H6...

        inversion H7; subst...
        inversion H9; subst.
        eapply pwm_nil_l in H13.
        eapply IHlist_max_eq in H13.
        eapply H13...
        idtac...
  - split; intros.
    + induction H6...
      * econstructor...
        econstructor...
        rewrite <- H2.
        rewrite H4.
        eapply In_SetIn...
        inversion H...
        eapply IHlist_max_eq in H7...
        inversion H7...
      * eapply IHlist_max_eq0...
        inversion H7; subst.
        inversion H9; subst...
        econstructor...
      * econstructor...
        rewrite <- H6.
        rewrite <- H2.
        eapply In_SetIn...
        inversion H...
        eapply IHlist_max_eq in H7...
      * econstructor...
        inversion H7; subst...
        inversion H9; subst...
        rewrite <- H2.
        rewrite <- H0.
        rewrite <- H6...

        inversion H7; subst...
        inversion H9; subst.
        eapply pwm_nil_l in H13.
        eapply IHlist_max_eq in H13.
        eapply H13...
        idtac...
    + inversion H7; subst...
      eapply IHlist_max_eq...
      inversion H8; subst...
      econstructor...
      inversion H6; subst...
      eapply IHlist_max_eq in H12...
      econstructor.
      econstructor.
      rewrite H13.
      rewrite H0.
      rewrite H2...

      eapply IHlist_max_eq in H14...
      eapply H14 in H12...
      inversion H12...
  - split; intros.
    + induction H6...
      * inversion H7; subst...
        inversion H6; subst...
        econstructor...
        econstructor...
        rewrite <- H2.
        rewrite H4.
        rewrite <- H1...
        eapply pwm_nil_r in H11.
        eapply IHlist_max_eq with (y2 := []) in H11.
        inversion H11...
        idtac...
      * inversion H7; subst.
        eapply IHlist_max_eq in H14...
        inversion H14; subst...
        econstructor...
        econstructor...
        rewrite <- H2.
        rewrite H4.
        rewrite <- H6...
        econstructor...
        econstructor...
        rewrite <- H2.
        rewrite H4.
        rewrite <- H6...
      * inversion H7; subst...
        inversion H9; subst...
        econstructor...
        rewrite <- H2.
        rewrite <- H6.
        rewrite <-H1...
        eapply IHlist_max_eq...
        econstructor...
      * inversion H7; subst...
        econstructor...
        rewrite <- H2.
        rewrite <- H6...
        eapply IHlist_max_eq...
    + induction H6...
      * inversion H7; subst...
        inversion H6; subst...
        econstructor...
        econstructor...
        rewrite  H2.
        rewrite H1.
        rewrite <- H4...
        eapply pwm_nil_r in H11.
        eapply IHlist_max_eq with (x2 := []) in H11.
        inversion H11...
        idtac...
      * inversion H7; subst.
        inversion H9; subst...
        econstructor...
        rewrite H2.
        rewrite H6.
        rewrite <-H4...
        eapply IHlist_max_eq...
        econstructor...
      * inversion H7; subst...
        eapply IHlist_max_eq in H14...
        inversion H14; subst...
        econstructor...
        econstructor...
        rewrite H2.
        rewrite H1.
        rewrite H6...
        econstructor...
        econstructor...
        rewrite H2.
        rewrite H1.
        rewrite H6...
      * inversion H7; subst...
        econstructor...
        rewrite H2.
        rewrite H6...
        eapply IHlist_max_eq...
Qed.


  Theorem Seteq_extensionality (A : Type) (eqA : relation A):
    forall S1 S2,
      (forall x, SetIn eqA S1 x <-> SetIn eqA S2 x) <->
      Seteq eqA S1 S2.
  Proof with eauto with setoids.
    intros; split; intros;
    split; intros elem; intros...
    all: apply H...
  Qed.

  Instance SetIn_mor (A : Type) (eqA : relation A) `{Equivalence A eqA}:
    Proper ((eqA ==> iff) ==> eqA ==> iff) (@SetIn A eqA).
  Proof with eauto with setoids.
    simpl_relation.
    split; intros.
    rewrite H1 in H2.    
    2: rewrite <- H1 in H2.
    all: repeat destruct H2.
    symmetry in H2.
    all: apply H0 in H2...
    all: apply H2 in H3...
    all: eexists;split;[|eassumption].
    all: reflexivity.
  Qed.    

  Instance Subseteq_rel_refl (E : Type) (rel : relation E) (Rec : Reflexive rel)  : Reflexive (Subseteq rel).
  intros x.
  intro elem.
  eauto.
Defined.

  Instance Subseteq_rel_trans (E : Type) (rel : relation E) (Rec : Transitive rel)  : Transitive (Subseteq rel).
  eapply subseteq_trans.
  eauto.
  Defined.

  Instance pair_eq_rel_refl (A B : Type)  (relA : relation A) (relB : relation B) (RecA : Reflexive relA) (RecB : Reflexive relB) : Reflexive (pair_eq relA relB).
  eapply pair_eq_refl;
  eauto.
  Defined.

  Instance pair_eq_rel_trans (A B : Type)  (relA : relation A) (relB : relation B) (RecA : Transitive relA) (RecB : Transitive relB) : Transitive (pair_eq relA relB).
  eapply pair_eq_trans;
  eauto.
  Defined.

Instance Included_trans (A : Type) : Transitive (Included A).
eapply Inclusion_is_transitive.
Defined.

Hint Constructors Equivalence : setoids.

  (* The map morphism is quite an interesting one.  We have some dependencies that are quite interesting, and make the internal dependencies on map quite explicit. They might remove at least some of our dependencies on appease_map! *)
  Lemma map_lme_compat { A  B : Type} (eqA : relation A) (eqB : relation B) `{Reflexive A eqA} `{Equivalence B eqB} : forall (f : A -> B) (d : A) (d' : B) (Heqd : eqB d' (f d)) (l1 l2 : list A),
      (forall x y, In x l1 \/ (eqA x d) -> In y l2 \/ (eqA x d)-> eqA x y -> eqB (f x) (f y)) ->
      (list_max_eq eqA d l1 l2) ->
      (list_max_eq eqB d' (map f l1) (map f l2)).
  Proof with eauto with setoids.
    intros.
    induction H2...
    all: econstructor...
    - rewrite Heqd...
    - eapply IHlist_max_eq...
      intros.
      eapply H1...
      destruct H4...
      left...
      right...
    - rewrite Heqd...
    - eapply IHlist_max_eq...
      intros.
      eapply H1...
      destruct H5...
      left...
      right...
    - eapply H1...
      all: left...
      all: left...
    - eapply IHlist_max_eq...
      intros.
      eapply H1...
      destruct H4...
      left...
      right...
      destruct H5...
      left...
      right...
  Qed.
  
  (* TODO : Write the morphism for the previous compat!*)

  Lemma Full_set_option_eq : forall A eq `{Reflexive A eq},
      (Seteq (option_eq eq) (Full_set (option A)) (Union _ (Singleton _ None)
                                        (SetMap (Full_set _) (fun x =>Some x)))).
  Proof with eauto with setoids.
    intros.
    split; intros.
    all: intros elem; intros.
    - destruct elem.
      exists (Some a); split...
      right.
      repeat econstructor.
      exists None; split...
      left...
      econstructor.
    - destruct elem; eexists; split;econstructor.
      reflexivity.
  Qed.

  (* While originally only defined for Fun a particular application  , it does work for SetMap2 in general*)

  Lemma SetMap2_eq_inhabit_r {A: Type} : forall f eqA (H' : Reflexive eqA) S1 S2 S3 S4,
      Inhabited A S1 ->
      Inhabited A S2 ->
      Seteq eqA (SetMap2 f S1 S2) (SetMap2 f S3 S4) ->
      (Inhabited A S3 /\ Inhabited A S4).
  Proof with eauto with setoids.
    intros.
    destruct H.
    destruct H0.
    inversion H1.
    assert (SetIn eqA (SetMap2 f S1 S2) (f x x0)).
    eapply In_SetIn...
    econstructor...
    apply H2 in H4.
    do 2 destruct H4.
    inversion H5.
    split; econstructor...
Qed.    
    
  Lemma SetMap2_inv {A : Type} :
    forall (f : A -> A -> A) (eqA : relation A) (H' : Equivalence eqA)
           (Hf : forall x x' y y',
               (eqA x x' /\ eqA y y' <->
                 eqA (f x y) (f x' y')))
           S1 S2 S3 S4,
      Inhabited A S1 ->
      Inhabited A S2 ->
      Seteq eqA (SetMap2 f S1 S2)
            (SetMap2 f S3 S4)
      ->
      (Seteq eqA S1 S3) /\ (Seteq eqA S2 S4).
  Proof with (eauto with setoids).
    split.
    - inversion H'; split; intros elem; intros...
      + inversion H0.
        assert (SetIn eqA (SetMap2 f S1 S2) (f elem x)).
        repeat destruct H2.
        repeat destruct H3.
        eexists; split.
        2 : {
          econstructor; try eassumption.
        }
        rewrite <- Hf...
        rewrite H1 in H4.
        inversion H4.
        destruct H5.
        inversion H6.
        all: subst.
        rewrite <- Hf in H5...
        exists x1; destruct H5...
      + destruct (SetMap2_eq_inhabit_r _ _ _ _ _ _ _ H H0 H1). 
        inversion H4.
        assert (SetIn eqA (SetMap2 f S3 S4) (f elem x)).
        repeat destruct H2.
        eexists; split.
        2 : {
         econstructor; try eassumption.
        }
        rewrite <- Hf...
        rewrite <- H1 in H6.
        inversion H6.
        destruct H7.
        inversion H8.
        all: subst.
        rewrite <- Hf in H7...
        exists x1; destruct H7...
    - inversion H'; split; intros elem; intros...
      + inversion H.
        assert (SetIn eqA (SetMap2 f S1 S2) (f x elem)).
        repeat destruct H2.
        repeat destruct H3.
        eexists; split.
        2 : {
          econstructor; try eassumption.
        }
        rewrite <- Hf...
        rewrite H1 in H4.
        inversion H4.
        destruct H5.
        inversion H6.
        all: subst.
        rewrite <- Hf in H5...
        exists y; destruct H5...
      + destruct (SetMap2_eq_inhabit_r _ _ _ _ _ _ _ H H0 H1). 
        inversion H3.
        assert (SetIn eqA (SetMap2 f S3 S4) (f x elem)).
        repeat destruct H2.
        eexists; split.
        2 : {
         econstructor; try eassumption.
        }
        rewrite <- Hf...
        rewrite <- H1 in H6.
        inversion H6.
        destruct H7.
        inversion H8.
        all: subst.
        rewrite <- Hf in H7...
        exists y; destruct H7...
  Qed.      
  
(* TODO : 
     - Provide reasoning principles for pointwise_member as required in the AGT development.
     - Continue refactoring general_model file.
 *)
