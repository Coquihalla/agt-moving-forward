Require Import PoplLibraries.Math.
Require Export Coq.Lists.List.
Export Coq.Lists.List.ListNotations.
Require Export Relation_Definitions.
Require Export FunInd. 
Require Export Recdef.

(* Note : These definitions have portions in Prop.
   For a purist development in Set, see bounded_rows_algorithmic_simplified.v *)

Fixpoint dependent_map {A B : Type} (l:list A)
         (f : forall x : A, In x l -> B) {struct l} : list B.
  case_eq l; intros.
  exact [].
  subst.
  eapply cons.
  - eapply f.
    simpl.
    left.
    reflexivity.
  - refine (dependent_map _ _ l0 _).
    intros.
    eapply f.
    simpl.
    right.
    eauto.
Defined.

Lemma appease_map {A B: Type} : forall l (f : forall x : A, In x l -> B) g,
    (forall x H, f x H = g x) ->
    dependent_map l f =
    map g l.
Proof.
  induction l; intros;
  simpl; eauto.
  unfold eq_rect_r.
  simpl.
  f_equal.
  f_equal.
  repeat (eapply functional_extensionality_dep; intros).
  rewrite H.
  all: eauto.
Qed.  

Hint Resolve appease_map : math.

Fixpoint zip_fill {A B C: Type} (d1 : A) (d2 : B) (l1 : list A) (l2 : list B) (f : A -> B -> C) {struct l1} : list C.
case_eq l1; intros.
- exact (map (fun X => f d1 X) l2).
- case_eq l2; intros; subst.
  exact (map (fun X => f X d2) (a :: l)).
  exact (f a b :: (zip_fill _ _ _ d1 d2 l l0 f)).
Defined.

Fixpoint dependent_zip_fill {A B C: Type} (d1 : A) (d2 : B) (l1 : list A) (l2 : list B) (f : forall x (H : (In x l1) + {x = d1}) y (H1 : (In y l2) + {y = d2}), C) { struct l1}  : list C.
  refine (match l1 as l return (l = l1) -> _ with
          | [] => fun _ => (dependent_map l2 (fun X HYP => f d1 (inright eq_refl) X (inleft HYP)))
          | a :: l1 => fun _ => _
          end eq_refl).
  refine (match l2 as l return (l = l2) -> _ with
          | [] => fun _ => (dependent_map (a :: l1) (fun X HYP => f X _ d2 (inright eq_refl)))
          | b :: l2 => fun _ => (_ :: _)
          end eq_refl).
  - rewrite <- e in *.
    left.
    apply HYP.
  - rewrite <- e in *.
    rewrite <- e0 in *.
    eapply f.
    left.
    left.
    reflexivity.
    left.
    left.
    reflexivity.
  - rewrite <- e in *.
    rewrite <- e0 in *.
    eapply (dependent_zip_fill _ _ _ d1 d2 l1 l2).
    intros.
    eapply f.
    destruct H.
    left.
    right.
    eapply i.
    right.
    eapply e1.
    destruct H1.
    left.
    right.
    eapply i.
    right.
    eapply e1.
Defined.    

(* Goal of dependent zip fill is to simplify use of induction hypotheses. *)

Lemma appease_zip_fill {A B C : Type} : forall (d1 : A) (d2 : B) l1 l2 f g,
    (forall x H1 y H2, f x H1 y H2 = g x y) ->
    @dependent_zip_fill A B C d1 d2 l1 l2 f =
    zip_fill d1 d2 l1 l2 g.
Proof.
  induction l1; destruct l2; intros; simpl; eauto.
  all: unfold eq_rect_r.
  all: simpl.
  all: f_equal; eauto with math.
Qed.

Hint Resolve appease_zip_fill : math.

Lemma match_push_up {A B C : Type} :
  forall (f : A -> B) (g : B -> option C),
    forall x,
      match match x with
                    | Some a => Some (f a)
                    | None => None
                    end
              with
              | Some b => g b
              | None => None
              end =
      match x with
      | Some a => g (f a)
      | None => None
      end.
Proof.
  destruct x; intros; eauto.
Qed.

Hint Resolve match_push_up : setoids.
