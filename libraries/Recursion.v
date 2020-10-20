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

Definition zip_fill {A B C : Type} : (B -> C) -> (A -> C) -> (A -> B -> C) -> list A -> list B -> list C :=
  fun d1 d2 f =>
    fix zip_fill (l_1 : list A) : list B -> list C :=
    match l_1 with
    | [] => fix zf_lmt (l_2 : list B) : list C :=
      match l_2 with
      | [] => []
      | hd_2 :: tl_2 => d1 hd_2 :: zf_lmt tl_2 
      end
    | hd_1 :: tl_1 => fun l_2 =>
                        match l_2 with
                        | [] => d2 hd_1 :: zip_fill tl_1 []
                        | hd_2 :: tl_2 => f hd_1 hd_2 :: zip_fill tl_1 tl_2
                        end
    end.

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
