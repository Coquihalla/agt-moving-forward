Set Bullet Behavior "Strict Subproofs".

Require Import PoplLibraries.Math.
Require Import PoplLibraries.Setoid_library.
Require Import PoplLibraries.Recursion.
Require Import PoplLibraries.Mutual_wf_fix.

(* This development is quite ad-hoc, but sufficient to prove gamma completeness for subtyping in the BRR system. *)

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

(* Unlike the zip_fill in coquitlam, it uses a default function instead of a default value.
   This is to appease the termination checker on default cases.
*)

Definition zip_fill_str2 {A B C : Type} : A -> B -> (A -> B -> C) -> list A -> list B -> list C :=
  fun d1 d2 f =>
    fix zip_fill (l_1 : list A) (l_2 : list B) {struct l_2} : list C :=
    match l_2 with
    | [] => (fix zf_lmt (l_1 : list A) : list C :=
               match l_1 with
               | [] => []
               | hd_1 :: tl_1 => f hd_1 d2 :: zf_lmt tl_1
               end) l_1
    | hd_2 :: tl_2 => match l_1 with
                      | [] => f d1 hd_2 :: (zip_fill [] tl_2)
                      | hd_1 :: tl_1 => f hd_1 hd_2 :: zip_fill tl_1 tl_2
                      end
    end.

Inductive Ann : Set :=
| Opt : Ann
| Req : Ann.

Inductive GType : Set :=
| GDyn : GType
| GInt : GType
| GBool : GType
| GFun : GType -> GType -> GType
| GRec : list GType_mapping -> GType
| GRow : list GType_mapping -> GType
with GType_mapping : Set :=
| m_missing : GType_mapping
| m_map : Ann -> GType -> GType_mapping.

Definition GType_good_ind (P : GType -> Prop) (P0 : GType_mapping -> Prop)
           (f : P GDyn)
           (f0 : P GInt)
           (f1 : P GBool)
           (f2 : forall S_1 S_2,
               P S_1 -> P S_2 -> P (GFun S_1 S_2))
           (f3 : forall l,
               Forall P0 l ->
               P (GRec l))
           (f4 : forall l,
               Forall P0 l ->
               P (GRow l))
           (f5 : P0 m_missing)
           (f6 : forall a s,
               P s ->
               P0 (m_map a s))
  : forall s, P s.

  refine (fix ind (s : GType) {struct s} : P s :=
            let fix l_ind (l : list GType_mapping) {struct l} : Forall P0 l :=
                _
            in
            match s with
            | GDyn => f
            | GInt => f0
            | GBool => f1
            | GFun dom cod => f2 dom cod (ind dom) (ind cod)
            | GRec l => f3 l (l_ind l)
            | GRow l => f4 l (l_ind l)
            end).
  destruct l;
  econstructor.
  destruct g.
  eapply f5.
  eapply f6.
  eapply ind.
  eapply l_ind.
Defined.

Fixpoint size_GT (x : GType) {struct x} : nat :=
  match x with
  | GFun dom cod => 1 + size_GT dom + size_GT cod
  | GRec l => 1 + fold_right (plus) 0 (map size_GT_map l)
  | GRow l => 1 + fold_right (plus) 0 (map size_GT_map l)
  | _ => 1
  end
with size_GT_map (x : GType_mapping) {struct x} : nat :=
       (match x with
          | m_map _ S' => size_GT S'
          | _ => 0
          end).

Fixpoint height_GT (x : GType) {struct x} : nat :=
  match x with
  | GFun dom cod => S (Nat.max (height_GT dom) (height_GT cod))
  | GRec l => S ( fold_right (Nat.max) 0 (map height_GT_map l))
  | GRow l => S ( fold_right (Nat.max) 0 (map height_GT_map l))
  | _ => 0
  end
with height_GT_map (x : GType_mapping) {struct x} : nat :=
       (match x with
        | m_map _ S' => (height_GT S') (* probably should not have the S *)
        | _ => 0
        end).

Theorem size_GT_map_ge1 : forall x,
    0 <= size_GT_map x.
Proof with eauto with math.
  destruct x; simpl...
Qed.

Theorem size_GT_ge1 : forall x,
    1 <= size_GT x.
Proof with eauto with math.
  destruct x; simpl...
Qed.
Theorem size_GT_gt0 : forall x,
    0 < size_GT x.
Proof with eauto with math.
  destruct x; simpl...
Qed.


Hint Resolve size_GT_map_ge1 : math.
Hint Resolve size_GT_gt0 : math.
Hint Resolve size_GT_ge1 : math.

Definition filter_error {A : Type} : list (option A) -> option (list A) :=
  fun l =>
    fold_right (fun hd tl =>
                  match hd, tl with
                  | Some hd, Some tl => Some (hd :: tl)
                  | _, _ => None
                  end) (Some []) l.


Inductive GAnn : Set :=
| Rec : GAnn
| Row : GAnn.

Definition g_meet_mapping_d (a_1 : GAnn) (M_2 : GType_mapping) : option GType_mapping :=
  match a_1, M_2 with
  | _, m_missing => Some m_missing
  | Rec, m_map Opt _ => Some m_missing
  | Row, m_map a S' => Some (m_map a S')
  | _, _ => None
  end.

Fixpoint g_meet (S_1 S_2 : GType) {struct S_1} : option GType :=
  match S_1, S_2 with
  | GInt, GInt => Some GInt
  | GBool, GBool => Some GBool
  | GFun S_11 S_12, GFun S_21 S_22 =>
    match g_meet S_11 S_21, g_meet S_12 S_22 with
    | Some S_dom, Some S_cod => Some (GFun S_dom S_cod)
    | _ , _ => None
    end
  | GRec l_1, GRec l_2 =>
    match filter_error (zip_fill (g_meet_mapping_d Rec) (g_meet_mapping_d Rec) g_meet_mapping l_1 l_2) with
    | Some l => Some (GRec l)
    | None => None
    end
  | GRow l_1, GRec l_2 =>
    match filter_error (zip_fill (g_meet_mapping_d Row) (g_meet_mapping_d Rec) g_meet_mapping l_1 l_2) with
    | Some l => Some (GRec l)
    | None => None
    end
  | GRec l_1, GRow l_2 =>
    match filter_error (zip_fill (g_meet_mapping_d Rec) (g_meet_mapping_d Row) g_meet_mapping l_1 l_2) with
    | Some l => Some (GRec l)
    | None => None
    end
  | GRow l_1, GRow l_2 =>
    match filter_error (zip_fill (g_meet_mapping_d Row) (g_meet_mapping_d Row) g_meet_mapping l_1 l_2) with
    | Some l => Some (GRow l)
    | None => None
    end
  | _, _ => None
  end
with g_meet_mapping (M_1 M_2 : GType_mapping) {struct M_1} : option GType_mapping :=
       match M_1, M_2 with
       | m_missing, m_missing => Some m_missing
       | m_missing, m_map Opt _ => Some m_missing
       | m_map Opt _, m_missing => Some m_missing
       | m_map Req S_1, m_map _ S_2 => match g_meet S_1 S_2 with
                                       | Some S_12 => Some (m_map Req S_12)
                                       | None => None
                                       end
       | m_map _ S_1, m_map Req S_2 => match g_meet S_1 S_2 with
                                       | Some S_12 => Some (m_map Req S_12)
                                       | None => None
                                       end
       | _, _ => None
       end
.

Definition height_oGT (x : option GType) : nat :=
  match x with
  | Some x => height_GT x
  | None => 0
  end.

Transparent height_oGT.

Lemma fold_right_max_le : (* move to math *)
  forall l l0,
    Forall2 le l l0 ->
    fold_right Nat.max 0 l <= fold_right Nat.max 0 l0.
Proof with eauto with math.
  intros.
  induction H; simpl...
Qed.  

Lemma filter_error_eq {A : Type} : forall l l0,
    @filter_error A l = Some l0 ->
    Forall2 (fun x y => x = Some y) l l0.
Proof with eauto with math.
  induction l; intros; simpl in H; inversion H; subst...
  destruct a; try congruence...
  destruct (filter_error l) eqn:?; try congruence.
  inversion H; subst.
  specialize (IHl l1 eq_refl)...
Qed.

Definition height_oGT_map (x : option GType_mapping) : nat :=
  match x with
  | Some x => height_GT_map x
  | None => 0
  end.

Lemma height_l : forall (l: list (option GType_mapping)) l', 
    filter_error l = Some l' ->
    fold_right (Nat.max) 0 (map height_GT_map l') = fold_right (Nat.max) 0 (map height_oGT_map l).
Proof with eauto with math.
  induction l; intros;
  simpl in H; inversion H...
  destruct a; try congruence.
  destruct (filter_error l)...
  specialize (IHl _ eq_refl).
  inversion H; subst; simpl...
Qed.

Lemma map_zipfill {A B C D: Type} : forall (l : list A) (l0 : list B) f g h z,
    @map C D z (zip_fill f g h l l0) =
    (zip_fill (fun x => z (f x)) (fun x => z (g x)) (fun x y => z (h x y)) l l0)
.
Proof with eauto with math.
  induction l; induction l0; intros; simpl in *...
  all: f_equal...
Qed.
    
Opaque Nat.max.

Fixpoint domain (x : GType) : nat :=
  match x with
  | GFun t_1 t_2 => (Nat.max (domain t_1) (domain t_2))
  | GRec l => Nat.max ( length l) (fold_right (Nat.max) 0 (map domain_mapping l))
  | GRow l => Nat.max ( length l) (fold_right (Nat.max) 0 (map domain_mapping l))
  | _ => 0
  end (* While we could likely make the bound a tiny bit lower, this would certainly simplify things *)
with domain_mapping (m : GType_mapping) : nat :=
       match m with
       | m_missing => 0
       | m_map _ S' => domain S'
       end.


Definition GType_good_ind_2 (P : GType -> Prop) (P0 : list GType_mapping -> Prop)
           (f : P GDyn)
           (f0 : P GInt)
           (f1 : P GBool)
           (f2 : forall S_1 S_2,
               P S_1 -> P S_2 -> P (GFun S_1 S_2))
           (f3 : forall l,
               P0 l ->
               P (GRec l))
           (f4 : forall l,
               P0 l ->
               P (GRow l))
           (f5 : P0 [])
           (f6 : forall l,
               P0 l ->
               P0 (m_missing :: l))
           (f7 : forall a s l,
               P s ->
               P0 l ->
               P0 (m_map a s :: l) )
  : forall s, P s.

  refine (fix ind (s : GType) {struct s} : P s :=
            let fix l_ind (l : list GType_mapping) {struct l} : P0 l :=
                _
            in
            match s with
            | GDyn => f
            | GInt => f0
            | GBool => f1
            | GFun dom cod => f2 dom cod (ind dom) (ind cod)
            | GRec l => f3 l (l_ind l)
            | GRow l => f4 l (l_ind l)
            end).
  destruct l.
  eassumption.
  destruct g.
  eapply f6.
  eapply l_ind.
  eapply f7.
  eapply ind.
  eapply l_ind.
Defined.

Lemma expand_max_2_succ : forall x y,
      ((Nat.max 2 x) ^ y) + ((Nat.max 2 x) ^ y) <= (Nat.max 2 x) ^ S (y).
Proof with eauto with math.
  intros.
  replace (Nat.max 2 x ^ y + Nat.max 2 x ^ y) with
      (2 * Nat.max 2 x ^ y)...
  eapply Nat.le_trans with (m := (Nat.max 2 x) * (Nat.max 2 x ^ y))...
  destruct (Nat.max_spec 2 x)...
  destruct H.
  rewrite H0...
  epose proof (Nat.mul_le_mono_l 2 x (x ^ y) _)...
  Unshelve.
  idtac...
Qed.  
Lemma expand_max_n_succ : forall n x y,
    2 <= n ->
    ((Nat.max n x) ^ y) + ((Nat.max n x) ^ y) <= (Nat.max n x) ^ S (y).
Proof with eauto with math.
  intros.
  replace (Nat.max n x ^ y + Nat.max n x ^ y) with
      (2 * Nat.max n x ^ y)...
  eapply Nat.le_trans with (m := (Nat.max n x) * (Nat.max n x ^ y))...
  destruct (Nat.max_spec n x).
  destruct H; destruct H0; try rewrite H0; subst...
  epose proof (Nat.mul_le_mono_l 2 x (x ^ y) _)...
  enough (2 <= Nat.max (S m) x)...
  epose proof (Nat.mul_le_mono_l 2 (Nat.max (S m) x) (Nat.max (S m) x ^ y) _)...
  destruct H0; try rewrite H1; subst...
  epose proof (Nat.mul_le_mono_l 2 n (n ^ y) _)...
  Unshelve.
  all: idtac...
Qed.  

Lemma expand_n_succ : forall n y,
    2 <= n ->
    (n ^ y) + (n ^ y) <= n ^ S (y).
Proof with eauto with math.
  intros...
  replace (n ^ y + n ^ y) with
      (2 *  n ^ y)...
  eapply Nat.le_trans with (m := n * (n ^ y))...
  epose proof (Nat.mul_le_mono_l 2 n (n ^ y) _)...
  Unshelve.
  all: idtac...
Qed.  

Lemma expand_3_n : forall n,
    3 * n = n + n + n.
Proof with eauto with math.
  idtac...
Qed.  

Lemma pow_gt1 : forall x y,
    1 <= (S x) ^ (S ( y)).
Proof with eauto with math.
  destruct x...
  induction y...
  simpl in *...
  induction y;
  simpl in *...
Qed.
Lemma pow_gtx : forall x y z,
    z <= x ->
    z <= ( x) ^ (S ( y)).
Proof with eauto with math.
  destruct x...
  induction y...
  destruct z;
  simpl in *...
  destruct z;
    simpl in *; intros...
  specialize (IHy (S z))...
Qed.

Lemma forall_add_distr {A : Type}: forall f g (l : list A),
    Forall (fun x => f x <= g x) l ->
    fold_right (plus) 0 (map f l) <=
    fold_right (plus) 0 (map g l).
Proof with eauto with math.
  intros.
  induction H...
  simpl...
Qed.  

Lemma forall_add_max {A : Type}: forall f k (l : list A),
    Forall (fun x => f x <= k) l ->
    fold_right (plus) 0 (map f l) <=
    (length l) * k.
Proof with eauto with math.
  intros.
  induction H...
  simpl...
Qed.  

  
Hint Resolve pow_gt1: math.
Hint Resolve pow_gtx: math.
Hint Resolve Nat.pow_le_mono : math.
Lemma height_bound : forall S_1,
    size_GT S_1 <= (S (2 + (domain S_1))) ^ S (height_GT S_1).  (* (3 + domain S_1) ^ S (height_GT S_1) works for function types, but it is harder to prove for records/rows .  The induction hypothesis looses too much info via max. *)
Proof with eauto with math.
  intros.
  eapply GType_good_ind with (s := S_1)
                             (P0 :=  fun x =>
                                       size_GT_map x <=
                                       S (2 + domain_mapping x) ^ S (height_GT_map x)).                                          
  all: try solve [simpl; eauto with math].
  all: intros...
  - cbn beta iota delta [size_GT].
    eapply Nat.le_trans with (m := 1 + (S (2 + (domain S_0)) ^ S (height_GT S_0)) +  (S (2 + (domain S_2)) ^ S (height_GT S_2)))...
    clear H.
    clear H0.
    eapply Nat.le_trans with (m := 1 + S (2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2)) + (S( 2 + (domain S_2)) ^ S (height_GT S_2)))...
    epose proof (Nat.pow_le_mono
                   (S (2 + (domain S_0))) (S (height_GT S_0))
                   (S (2 + (domain (GFun S_0 S_2)))) (height_GT (GFun S_0 S_2)) _ _ _
                )...
    Unshelve.
    2: shelve.
    all: try solve [simpl; eauto with math].

    eapply Nat.le_trans with (m := 1 + S (2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2)) + (S(2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2))))...
    epose proof (Nat.pow_le_mono
                   (S (2 + (domain S_2))) (S (height_GT S_2))
                   (S (2 + (domain (GFun S_0 S_2)))) (height_GT (GFun S_0 S_2)) _ _ _
                )...
    Unshelve.
    2: shelve.
    all: try solve [simpl; eauto with math].

    eapply Nat.le_trans with (m :=   3 * (S(2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2))))...
    enough (1 <= (S(2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2))))...
    
    eapply Nat.le_trans with (m :=   S(2 + (domain (GFun S_0 S_2))) * (S(2 + (domain (GFun S_0 S_2))) ^ (height_GT (GFun S_0 S_2))))...

    Unshelve.
    idtac...
  - cbn beta iota delta [ size_GT domain height_GT].

    eapply Nat.le_trans with (m := 1 + (fold_right (plus) 0
                                                   (map (fun x => S (2 + domain_mapping x) ^ S (height_GT_map x)) l)))...
    eapply forall_add_distr in H...
    (* And this is the important step : *)
    epose proof (forall_add_max (fun x => S (2 + domain_mapping x) ^ S (height_GT_map x)) 
                               (S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l))) l _).
    eapply forall_add_distr in H.
    Unshelve.
    2 : {
      generalize dependent H.
      induction l; intros...
      inversion H; subst.
      specialize (IHl H3).
      econstructor...
      - eapply Nat.pow_le_mono; simpl...
      - eapply Forall_impl.
        2: eapply IHl.
        intros.
        cbn beta iota in H0.
        eapply Nat.le_trans;[ eapply H0|].
        eapply Nat.pow_le_mono; simpl...
    }        
    eapply Nat.le_trans with (m := 1 + length l *
      S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply Nat.le_trans with (m := 1 + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply le_n_S...
    eapply Nat.mul_le_mono_r...
    eapply Nat.le_trans with (m := 1 + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply le_n_S...
    eapply Nat.mul_le_mono_l...
    
    eapply Nat.le_trans with (m := S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)) + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    enough (1 <=S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
  - cbn beta iota delta [ size_GT domain height_GT].

    eapply Nat.le_trans with (m := 1 + (fold_right (plus) 0
                                                   (map (fun x => S (2 + domain_mapping x) ^ S (height_GT_map x)) l)))...
    eapply forall_add_distr in H...
    (* And this is the important step : *)
    epose proof (forall_add_max (fun x => S (2 + domain_mapping x) ^ S (height_GT_map x)) 
                               (S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l))) l _).
    eapply forall_add_distr in H.
    Unshelve.
    2 : {
      generalize dependent H.
      induction l; intros...
      inversion H; subst.
      specialize (IHl H3).
      econstructor...
      - eapply Nat.pow_le_mono; simpl...
      - eapply Forall_impl.
        2: eapply IHl.
        intros.
        cbn beta iota in H0.
        eapply Nat.le_trans;[ eapply H0|].
        eapply Nat.pow_le_mono; simpl...
    }        
    eapply Nat.le_trans with (m := 1 + length l *
      S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply Nat.le_trans with (m := 1 + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + fold_right Nat.max 0 (map domain_mapping l)) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply le_n_S...
    eapply Nat.mul_le_mono_r...
    eapply Nat.le_trans with (m := 1 + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    eapply le_n_S...
    eapply Nat.mul_le_mono_l...
    
    eapply Nat.le_trans with (m := S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)) + (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) *
      S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...
    enough (1 <=S (2 + Nat.max (length l) (fold_right Nat.max 0 (map domain_mapping l))) ^ S (fold_right Nat.max 0 (map height_GT_map l)))...

Qed.
    
  
Lemma height_meet : forall S_1 S_2,
    height_oGT (g_meet S_1 S_2) <= Nat.max (height_GT S_1) (height_GT S_2).
Proof with eauto with math.
  intros S_1.
  eapply GType_good_ind with (s:=S_1) (P0 := fun M_1 => forall M_2,
               match (g_meet_mapping M_1 M_2) with
               | Some M' => height_GT_map M'
               | None => 0
               end <= Nat.max (height_GT_map M_1) (height_GT_map M_2)).
  all: simpl; auto with math.
  all: intros.
  - destruct S_2; simpl...
  - destruct S_2; simpl...
  - destruct S_3; simpl...
    destruct (g_meet S_0 S_3_1) eqn:?;
             destruct (g_meet S_2 S_3_2) eqn:?; simpl...
    specialize (H S_3_1).
    specialize (H0 S_3_2).
    rewrite Heqo in H.
    rewrite Heqo0 in H0.
    simpl in * ...
  - destruct S_2; simpl...
    + rewrite <- Nat.succ_max_distr.
      generalize dependent l0.
      induction H...
      * intros.
        match goal with
        | [ |- context[ match ?A with | Some _ => _ | None => _ end] ] =>
          destruct A eqn:?
        end;[|simpl]...
        simpl.
        eapply height_l in Heqo.
        rewrite Heqo.
        clear Heqo.
        induction l0; simpl...
        destruct a; simpl...
        destruct a; simpl in *...
      * intros. 
        specialize (IHForall (tl l0)).
        clear H0.
        generalize dependent l0.
        induction l0; intros...
        all: simpl in *.
        -- destruct x; [ | destruct a]; simpl...
           all: match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           simpl in *...
        -- destruct (g_meet_mapping x a) eqn:?;[|simpl]...
           match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           specialize (H a).
           rewrite Heqo in H.
           simpl in *...
    +rewrite <- Nat.succ_max_distr.
      generalize dependent l0.
      induction H...
      * intros.
        match goal with
        | [ |- context[ match ?A with | Some _ => _ | None => _ end] ] =>
          destruct A eqn:?
        end;[|simpl]...
        simpl.
        eapply height_l in Heqo.
        rewrite Heqo.
        clear Heqo.
        induction l0; simpl...
        destruct a; simpl...
        destruct a; simpl in *...
      * intros. 
        specialize (IHForall (tl l0)).
        clear H0.
        generalize dependent l0.
        induction l0; intros...
        all: simpl in *.
        -- destruct x; [ | destruct a]; simpl...
           all: match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           all: simpl in *...
        -- destruct (g_meet_mapping x a) eqn:?;[|simpl]...
           match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           specialize (H a).
           rewrite Heqo in H.
           simpl in *...
  - destruct S_2; simpl...
    + rewrite <- Nat.succ_max_distr.
      generalize dependent l0.
      induction H...
      * intros.
        match goal with
        | [ |- context[ match ?A with | Some _ => _ | None => _ end] ] =>
          destruct A eqn:?
        end;[|simpl]...
        simpl.
        eapply height_l in Heqo.
        rewrite Heqo.
        clear Heqo.
        induction l0; simpl...
        destruct a; simpl...
        destruct a; simpl in *...
      * intros. 
        specialize (IHForall (tl l0)).
        clear H0.
        generalize dependent l0.
        induction l0; intros...
        all: simpl in *.
        -- destruct x; [ | destruct a]; simpl...
           all: match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           simpl in *...
        -- destruct (g_meet_mapping x a) eqn:?;[|simpl]...
           match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           specialize (H a).
           rewrite Heqo in H.
           simpl in *...
    +rewrite <- Nat.succ_max_distr.
      generalize dependent l0.
      induction H...
      * intros.
        match goal with
        | [ |- context[ match ?A with | Some _ => _ | None => _ end] ] =>
          destruct A eqn:?
        end;[|simpl]...
        simpl.
        eapply height_l in Heqo.
        rewrite Heqo.
        clear Heqo.
        induction l0; simpl...
        destruct a; simpl...
        destruct a; simpl in *...
      * intros. 
        specialize (IHForall (tl l0)).
        clear H0.
        generalize dependent l0.
        induction l0; intros...
        all: simpl in *.
        -- destruct x; [ | destruct a]; simpl...
           all: match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           all: simpl in *...
        -- destruct (g_meet_mapping x a) eqn:?;[|simpl]...
           match goal with
           | [ |- context[ match filter_error ?A with | Some _ => _ | None => _ end] ] =>
             destruct (filter_error A) eqn:?
           end...
           specialize (H a).
           rewrite Heqo in H.
           simpl in *...
  - destruct M_2; simpl...
    destruct a; simpl...
  - destruct a; destruct M_2...
    destruct a; simpl...
    all: specialize (H g); simpl in *.
    all: destruct (g_meet s g); simpl in * ...
Qed.      

Definition Ev := (GType * GType) % type.

Definition size_ev (x : Ev) :=
  size_GT (fst x) + size_GT (snd x).

Definition height_ev (x : Ev) :=
  Nat.max (height_GT (fst x)) (height_GT (snd x)).

Definition domain_ev (x : Ev) :=
  Nat.max (domain (fst x)) (domain (snd x)).

Lemma ev_size_bound : forall x,
    size_ev (x) <= 2 * S (2 + domain_ev x) ^ S (height_ev x). (* because we do size of each type *)
Proof with eauto with math.
  intros.
  unfold size_ev.
  rewrite Nat.mul_succ_l.
  rewrite Nat.mul_succ_l.
  rewrite Nat.mul_0_l.
  rewrite plus_O_n.
  eapply Nat.add_le_mono.
  all: unfold domain_ev.
  all: unfold height_ev.
  - eapply Nat.le_trans with (m := S (2 + (domain (fst x))) ^ S (height_GT (fst x)))...
    eapply height_bound.
  - eapply Nat.le_trans with (m := S (2 + (domain (snd x))) ^ S (height_GT (snd x)))...
    eapply height_bound.
Qed.

Definition D (a : GAnn) : GType_mapping :=
  match a  with
  | Rec => m_missing
  | Row => m_map Opt GDyn
  end.

(* NOTE: STRICT POSITIVITY RESTRICTIONS MAKE THIS A PROXY FOR THE PROOF ONLY, NOT A CORRECT DEFINITION*)
Inductive I : GType -> GType -> Ev -> Prop :=
| I_ii : I GInt GInt (GInt, GInt)
| I_bb : I GBool GBool (GBool, GBool)
| I_dd : I GDyn GDyn (GDyn, GDyn)
| I_id : I GInt GDyn (GInt, GInt)
| I_di : I GDyn GInt (GInt, GInt)
| I_bd : I GBool GDyn (GBool, GBool)
| I_db : I GDyn GBool (GBool, GBool)
| I_fd : forall S_1 S_2 ev,
    I (GFun S_1 S_2) (GFun GDyn GDyn) ev ->
    I (GFun S_1 S_2) GDyn ev
| I_df : forall S_3 S_4 ev,
    I (GFun GDyn GDyn) (GFun S_3 S_4) ev ->
    I GDyn (GFun S_3 S_4) ev
| I_ff : forall S_11 S_12 S_21 S_22 S'_11 S'_12 S'_21 S'_22,
    I S_21 S_11 (S'_21, S'_11) ->
    I S_12 S_22 (S'_12, S'_22) ->
    I (GFun S_11 S_12) (GFun S_21 S_22) (GFun S'_11 S'_12, GFun S'_21 S'_22)
| I_red : forall l ev,
    I (GRec l) (GRow []) ev ->
    I (GRec l) GDyn ev
| I_rod : forall l ev,
    I (GRow l) (GRow []) ev ->
    I (GRow l) GDyn ev
| I_dre : forall l ev,
    I (GRow []) (GRec l) ev ->
    I GDyn (GRec l) ev
| I_dro : forall l ev,
    I (GRow []) (GRow l) ev ->
    I GDyn (GRow l) ev
| I_rere : forall l_1 l_2 l_3 l_4,
    FAI Rec Rec l_1 l_2 (l_3, l_4) ->
    I (GRec l_1) (GRec l_2) (GRec l_3, GRec l_4)
| I_rero : forall l_1 l_2 l_3 l_4,
    FAI Rec Row l_1 l_2 (l_3, l_4) ->
    I (GRec l_1) (GRow l_2) (GRec l_3, GRec l_4)
| I_rore : forall l_1 l_2 l_3 l_4,
    FAI Row Rec l_1 l_2 (l_3, l_4) ->
    I (GRow l_1) (GRec l_2) (GRow l_3, GRec l_4)
| I_roro : forall l_1 l_2 l_3 l_4,
    FAI Row Row l_1 l_2 (l_3, l_4) ->
    I (GRow l_1) (GRow l_2) (GRow l_3, GRow l_4)
with I_m : GType_mapping -> GType_mapping -> (GType_mapping * GType_mapping) % type -> Prop :=
| Im_mis : forall M,
    I_m M m_missing (M, m_missing)
| Im_rr : forall S_1 S_2 S'_1 S'_2,
    I S_1 S_2 (S'_1, S'_2) ->
    I_m (m_map Req S_1) (m_map Req S_2) (m_map Req S'_1, m_map Req S'_2)
| Im_xo_def : forall a S_1 S_2 S'_1 S'_2,
    I S_1 S_2 (S'_1, S'_2) ->
    I_m (m_map a S_1) (m_map Opt S_2) (m_map a S_1, m_map Opt S'_2)
| Im_xo_undef : forall a S_1 S_2,
    (* (forall ev, ~ I S_1 S_2 ev) strictly positive restriction impedes this, but would be sufficient
       for the proof to just have the case and deal with it! *) 
    I_m (m_map a S_1) (m_map Opt S_2) (m_map a S_1, m_missing)
with FAI : GAnn -> GAnn -> list GType_mapping -> list GType_mapping -> (list GType_mapping * list GType_mapping) -> Prop :=
| FAI_nil : forall d_1 d_2,
    FAI d_1 d_2 [] [] ([], [])
| FAI_cons : forall d_1 d_2 hd_1 hd_2 tl_1 tl_2 hd'_1 hd'_2 tl'_1 tl'_2,
    I_m hd_1 hd_2 (hd'_1, hd'_2) ->
    FAI d_1 d_2 tl_1 tl_2 (tl'_1, tl'_2) ->
    FAI d_1 d_2 (hd_1 :: tl_1) (hd_2 :: tl_2) (hd'_1 :: tl'_1, hd'_2 :: tl'_2)
| FAI_nil_l : forall d_1 d_2 hd_2 tl_2 hd'_1 hd'_2 tl'_1 tl'_2,
    I_m (D d_1) hd_2 (hd'_1, hd'_2) ->
    FAI d_1 d_2 [] tl_2 (tl'_1, tl'_2) ->
    FAI d_1 d_2 [] (hd_2 :: tl_2) (hd'_1 :: tl'_1, hd'_2 :: tl'_2)
| FAI_nil_r : forall d_1 d_2 hd_1 tl_1 hd'_1 hd'_2 tl'_1 tl'_2,
    I_m hd_1 (D d_2) (hd'_1, hd'_2) ->
    FAI d_1 d_2 tl_1 [] (tl'_1, tl'_2) ->
    FAI d_1 d_2 (hd_1 :: tl_1) [] (hd'_1 :: tl'_1, hd'_2 :: tl'_2)

.

Scheme I_good_ind := Induction for I Sort Prop
  with I_m_good_ind := Induction for I_m Sort Prop
  with FAI_good_ind := Induction for FAI Sort Prop.

Lemma I_bound : forall S_1 S_2 ev,
    I S_1 S_2 ev ->
    height_ev ev <= Nat.max (height_GT S_1) (height_GT S_2).
Proof with eauto with math.
  intros S_1 S_2 ev H.
  eapply I_good_ind with (g := S_1) (g0 := S_2) (e := ev)
                         (P0 := fun m m0 p H =>
                                  Nat.max (height_GT_map (fst p))
                                          (height_GT_map (snd p)) <=
                                  Nat.max (height_GT_map m)
                                          (height_GT_map m0))
    (P1 := fun d_1 d_2 l_1 l_2 ev f =>
             Nat.max (S (fold_right Nat.max 0 (map height_GT_map (fst ev))))
                     (S (fold_right Nat.max 0 (map height_GT_map (snd ev)))) <=
             Nat.max (S (fold_right Nat.max 0 (map height_GT_map l_1)))
                     (S (fold_right Nat.max 0 (map height_GT_map l_2))))

  ...
  - simpl in *...
  - intros.
    unfold height_ev in *; simpl.
    simpl in *.
    eauto with math.
  - simpl in *...
  - simpl in *...
  - destruct a; intros; simpl in *...
    all: unfold height_ev in *; simpl.
    all: simpl in *...
  - destruct a; intros; simpl in *...
    all: unfold height_ev in *; simpl.
    all: simpl in *...
  - intros; simpl in *...
  - intros; destruct d_1; simpl in *...
  - intros; destruct d_2; simpl in *...
Qed.

Lemma filter_error_length {A :Type}: forall l l0,
    filter_error l = Some l0 ->
    length l = @length A l0.
Proof with eauto with math.
  induction l; simpl; intros...
  all: inversion H...
  destruct a...
  destruct (filter_error l) eqn:?; try congruence.
  inversion H; subst; simpl...
Qed.  

(* These two pending lemmas are hard to prove in Coq but are straightforward to prove by hand.*)
Lemma meet_domain_bound : forall S_1 S_2 S_3,
    g_meet S_1 S_2 = Some S_3 ->
    domain S_3 <= Nat.max (domain S_1) (domain S_2).
Proof with eauto with math.
  Admitted.
Lemma I_domain_bound : forall S_1 S_2 ev,
    I S_1 S_2 ev ->
    domain_ev ev <= Nat.max (domain S_1) (domain S_2).
Proof with eauto with math.
Admitted.
                                 
Inductive evidence_composition : Ev -> Ev -> Ev -> Prop :=
| ec_intro : forall S_1 S_2 S_3 S_4 S_23 ev_l ev_r ev,
    g_meet S_2 S_3 = Some S_23 ->
    I S_1 S_23 ev_l ->
    I S_23 S_3 ev_r ->
    I (fst ev_l) (snd ev_r) ev ->
    evidence_composition (S_1, S_2) (S_3, S_4) ev.

Lemma ec_bound_height :
  forall ev_1 ev_2 ev_3,
    evidence_composition ev_1 ev_2 ev_3 ->
    height_ev ev_3 <= Nat.max (height_ev ev_1) (height_ev ev_2).
Proof with eauto with math.
  intros.
  inversion H; subst.
  pose proof (height_meet S_2 S_3).
  rewrite H0 in H4.
  simpl in H4.
  eapply I_bound in H1.
  eapply I_bound in H2.
  eapply I_bound in H3.
  unfold height_ev in *.
  simpl in *...
Qed.

Theorem ec_bound_size :
  forall ev_1 ev_2 ev_3,
    evidence_composition ev_1 ev_2 ev_3 ->
    size_ev ev_3 <= 2 * S (2 + Nat.max (domain_ev ev_1) (domain_ev ev_2)) ^ S (Nat.max (height_ev ev_1) (height_ev ev_2)).
Proof with eauto with math.
  intros.
  inversion H; subst.
  eapply Nat.le_trans.
  eapply ev_size_bound.
  eapply Nat.mul_le_mono_l.
  eapply Nat.pow_le_mono...
  2 : eapply ec_bound_height in H...
  eapply meet_domain_bound in H0.
  eapply I_domain_bound in H1.
  eapply I_domain_bound in H2.
  eapply I_domain_bound in H3.
  unfold domain_ev in *; simpl in *...
Qed.  
  
      
    (* Local Variables: *)
    (* mode: coq; *)
    (* coq-compile-before-require: t; *)
    (* End: *)
                   
