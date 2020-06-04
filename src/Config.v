From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Export Heapster.Permissions.

Import MonadNotation.
Import ListNotations.

Variant Lifetime := current | finished.

(* Memory model *)
Definition addr : Set := nat * nat.

Inductive SByte :=
| Byte : nat -> SByte
| Ptr : addr -> SByte
| SUndef : SByte.

Definition mem_block := nat -> option SByte.

Inductive logical_block :=
| LBlock (size : nat) (bytes : mem_block) : logical_block.

Definition memory := nat -> option logical_block.

Record config : Type :=
  {
  l : list Lifetime;
  m : memory;
  }.
Module Config <: Permissions.Config.
  Definition t := config.
End Config.

Module Permissions' := Permissions Config.
Export Config.
Export Permissions'.

(** lifetime helpers **)

Definition lifetime : config -> nat -> option Lifetime :=
  fun c => nth_error (l c).

Fixpoint replace_list_index {A : Type} (l : list A) (n : nat) (new : A) :=
  match l with
  | [] => repeat new (n + 1)
  | h :: t => match n with
            | O => new :: t
            | S n => h :: replace_list_index t n new
            end
  end.
Definition replace_lifetime (c : config) (n : nat) (new : Lifetime) : config :=
  {|
  l := replace_list_index (l c) n new;
  m := m c
  |}.

Lemma replace_lifetime_same c n l :
  lifetime c n = Some l -> replace_lifetime c n l = c.
Proof.
  intros. destruct c. unfold lifetime in H. unfold replace_lifetime. f_equal. simpl in *.
  generalize dependent n. induction l0; intros; simpl in *; auto.
  - assert (@nth_error Lifetime [] n <> None). intro. rewrite H in H0. discriminate H0.
    apply nth_error_Some in H0. inversion H0.
  - destruct n; auto.
    + inversion H. auto.
    + rewrite IHl0; auto.
Qed.

Lemma lifetime_replace_lifetime c n l :
  lifetime (replace_lifetime c n l) n = Some l.
Proof.
  destruct c. unfold replace_lifetime. simpl. revert n l.
  induction l0; intros; simpl; induction n; auto.
  unfold lifetime in *. simpl in *. auto.
Qed.

Definition lifetime_lte (l1 l2 : option Lifetime) : Prop :=
  match l1, l2 with
  | None, _ => True
  | Some current, None => False
  | Some current, _ => True
  | Some finished, Some finished => True
  | _, _ => False
  end.

Instance lifetime_lte_preorder : PreOrder lifetime_lte.
Proof.
  constructor; repeat intro.
  - destruct x as [[] |]; simpl; auto.
  - destruct x as [[] |], y as [[] |], z as [[] |]; simpl; intuition.
Qed.

Definition monotonic_at (p : perm) (n : nat) (x y : config) : Prop :=
  upd p x y -> lifetime_lte (lifetime x n) (lifetime y n).

Instance monotonic_at_reflexive p n : Reflexive (monotonic_at p n).
Proof.
  repeat intro. reflexivity.
Qed.

Lemma bottom_monotonic_at n : forall x y, monotonic_at bottom_perm n x y.
Proof.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

Definition monotonic (P : Perms) (n : nat) : Prop :=
  forall p, p ∈ P -> exists p', p' <= p /\ p' ∈ P /\ forall x y, monotonic_at p' n x y.

Lemma monotonic_bottom n : monotonic bottom_Perms n.
Proof.
  repeat intro. exists bottom_perm. split; [| split].
  apply bottom_perm_is_bottom. auto. apply bottom_monotonic_at.
Qed.

Program Definition restrict_monotonic_at (p : perm) (n : nat) : perm :=
  {|
  dom := dom p;
  view := view p;
  upd := fun x y => upd p x y /\ monotonic_at p n x y;
  |}.
Next Obligation.
  respects.
Qed.
Next Obligation.
  constructor; repeat intro.
  - split; intuition.
  - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
Qed.

Lemma restrict_monotonic_at_monotone p p' n :
  p <= p' -> restrict_monotonic_at p n <= restrict_monotonic_at p' n.
Proof.
  intros []. constructor; intros; simpl; auto. destruct H.
  split; auto. intro. auto.
Qed.

Lemma restrict_monotonic_at_lte p n : restrict_monotonic_at p n <= p.
Proof.
  constructor; intros; simpl in *; intuition.
Qed.

Definition invariant_at (p : perm) (n : nat) : Prop :=
  forall l1 l2 x y, upd p x y <-> upd p (replace_lifetime x n l1) (replace_lifetime y n l2).

Lemma invariant_l p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime y n = Some l2 ->
               upd p x y <-> upd p (replace_lifetime x n l1) y.
Proof.
  intros.
  rewrite <- (replace_lifetime_same y n l2) at 2; auto.
Qed.

Lemma invariant_r p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime x n = Some l1 ->
               upd p x y <-> upd p x (replace_lifetime y n l2).
Proof.
  intros.
  rewrite <- (replace_lifetime_same x n l1) at 2; auto.
Qed.

(** memory helpers **)

Definition read (c : config) (ptr : addr) : option SByte :=
  match m c (fst ptr) with
  | Some (LBlock size bytes) => if snd ptr <? size then bytes (snd ptr) else None
  | _ => None
  end.

Definition write (c : config) (ptr : addr) (val : SByte)
  : option config :=
  match m c (fst ptr) with
  | Some (LBlock size bytes) =>
    if snd ptr <? size
    then Some {|
             l := l c;
             m := fun b => if b =? fst ptr
                        then Some (LBlock size (fun o => if o =? snd ptr
                                                      then Some val
                                                      else bytes o))
                        else m c b
           |}
    else None
  | _ => None
  end.

(* TODO clean up these proofs (ssreflect?) *)
Lemma write_read : forall c ptr val,
    (exists c', write c ptr val = Some c') ->
    (* TODO notation not working? *)
    bind (write c ptr val) (fun c' => read c' ptr) = Some val.
Proof.
  intros. destruct H. simpl. rewrite H. unfold write in H. unfold read. destruct ptr. simpl in *.
  destruct (m c n); try solve [inversion H]. destruct l0.
  destruct (n0 <? size) eqn:?; inversion H. simpl. rewrite Nat.eqb_refl.
  rewrite Heqb. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma read_write : forall c ptr,
    (exists val, read c ptr = Some val) ->
    bind (read c ptr) (fun val => write c ptr val) = Some c.
Proof.
  intros. destruct H. simpl. rewrite H. unfold read in H. unfold write.
  destruct ptr as (b & o). destruct c. simpl in *.
  destruct (m0 b) eqn:?; try solve [inversion H]. destruct l1.
  destruct (o <? size); try solve [inversion H].
  apply f_equal. (* not sure why I need apply *)
  f_equal. apply functional_extensionality. intros. destruct (x0 =? b) eqn:?; auto.
  rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0; subst.
  rewrite Heqo0. f_equal. f_equal. apply functional_extensionality. intros.
  destruct (x0 =? o) eqn:?; auto.
  rewrite <- (Bool.reflect_iff _ _ (Nat.eqb_spec _ _)) in Heqb0. subst. auto.
Qed.

Lemma write_write : forall c ptr val,
    bind (write c ptr val) (fun c' => write c' ptr val) = write c ptr val.
Proof.
  simpl. intros. destruct (write c ptr val) eqn:?; auto. unfold write in *.
  destruct (m c (fst ptr)) eqn:?; try solve [inversion Heqo].
  destruct l0 eqn:?. destruct (snd ptr <? size) eqn:?; inversion Heqo.
  simpl. rewrite Nat.eqb_refl. rewrite Heqb. apply f_equal. f_equal.
  apply functional_extensionality. intros. destruct (x =? fst ptr); auto.
  repeat f_equal. apply functional_extensionality. intros.
  destruct (x0 =? snd ptr); auto.
Qed.

(** Lifetime permissions **)

Program Definition when (n : nat) (p : perm) : perm :=
  {|
  dom := fun x => (lifetime x n = Some current /\ dom p x) \/
               lifetime x n = Some finished;
  view := fun x y => lifetime x n = None /\ lifetime y n = None \/
                  lifetime y n = Some finished \/
                  lifetime x n = Some current /\ lifetime y n = Some current /\ view p x y;
  upd := fun x y => x = y \/
                 lifetime x n = Some current /\ lifetime y n = Some current /\ upd p x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - destruct (lifetime x n) as [[] |]; intuition.
  - decompose [and or] H; decompose [and or] H0; subst; auto.
    + rewrite H1 in H3. discriminate H3.
    + rewrite H2 in H3. discriminate H3.
    + rewrite H1 in H2. discriminate H2.
    + rewrite H2 in H5. discriminate H5.
    + right; right. split; [| split]; auto. etransitivity; eauto.
Qed.
Next Obligation.
  decompose [and or] H; decompose [or and] H0; subst; auto.
  - rewrite H2 in H4. discriminate H4.
  - rewrite H1 in H2. discriminate H2.
  - left. split; auto. eapply dom_respects; eauto.
  - rewrite H1 in H3. discriminate H3.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; [| split]; auto. etransitivity; eauto.
Qed.

Lemma when_monotone n p1 p2 : p1 <= p2 -> when n p1 <= when n p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 7.
Qed.

Instance Proper_lte_perm_when :
  Proper (eq ==> lte_perm ==> lte_perm) when.
Proof.
  repeat intro; subst. apply when_monotone; auto.
Qed.

Instance Proper_eq_perm_when :
  Proper (eq ==> eq_perm ==> eq_perm) when.
Proof.
  repeat intro; subst. split; apply when_monotone; auto.
Qed.

Lemma restrict_monotonic_at_when p n : when n p ≡ restrict_monotonic_at (when n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto.
  intro. rewrite H1, H0. reflexivity.
Qed.
Lemma when_restrict_monotonic_at p n : when n p ≡ when n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H, H0. reflexivity.
Qed.

Program Definition owned (n : nat) (p : perm) : perm :=
  {|
  dom := fun x => lifetime x n = Some current;
  view := fun x y => lifetime x n = lifetime y n /\ (lifetime x n = Some finished -> view p x y);
  upd := fun x y => x = y \/
                 lifetime y n = Some finished /\ upd p (replace_lifetime x n finished) y;
  |}.
Next Obligation.
  constructor; repeat intro; auto.
  - split; intuition.
  - destruct H, H0.
    split; etransitivity; eauto. apply H2. rewrite <- H. auto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; auto. etransitivity; eauto.
  rewrite <- (replace_lifetime_same y n finished); auto.
Qed.

Lemma owned_monotone n p1 p2 : p1 <= p2 -> owned n p1 <= owned n p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6.
Qed.

Instance Proper_lte_perm_owned :
  Proper (eq ==> lte_perm ==> lte_perm) owned.
Proof.
  repeat intro; subst. apply owned_monotone; auto.
Qed.

Instance Proper_eq_perm_owned :
  Proper (eq ==> eq_perm ==> eq_perm) owned.
Proof.
  repeat intro; subst. split; apply owned_monotone; auto.
Qed.

Lemma restrict_monotonic_at_owned p n : owned n p ≡ restrict_monotonic_at (owned n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
  intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto.
Qed.
Lemma owned_restrict_monotonic_at p n : owned n p ≡ owned n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity.
Qed.

(* trivial direction *)
Lemma foo' p q n :
  owned n (restrict_monotonic_at p n * restrict_monotonic_at q n) <=
  owned n (restrict_monotonic_at (p * q) n).
Proof.
  rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
  apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
Qed.

Lemma lifetimes_sep_gen p q n :
  p ⊥ owned n q -> when n p ⊥ owned n (p * q).
Proof.
  split; intros.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. right; left; auto.
  - simpl in H0. decompose [and or] H0. subst; intuition.
    simpl. split. rewrite H1, H2; auto.
    intros. rewrite H2 in H3. discriminate H3.
Qed.

(* not actually a special case of the above *)
Lemma lifetimes_sep n p : when n p ⊥ owned n p.
Proof.
  constructor; intros; simpl in H; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. right; left; auto.
  - decompose [and or] H; subst; try reflexivity.
    simpl. split. rewrite H1, H0. auto. intros. rewrite H1 in H2. discriminate H2.
Qed.

Lemma convert p q n (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) :
  when n p * owned n (p * q) <= p * owned n q.
Proof.
  split; intros.
  - simpl in *. decompose [and or] H; auto. split; auto. split; auto.
    eapply lifetimes_sep_gen; eauto.
  - simpl in *. decompose [and or] H; auto. destruct (lifetime x n) as [[] | ]; auto 7.
  - simpl in H. induction H. 2: { econstructor 2; eauto. }
    decompose [and or] H; simpl; subst; try solve [constructor; auto].
    clear H.
    apply Operators_Properties.clos_trans_t1n_iff.
    apply Operators_Properties.clos_trans_t1n_iff in H2.
    constructor 2 with (y:=replace_lifetime x n finished).
    { right; right. split; [apply lifetime_replace_lifetime | reflexivity]. }
    pose proof (lifetime_replace_lifetime x n finished).
    induction H2; intros; subst; auto.
    + constructor. destruct H1; auto. right; right. split; auto.
      rewrite replace_lifetime_same; auto.
    + assert (lifetime y n = Some finished).
      { destruct H1; [apply Hmon in H1 | apply Hmon' in H1]; rewrite H in H1; simpl in H1;
          destruct (lifetime y n) as [[] |]; inversion H1; auto. }
      econstructor 2. 2: apply IHclos_trans_1n; auto.
      destruct H1; auto. right; right. split; auto. rewrite replace_lifetime_same; auto.
Qed.

(* special case of convert *)
Lemma convert_bottom p n (Hmon : forall x y, monotonic_at p n x y) :
  when n p * owned n p <= p * owned n bottom_perm.
Proof.
  rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

(** memory permissions **)

Program Definition read_p (ptr : addr) : perm :=
  {|
  (* ptr points to valid memory *)
  dom x := exists v, read x ptr = Some v;
  (* only checks if the memory ptr points to in the 2 configs are equal *)
  view x y := match m x (fst ptr), m y (fst ptr) with
              | Some (LBlock size1 bytes1), Some (LBlock size2 bytes2) =>
                (snd ptr < size1 <-> snd ptr < size2) /\
                bytes1 (snd ptr) = bytes2 (snd ptr)
              | Some _, None => False
              | None, Some _ => False
              | _, _ => True
              end;
  (* no updates allowed *)
  upd x y := x = y;
  |}.
Next Obligation.
  split; intuition. inversion H0. inversion H1. inversion H0.
Qed.
Next Obligation.
  constructor; repeat intro; simpl; auto; destruct (m x (fst ptr)); auto.
  - destruct l0. split; reflexivity.
  - destruct l0. destruct (m y (fst ptr)); destruct (m z (fst ptr)); auto; destruct l0;
                   intros; auto. destruct l1; intros.
    + destruct H, H0. split; etransitivity; eauto.
    + contradiction H.
  - destruct (m z (fst ptr)); auto. destruct (m y (fst ptr)); try intuition.
Qed.
Next Obligation.
  unfold read in *.
  destruct (m y (fst ptr)).
  - destruct l0. destruct (m x (fst ptr)); [destruct l0 | contradiction H]; auto.
    destruct H. destruct (snd ptr <? size0) eqn:?.
    + repeat rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H.
      exists H0. rewrite H in Heqb. rewrite Heqb. rewrite <- H2. auto.
    + inversion H1.
  - destruct (m x (fst ptr)). destruct l0; contradiction H. inversion H1.
Qed.
Next Obligation.
  constructor; repeat intro; subst; auto.
Qed.

(* TODO factor out common dom and view *)
Program Definition write_p (ptr : addr) : perm :=
  {|
  (* ptr points to valid memory *)
  dom x := exists v, read x ptr = Some v;
  (* only checks if the memory ptr points to in the 2 configs are equal *)
  view x y := match m x (fst ptr), m y (fst ptr) with
              | Some (LBlock size1 bytes1), Some (LBlock size2 bytes2) =>
                (snd ptr < size1 <-> snd ptr < size2) /\
                bytes1 (snd ptr) = bytes2 (snd ptr)
              | Some _, None => False
              | None, Some _ => False
              | _, _ => True
              end;
  (* only the pointer we have write permission to may change *)
  upd x y := forall ptr', ptr <> ptr' -> read x ptr' = read y ptr';
  |}.
Next Obligation.
  split; intuition. inversion H0. inversion H1. inversion H0.
Qed.
Next Obligation.
  constructor; repeat intro; simpl; auto; destruct (m x (fst ptr)); auto.
  - destruct l0. split; reflexivity.
  - destruct l0. destruct (m y (fst ptr)); destruct (m z (fst ptr)); auto; destruct l0;
                   intros; auto. destruct l1; intros.
    + destruct H, H0. split; etransitivity; eauto.
    + contradiction H.
  - destruct (m z (fst ptr)); auto. destruct (m y (fst ptr)); try intuition.
Qed.
Next Obligation.
  unfold read in *.
  destruct (m y (fst ptr)).
  - destruct l0. destruct (m x (fst ptr)); [destruct l0 | contradiction H]; auto.
    destruct H. destruct (snd ptr <? size0) eqn:?.
    + repeat rewrite (Bool.reflect_iff _ _ (Nat.ltb_spec0 _ _)) in H.
      exists H0. rewrite H in Heqb. rewrite Heqb. rewrite <- H2. auto.
    + inversion H1.
  - destruct (m x (fst ptr)). destruct l0; contradiction H. inversion H1.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  etransitivity. apply H; auto. apply H0; auto.
Qed.

Lemma read_lte_write : forall ptr, read_p ptr <= write_p ptr.
Proof.
  constructor; simpl; repeat intro; subst; auto.
Qed.

(* Lemma read_separate : forall ptr ptr', read_p ptr ⊥ read_p ptr'. *)
(* Proof. *)
(*   constructor; intros; auto. *)
(*   - simpl. *)
(* Qed. *)
