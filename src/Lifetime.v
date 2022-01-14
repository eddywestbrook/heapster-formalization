(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms.

From Heapster Require Import
     Utils
     Permissions.

Import ListNotations.
(* end hide *)

Variant Lifetime := current | finished.
Definition Lifetimes := list Lifetime.

(** lifetime helpers **)

Definition lifetime : Lifetimes -> nat -> option Lifetime :=
  @nth_error Lifetime.

Definition replace_lifetime (l : Lifetimes) (n : nat) (new : Lifetime) : Lifetimes :=
  replace_list_index l n new.

Lemma replace_lifetime_same c n l :
  lifetime c n = Some l -> replace_lifetime c n l = c.
Proof.
  apply replace_list_index_eq.
Qed.

Lemma lifetime_replace_lifetime c n l :
  lifetime (replace_lifetime c n l) n = Some l.
Proof.
  apply nth_error_replace_list_index_eq.
Qed.

(** [n1] in the lifetime list [x1] subsumes [n2] in the lifetime list [x2] *)
Definition subsumes n1 n2 x1 x2 :=
  (Some current = lifetime x2 n2 -> Some current = lifetime x1 n1) /\
  (Some finished = lifetime x1 n1 -> Some finished = lifetime x2 n2) /\
  (None = lifetime x1 n1 -> None = lifetime x2 n2).

(* TODO: generalize to a single lemma *)
Instance subsumes_preorder x : PreOrder (fun a b => subsumes a b x x).
Proof.
  unfold subsumes.
  constructor; [repeat intro; auto |].
  intros n1 n2 n3. intros (? & ? & ?) (? & ? & ?). split; [| split]; intros.
  - apply H. apply H2; auto.
  - apply H3. apply H0; auto.
  - apply H4. apply H1; auto.
Qed.
Instance subsumes_preorder' x : PreOrder (subsumes x x).
Proof.
  unfold subsumes.
  constructor; [repeat intro; auto |].
  intros n1 n2 n3. intros (? & ? & ?) (? & ? & ?). split; [| split]; intros.
  - apply H. apply H2; auto.
  - apply H3. apply H0; auto.
  - apply H4. apply H1; auto.
Qed.

Lemma subsumes_decidable n1 n2 l1 l2 : decidable (subsumes n1 n2 l1 l2).
Proof.
  unfold subsumes.
Admitted.

(** Lifetime ordering **)
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

Definition monotonic_at (p : perm) (n : nat) (x y : Lifetimes) : Prop :=
  guar p x y -> lifetime_lte (lifetime x n) (lifetime y n).

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
  pre := pre p;
  rely := rely p;
  guar := fun x y => guar p x y /\ monotonic_at p n x y;
  |}.
Next Obligation.
  constructor; repeat intro.
  - split; intuition.
  - destruct H, H0. split; [etransitivity; eauto |]. intro. etransitivity; eauto.
Qed.
Next Obligation.
  respects.
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
  forall l1 l2 x y, guar p x y <-> guar p (replace_lifetime x n l1) (replace_lifetime y n l2).

Lemma invariant_l p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime y n = Some l2 ->
               guar p x y <-> guar p (replace_lifetime x n l1) y.
Proof.
  intros.
  erewrite <- (replace_list_index_eq _ y n l2) at 2; auto.
Qed.

Lemma invariant_r p n (Hinv : invariant_at p n) :
  forall l1 l2 x y, lifetime x n = Some l1 ->
               guar p x y <-> guar p x (replace_lifetime y n l2).
Proof.
  intros.
  rewrite <- (replace_list_index_eq _ x n l1) at 2; auto.
Qed.

(* Note: does not have permission to start or end the lifetime [n] *)
Program Definition when (n : nat) (p : perm) : perm :=
  {|
    pre := fun x => lifetime x n = Some current -> pre p x;
    rely := fun x y => lifetime x n = None /\ lifetime y n = None \/
                      lifetime y n = Some finished \/
                      (* This is similar to [lifetime_lte] but we cannot have [lifetime x n =
                  None /\ lifetime y n = Some current], since that would break transitivity
                  of [rely]. This would allow for an earlier period where the lifetime is
                  not started, where the rely of p is not true. *)
                  lifetime x n = Some current /\ lifetime y n = Some current /\ rely p x y;
    guar := fun x y => x = y \/
                    (* state that the guarantee should hold even when you change lifetimes in x, or something like that, kind of like what we do in owned *)
                    (forall n n', subsumes n' n x x -> subsumes n' n y y) /\
                    lifetime x n = Some current /\ lifetime y n = Some current /\ guar p x y;
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
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; [| split; [| split]]; auto; etransitivity; eauto.
Qed.
Next Obligation.
  decompose [and or] H; decompose [or and] H0; subst; auto.
  - rewrite H1 in H4. discriminate H4.
  - rewrite H1 in H3. discriminate H3.
  - eapply pre_respects; eauto.
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

Lemma restrict_monotonic_at_when p n : when n p ≡≡ restrict_monotonic_at (when n p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto.
  intro. rewrite H0, H2. reflexivity.
Qed.
Lemma when_restrict_monotonic_at p n : when n p ≡≡ when n (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H0, H1. reflexivity.
Qed.

Program Definition owned (n : nat) (ls : nat -> Prop) (p : perm) : perm :=
  {|
    pre := fun x => lifetime x n = Some current; (* probably need soemthing with subsumes *)
    rely := fun x y => lifetime x n = lifetime y n /\
                      (forall l, ls l -> subsumes l l x y) /\
                      (lifetime x n = Some finished -> rely p x y);
    guar := fun x y => x = y \/
                      lifetime y n = Some finished /\ guar p (replace_lifetime x n finished) y;
  |}.
Next Obligation.
  constructor; repeat intro; auto.
  - split; intuition.
  - decompose [and] H. decompose [and] H0. clear H H0.
    split; [| split]; intros.
    + etransitivity; eauto.
    + etransitivity. apply H3; auto. auto.
    + etransitivity. eauto. apply H7; auto. rewrite <- H1. auto.
Qed.
Next Obligation.
  constructor; repeat intro; auto.
  decompose [and or] H; decompose [and or] H0; subst; auto.
  right. split; auto. etransitivity; eauto.
  rewrite <- (replace_lifetime_same y n finished); auto.
Qed.

Lemma owned_monotone n ls p1 p2 : p1 <= p2 -> owned n ls p1 <= owned n ls p2.
Proof.
  intros. destruct H. constructor; simpl; intros; decompose [and or] H; auto 6.
Qed.

Instance Proper_lte_perm_owned :
  Proper (eq ==> eq ==> lte_perm ==> lte_perm) owned.
Proof.
  repeat intro; subst. apply owned_monotone; auto.
Qed.

Instance Proper_eq_perm_owned :
  Proper (eq ==> eq ==> eq_perm ==> eq_perm) owned.
Proof.
  repeat intro; subst. split; apply owned_monotone; auto.
Qed.

Lemma restrict_monotonic_at_owned n ls p : owned n ls p ≡≡ restrict_monotonic_at (owned n ls p) n.
Proof.
  split; [constructor; intros; simpl in *; auto | apply restrict_monotonic_at_lte].
  decompose [and or] H; subst; try solve [intuition]. split; auto. clear H.
  intro. rewrite H1. destruct (lifetime x n) as [[] |]; simpl; auto.
Qed.
Lemma owned_restrict_monotonic_at n ls p : owned n ls p ≡≡ owned n ls (restrict_monotonic_at p n).
Proof.
  split; constructor; intros; simpl in *; intuition.
  right; intuition. intro. rewrite H. rewrite lifetime_replace_lifetime. reflexivity.
Qed.

(* trivial direction *)
Lemma foo' n ls p q :
  owned n ls (restrict_monotonic_at p n ** restrict_monotonic_at q n) <=
  owned n ls (restrict_monotonic_at (p ** q) n).
Proof.
  rewrite <- owned_restrict_monotonic_at. apply owned_monotone.
  apply sep_conj_perm_monotone; apply restrict_monotonic_at_lte.
Qed.

Lemma lifetimes_sep_gen p q n ls :
  p ⊥ owned n ls q -> when n p ⊥ owned n ls (p ** q).
Proof.
  split; intros.
  - simpl in H0. decompose [and or] H0; [subst; intuition |].
    simpl. right; left; auto.
  - simpl in H0. decompose [and or] H0; [subst; intuition |].
    simpl. split; [| split].
    + rewrite H1, H3; auto.
    + intros. destruct H. simpl in sep_r. apply sep_r; auto.
    + intros. rewrite H1 in H4. discriminate H4.
Qed.

(* no longer true after adding [ls]. Fortunately it's not used. *)
(* not actually a special case of the above *)
(* Lemma lifetimes_sep n p ls : when n p ⊥ owned n ls p. *)
(* Proof. *)
(*   constructor; intros; simpl in H; auto. *)
(*   - decompose [and or] H; subst; try reflexivity. *)
(*     simpl. right; left; auto. *)
(*   - decompose [and or] H; subst; try reflexivity. *)
(*     simpl. split; [| split]. *)
(*     + rewrite H1, H0. auto. *)
(*     + intros. *)
(*     + intros. rewrite H1 in H2. discriminate H2. *)
(* Qed. *)

Lemma convert p q n ls (Hmon : forall x y, monotonic_at p n x y) (Hmon' : forall x y, monotonic_at q n x y) :
  when n p ** owned n ls (p ** q) <= p ** owned n ls q.
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
Lemma convert_bottom p n ls (Hmon : forall x y, monotonic_at p n x y) :
  when n p ** owned n ls p <= p ** owned n ls bottom_perm.
Proof.
  rewrite <- (sep_conj_perm_bottom p) at 2. apply convert; auto.
  repeat intro. simpl in H. subst. reflexivity.
Qed.

(* Lemma lcurrent_pre_trans' x n1 n2 n3 : *)
(*     lcurrent_pre x n1 n3 -> *)
(*     lcurrent_pre x n1 n2 /\ lcurrent_pre x n2 n3. *)
(* Proof. *)
(*   unfold lcurrent_pre. split. *)
(*   - split. *)
(*     + intro. apply H. *)
(* Admitted. *)

(** n1 subsumes n2, and the rely states that lifetimes don't do weird stuff. **)
Program Definition lcurrent n1 n2 : perm :=
  {|
    pre x := subsumes n1 n2 x x;
    rely x y := x = y \/ (* add a case for when it doesn't subsume in x, then anything, that lets us weaken the guar. *)
                  ~subsumes n1 n2 x x \/ (* no longer needed if ⊥ changes *)
                    subsumes n1 n2 x x /\
                    subsumes n1 n2 y y /\
                    lifetime_lte (lifetime x n1) (lifetime y n1) /\
                    lifetime_lte (lifetime x n2) (lifetime y n2);
    guar x y := x = y \/ ~subsumes n1 n2 x x;
  |}.
Next Obligation.
  constructor; repeat intro; intuition; subst; intuition.
  right. right. intuition; etransitivity; eauto.
Qed.
Next Obligation.
  constructor; auto. intros ? ? ? [] []; subst; auto.
  (* right. destruct H, H0; auto. *)
Qed.
Next Obligation.
  destruct H; subst; auto. destruct H; intuition.
Qed.

Lemma lcurrent_transitive n1 n2 n3 :
  lcurrent n1 n3 <= lcurrent n1 n2 ** lcurrent n2 n3.
Proof.
  constructor; intros.
  - destruct H as (? & ? & ?). simpl in *. eapply subsumes_preorder; eauto.
  - destruct H. simpl in *. destruct H, H0; subst; auto. right. admit.
  - simpl in *. (* should be easy *)
(*     destruct H as (H12 & ? & ?), H0 as (H23 & ? & ?). split; [| split]; auto.
    destruct H12, H23.
    split; etransitivity; eauto.
    (* intros. etransitivity; eauto. apply H12. admit. admit. *)
    (* (* we don't know anything about n2 *) *)
  - constructor; auto.
Qed.*)
Admitted.

Lemma lcurrent_sep n1 n2 :
  lcurrent n1 n2 ⊥ lcurrent n1 n2.
Proof.
  constructor; intros ? ? []; subst; try reflexivity; simpl; intuition.
Qed.

(* Lemma lcurrent_sep_owned n1 n2 p : *)
(*   lcurrent n1 n2 ⊥ owned n1 p. *)
(* Proof. *)
(*   constructor; intros ? ? []; subst; try reflexivity. *)
(*   destruct H. right. *)
(* Qed. *)

Lemma lcurrent_duplicate n1 n2 :
  lcurrent n1 n2 ≡≡ lcurrent n1 n2 ** lcurrent n1 n2.
Proof.
  split.
  - constructor; intros; simpl in *; [apply H | apply H | subst; constructor; left; auto].
  - constructor; intros; simpl in *; subst; auto.
    + split; [| split]; auto. apply lcurrent_sep.
    + induction H. intuition.
      destruct IHclos_trans1; subst; auto.
Qed.

(* Weaken the lifetime n1 to n2 *)
Lemma lcurrent_when n1 n2 p :
  (* lcurrent n1 n2 should still be valid too? *)
  lcurrent n1 n2 ** when n2 p <= lcurrent n1 n2 ** when n1 p.
Proof.
  constructor; intros.
  - simpl in *. destruct H as (? & ? & ?). split; [| split]; auto.
    + intro. apply H0. symmetry. apply H. auto.
    + admit.
      (* split; intros. *)
      (* * apply H1. destruct H2; subst; intuition. *)
      (*   right. split; [| split; [| split]]; auto; symmetry. *)
      (*   apply H. ; auto. *)
  - simpl in *. admit.
  - simpl in *. induction H.
    + destruct H; subst; auto. constructor. destruct H; subst; auto.
      destruct H; subst; auto. constructor; auto.
      destruct H as (? & ? & ? & ?).
      pose proof (subsumes_decidable n1 n2 x x).
      destruct H3.
      * pose proof (H _ _ H3).
        symmetry in H0. apply H3 in H0.
        symmetry in H1. apply H4 in H1.
        constructor; auto. right. right. split; auto.
      * constructor; auto.
    + econstructor 2; eauto.
Abort.


 (*  - simpl. destruct H as (? & ? & ?). simpl in *. *)
 (*    intro. symmetry in H2. apply H in H2. auto. *)
 (*  - destruct H. destruct H; subst; try reflexivity. destruct H as ((? & ?) & ? & ?). *)
 (*    destruct H0 as [[? ?] | [? | ?]]. *)
 (*    + left. split; symmetry; [apply H | apply H1]; auto. *)
 (*    + right. left. symmetry. apply H1; auto. *)
 (*    + (* subsumes x n1 n2 gives us the wrong direction here. *) *)
 (*      right. destruct (lifetime y n2) eqn:?; auto. destruct l. *)
 (*      * right. destruct H0 as (? & ? & ?). split; [| split]; auto. *)
 (*        destruct (lifetime x n2) eqn:?. destruct l. all: auto; try contradiction H3. *)
 (*        red in H. rewrite H0, Heqo0 in H. *)
 (*        admit. *)
 (*      * admit. *)
 (*      * admit. *)
 (*  (* right. destruct H2 as (? & ? & ?). split; [| split]; admit. *) *)
 (*  admit. admit. *)
 (*  - induction H. 2: econstructor 2; eauto. *)
 (*    destruct H. constructor. left. auto. *)

 (*    destruct H; subst; try reflexivity. destruct H as (? & ? & ?). *)
 (*    constructor. right. right. split; [| split]; auto. *)
 (* Abort. *)
