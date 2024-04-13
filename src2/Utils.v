(* begin hide *)
Require Import Coq.Lists.List.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eqit
     Eq.UpToTaus
     Eq.EqAxiom.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

(** * Lens typeclass *)
Class Lens (A B:Type) : Type :=
  {
  lget: A -> B;
  lput: A -> B -> A;
  lGetPut: forall a b, lget (lput a b) = b;
  lPutGet: forall a, lput a (lget a) = a;
  lPutPut: forall a b b', lput (lput a b) b' = lput a b'
  }.

(* A lens into the first projection gives a lens into a pair type *)
Global Program Instance Lens_fst (A B C : Type) `{Lens A C} : Lens (A * B) C :=
  {|
    lget x := lget (fst x);
    lput x y := (lput (fst x) y, snd x);
  |}.
Next Obligation.
  rewrite lGetPut. reflexivity.
Qed.
Next Obligation.
  rewrite lPutGet. reflexivity.
Qed.
Next Obligation.
  rewrite lPutPut. reflexivity.
Qed.


(* An indexed partial lens is a partial lens for each index in a set Ix *)
Class IxPartialLens (Ix A B : Type) : Type :=
  {
    iget : Ix -> A -> option B;
    iput : Ix -> A -> B -> A;
    iGetPut_eq : forall i a b, iget i (iput i a b) = Some b;
    iGetPut_neq : forall i1 i2 a b1 b2,
      i1 <> i2 -> iget i1 a = Some b1 ->
      iget i1 (iput i2 a b2) = iget i1 a;
    iPutGet : forall i a b, iget i a = Some b -> iput i a b = a;
    iPutPut_eq : forall i a b, iput i (iput i a b) b = iput i a b;
    iPutPut : forall i a b0 b1 b2, iget i a = Some b0 ->
                                   iput i (iput i a b1) b2 = iput i a b2;
  }.

(* Can compose a Lens with an index partial lens *)
Global Program Instance Lens_IxPartialLens Ix A B C `{Lens A B} `{IxPartialLens Ix B C} :
  IxPartialLens Ix A C :=
  {|
    iget i a := iget i (lget a);
    iput i a c := lput a (iput i (lget a) c);
  |}.
Next Obligation.
  rewrite lGetPut. apply iGetPut_eq.
Qed.
Next Obligation.
  rewrite lGetPut. eapply iGetPut_neq; eassumption.
Qed.
Next Obligation.
  rewrite iPutGet; [ | assumption ]. apply lPutGet.
Qed.
Next Obligation.
  rewrite lGetPut. rewrite lPutPut. rewrite iPutPut_eq. reflexivity.
Qed.
Next Obligation.
  rewrite lPutPut. rewrite lGetPut. erewrite iPutPut; [ reflexivity | eassumption ].
Qed.


(** * [replace_list_index] *)
(** A function for replacing an element in a list, growing the list if needed. *)
Fixpoint replace_list_index {A : Type} (l : list A) (n : nat) (new : A) : list A :=
  match l with
  | [] => repeat new (n + 1)
  | h :: t => match n with
            | O => new :: t
            | S n => h :: replace_list_index t n new
            end
  end.

(** Some properties about [replace_list_index] and [nth_error] *)
Lemma replace_list_index_length A (l : list A) n (a : A) :
  n < length l ->
  length l = length (replace_list_index l n a).
Proof.
  revert l. induction n; intros l Hl.
  - destruct l; auto. inversion Hl.
  - destruct l.
    + inversion Hl.
    + simpl in Hl. apply PeanoNat.Nat.succ_lt_mono in Hl. simpl. f_equal. auto.
Qed.

Lemma nth_error_replace_list_index_neq A n n' (l : list A) (a : A) :
  n' < length l ->
  n <> n' ->
  nth_error l n = nth_error (replace_list_index l n' a) n.
Proof.
  revert l n'.
  induction n; intros l n' Hl Hn; (destruct l; [inversion Hl |]);
    simpl; destruct n'; intuition.
  (* apply IHn; auto. apply PeanoNat.Nat.succ_lt_mono; auto. *)
Qed.

Lemma nth_error_replace_list_index_eq A n (l : list A) (a : A) :
  nth_error (replace_list_index l n a) n = Some a.
Proof.
  revert l. induction n; intros l.
  - destruct l; auto.
  - destruct l; simpl; auto.
    clear IHn. simpl. rewrite PeanoNat.Nat.add_1_r. induction n; auto.
Qed.

Lemma replace_list_index_eq A (l : list A) n a :
  nth_error l n = Some a ->
  replace_list_index l n a = l.
Proof.
  intros. revert H. revert n. induction l; intros.
  - destruct n; inversion H.
  - destruct n; simpl; auto.
    + inversion H; auto.
    + f_equal; auto.
Qed.

Lemma nth_error_app_last A n (l : list A) (a : A) :
  length l = n ->
  nth_error (l ++ [a]) n = Some a.
Proof.
  revert l. induction n; intros [| l] Hl; inversion Hl; auto.
  simpl. remember (length l0). subst. apply IHn; auto.
Qed.

Lemma nth_error_app_early A n (l : list A) (a : A) :
  n < length l ->
  nth_error (l ++ [a]) n = nth_error l n.
Proof.
  revert l. induction n; intros l Hl.
  - destruct l; auto; inversion Hl.
  - destruct l; auto.
    + inversion Hl.
    + simpl in Hl. apply PeanoNat.Nat.succ_lt_mono in Hl. apply IHn; auto.
Qed.

Lemma replace_list_index_idem {A} l n new :
  @replace_list_index A (replace_list_index l n new) n new =
    replace_list_index l n new.
Proof.
  revert n; induction l; intros; [ induction n | destruct n ]; simpl; try reflexivity.
  - simpl in IHn. rewrite IHn; reflexivity.
  - simpl in IHl. rewrite (IHl n). reflexivity.
Qed.

Lemma replace_list_index_twice {A} l n new1 new2 :
  n < length l ->
  @replace_list_index A (replace_list_index l n new1) n new2 =
    replace_list_index l n new2.
Proof.
  revert n; induction l; intros; [ induction n | destruct n ]; simpl; try reflexivity.
  - inversion H.
  - f_equal. apply IHl. apply Lt.lt_S_n. assumption.
Qed.


(* List indexing is an indexed partial lens *)
Global Program Instance IxPartialLens_list A : IxPartialLens nat (list A) A :=
  {|
    iget i l := nth_error l i;
    iput i l a := replace_list_index l i a;
  |}.
Next Obligation.
  apply nth_error_replace_list_index_eq.
Qed.
Next Obligation.
  revert i1 i2 H H0; induction a; intros; [ | destruct i1 ].
  - destruct i1; simpl in H0; discriminate.
  - destruct i2; [ elimtype False; apply H; reflexivity | ].
    simpl; reflexivity.
  - destruct i2; [ simpl; reflexivity | ]. apply IHa.
    + intro; subst. apply H; reflexivity.
    + apply H0.
Qed.
Next Obligation.
  apply replace_list_index_eq; assumption.
Qed.
Next Obligation.
  apply replace_list_index_idem.
Qed.
Next Obligation.
  apply replace_list_index_twice.
  revert i H; induction a; intros; [ | destruct i ].
  - destruct i; simpl in H; discriminate.
  - apply Lt.neq_0_lt. simpl. intro; discriminate.
  - simpl. apply Lt.lt_n_S. apply IHa. assumption.
Qed.


(** * itree stuff *)

(* The effect that combines a get and a put on the current state, by modifying
the state according to the supplied function and returning the old version
before it was modified *)
Variant modifyE C : Type -> Type :=
  | Modify : forall (f : C -> C), modifyE C C.
Global Arguments Modify {C} f.

Definition sceE (C : Type) := (exceptE unit +' modifyE C +' nondetE).
