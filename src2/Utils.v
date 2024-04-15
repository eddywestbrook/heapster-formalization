(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Lists.List
     Arith.PeanoNat.

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


(***
 *** Helper PreOrder instances
 ***)

Global Instance PreOrder_trivial {A} : @PreOrder A (fun _ _ => True).
Proof.
  constructor; repeat intro; trivial.
Qed.

Global Instance PreOrder_and {A} (R1 R2 : A -> A -> Prop) `{PreOrder A R1} `{PreOrder A R2} :
  PreOrder (fun x y => R1 x y /\ R2 x y).
Proof.
  constructor; repeat intro.
  - split; reflexivity.
  - destruct H1; destruct H2; split; etransitivity; eassumption.
Qed.

Global Instance PreOrder_impl {A} (R : A -> Prop) : PreOrder (fun x y => R x -> R y).
Proof.
  constructor; repeat intro; auto.
Qed.

Global Instance PreOrder_map_PreOrder {A B} f R `{PreOrder B R} :
  @PreOrder A (fun x y => R (f x) (f y)).
Proof.
  constructor; repeat intro; [ reflexivity | etransitivity; eassumption ].
Qed.


(***
 *** Lenses and partial lenses
 ***)

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
    iGetPut_neq : forall i1 i2 a b,
      i1 <> i2 -> iget i1 a <> None ->
      iget i1 (iput i2 a b) = iget i1 a;
    iPutGet : forall i a b, iget i a = Some b -> iput i a b = a;
    iPutPut_eq : forall i a b, iput i (iput i a b) b = iput i a b;
    iPutPut : forall i a b1 b2, iget i a <> None ->
                                iput i (iput i a b1) b2 = iput i a b2;
  }.

(* Putting 3 times with a partial lens always simplifies to putting twice,
because the first put ensures the index has a value so iPutPut can work *)
Lemma iPutPutPut `{IxPartialLens} i a b1 b2 b3 :
  iput i (iput i (iput i a b1) b2) b3 = iput i (iput i a b1) b3.
Proof.
  apply iPutPut. rewrite iGetPut_eq. intro; discriminate.
Qed.


(* The option type is a trivial partial lens *)
Global Program Instance IxPartialLens_option A : IxPartialLens unit (option A) A :=
  {|
    iget _ opt_a := opt_a;
    iput _ _ a := Some a;
  |}.
Next Obligation.
  elimtype False. apply H. destruct i1; destruct i2; reflexivity.
Qed.


(* A Lens can be composed with an indexed partial lens *)
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


(* A set of indices is self-contained iff writing to any index outside the set
   does not affect any index in the set *)
Definition self_contained_ixs `{IxPartialLens} (ixs : Ix -> Prop) : Prop :=
  forall st ix_in ix_out elem,
    ixs ix_in -> ~ ixs ix_out ->
    iget ix_in (iput ix_out st elem) = iget ix_in st.

(* Types with a default element *)
Class Default (A:Type) := default_elem : A.

(* Lists have the empty list as a default element *)
Global Instance Default_List A : Default (list A) := nil.

(* Option types have None as a default element *)
Global Instance Default_option A : Default (option A) := None.

(* Types with decidable equality *)
Class DecidableEq (A:Type) := dec_eq : forall (x y : A), {x = y} + {x <> y}.

(* The unit type trivially has decidable equality *)
Global Program Instance DecidableEq_unit : DecidableEq unit := fun _ _ => left _.
Next Obligation.
  destruct H; destruct H0; reflexivity.
Qed.

(* Natural numbers have decidable equality *)
Global Instance DecidableEq_nat : DecidableEq nat := Nat.eq_dec.

(* Apply iget to an optional value, returning None if the value is None *)
Definition iget_opt {Ix A B} `{IxPartialLens Ix A B} ix (opt_x : option A) : option B :=
  match opt_x with
  | None => None
  | Some x => iget ix x
  end.

(* Apply iput to an optional value, returning a default if the value is None *)
Definition iput_opt {Ix A B} `{IxPartialLens Ix A B} `{Default A}
  ix (opt_a : option A) b : A :=
  match opt_a with
  | None => iput ix default_elem b
  | Some a => iput ix a b
  end.

(* Two indexed partial lenses can be composed if the middle type has a default
and the index types have decidable equality *)
Global Program Instance IxPartialLens_IxPartialLens Ix1 Ix2 A B C
  `{IxPartialLens Ix1 A B} `{IxPartialLens Ix2 B C}
  `{DecidableEq Ix1} `{DecidableEq Ix2} `{Default B} :
  IxPartialLens (Ix1 * Ix2) A C :=
  {|
    iget '(i1,i2) a := iget_opt i2 (iget i1 a);
    iput '(i1,i2) a c := iput i1 a (iput_opt i2 (iget i1 a) c);
  |}.
Next Obligation.
  rewrite iGetPut_eq. destruct (iget i a); apply iGetPut_eq.
Qed.
Next Obligation.
  destruct (dec_eq i1 i); [ destruct (dec_eq i2 i0) | ]; subst.
  - elimtype False; auto.
  - destruct (iget i a); simpl in H5;
      [ | elimtype False; auto ].
    rewrite iGetPut_eq. simpl. eapply iGetPut_neq; eassumption.
  - case_eq (iget i1 a); intros; rewrite H6 in H5; simpl in H5;
      [ | elimtype False; auto ].
    erewrite iGetPut_neq; try rewrite H6;
      [ reflexivity | assumption | intro; discriminate ].
Qed.
Next Obligation.
  rewrite iPutGet; [ reflexivity | ].
  destruct (iget i a); [ | simpl in H4; discriminate ].
  simpl. simpl in H4. f_equal. symmetry; apply iPutGet; assumption.
Qed.
Next Obligation.
  case_eq (iget i a); intros; simpl.
  - rewrite iGetPut_eq. simpl. repeat rewrite iPutPut_eq. reflexivity.
  - rewrite iGetPut_eq. simpl. repeat rewrite iPutPut_eq. reflexivity.
Qed.
Next Obligation.
  revert H4; case_eq (iget i a); simpl; intros; [ | elimtype False; auto ].
  rewrite iGetPut_eq. simpl.
  erewrite iPutPut; [ | rewrite H4; intro; discriminate ].
  erewrite iPutPut; [ reflexivity | eassumption ].
Qed.


(***
 *** The indexed partial lens for lists
 ***)

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
  - destruct i1; simpl in H0; elimtype False; auto.
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
  - destruct i; simpl in H; elimtype False; auto.
  - apply Lt.neq_0_lt. simpl. intro; discriminate.
  - simpl. apply Lt.lt_n_S. apply IHa. assumption.
Qed.


(* The length of a list equals the least index where iget returns None *)
Lemma lt_length_least_None A (l : list A) n :
  length l = n <->
    (iget n l = None /\
       forall i, i < n -> exists s, iget i l = Some s).
Proof.
  split; [ split | ]; intros.
  - apply nth_error_None. subst. reflexivity.
  - subst. apply nth_error_Some in H0. simpl.
    destruct (nth_error l i); [ eexists; reflexivity | ].
    elimtype False; apply H0; reflexivity.
  - revert n H; induction l; destruct n; intros; destruct H.
    + reflexivity.
    + destruct (H0 n); [ unfold lt; reflexivity | ].
      destruct n; simpl in H1; discriminate.
    + simpl in H. discriminate.
    + simpl. f_equal. apply IHl. simpl in H.
      split; [ assumption | ]. intros.
      apply (H0 (Datatypes.S i)).
      apply Lt.lt_n_S. assumption.
Qed.

Lemma self_contained_list_ixs {A} n : self_contained_ixs (B:=A) (fun i => i >= n).
Proof.
  repeat intro. simpl. revert n ix_in ix_out H H0; induction st; intros.
  - simpl.
    rewrite (proj2 (nth_error_None _ _));
      [ rewrite (proj2 (nth_error_None _ _));
        [ reflexivity | apply Nat.le_0_l ] | ].
    rewrite repeat_length.
    admit. (* straightforward *)
  - destruct ix_in.
    + assert (0 = n); [ apply (Le.le_n_0_eq n H) | ]; subst.
      elimtype False; apply H0. apply Nat.le_0_l.
    + destruct ix_out; [ reflexivity | ]. simpl.
      destruct n; [ elimtype False; apply H0; apply Nat.le_0_l | ].
      apply (IHst n).
      * apply le_S_n. assumption.
      * intro. apply H0. apply le_n_S. assumption.
Admitted.


(** * itree stuff *)

(* The effect that combines a get and a put on the current state, by modifying
the state according to the supplied function and returning the old version
before it was modified *)
Variant modifyE C : Type -> Type :=
  | Modify : forall (f : C -> C), modifyE C C.
Global Arguments Modify {C} f.

Definition sceE (C : Type) := (exceptE unit +' modifyE C +' nondetE).
