(* begin hide *)

From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Lia.

From Heapster2 Require Import
     Utils
     Permissions
     Lifetime
     SepStep
     Typing.

From ITree Require Import
     ITree
     Eq.Eqit.

From Paco Require Import
     paco.

Import ListNotations.
(* end hide *)


(*** Helper instances for clos_refl_trans ***)

Global Instance Reflexive_clos_refl_trans {A} R : Reflexive (clos_refl_trans A R).
Proof.
  intro. apply rt_refl.
Qed.

Global Instance Transitive_clos_trans {A} R : Transitive (clos_refl_trans A R).
Proof.
  repeat intro. eapply rt_trans; eassumption.
Qed.

Global Instance PreOrder_clos_trans {A} R : PreOrder (clos_refl_trans A R).
Proof.
  constructor; typeclasses eauto.
Qed.


Section PLensPerms.
  Context {St Ix Elem} `{IxPLens:IxPartialLens Ix St Elem}.

  (* The permission to write to an ixplens, assuming it already has a value *)
  Program Definition ixplens_write_perm ix : @perm St :=
    {|
      pre x := iget ix x <> None;
      rely x y := iget ix x <> None -> iget ix x = iget ix y;
      guar x y := x = y \/
                    iget ix x <> None /\ exists elem, y = iput ix x elem;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - rewrite <- (H H1) in H0. apply H0; assumption.
  Qed.
  Next Obligation.
    constructor; repeat intro.
    - left; reflexivity.
    - destruct H; [ subst; assumption | ].
      destruct H0 as [? | [? [elem2 ?]]]; [ subst; right; eassumption | ].
      destruct H as [? [elem1 ?]]. right; subst.
      split; [ assumption | ].
      exists elem2. apply iPutPut; assumption.
  Qed.
  Next Obligation.
    rewrite <- (H H0). assumption.
  Qed.


  (* The permission to read from an ixplens, assuming it already has a value *)
  Program Definition ixplens_read_perm ix : @perm St :=
    {|
      pre x := iget ix x <> None;
      rely x y := iget ix x <> None -> iget ix x = iget ix y;
      guar x y := x = y;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - rewrite <- (H H1) in H0. apply H0; assumption.
  Qed.
  Next Obligation.
    rewrite <- (H H0). assumption.
  Qed.


  (* A write permission is greater than a read permission *)
  Lemma lte_read_write ix : ixplens_read_perm ix <= ixplens_write_perm ix.
  Proof.
    constructor; intros.
    - apply H0.
    - apply H0.
    - inversion H0; reflexivity.
    - apply I.
  Qed.

  (* Read permissions are always separate *)
  Lemma ixplens_read_read_sep ix1 ix2 : ixplens_read_perm ix1 ⊥ ixplens_read_perm ix2.
  Proof.
    constructor; intros; inversion H1; reflexivity.
  Qed.

  (* Write permissions with different indices are separate *)
  Lemma ixplens_write_write_sep ix1 ix2 :
    ix1 <> ix2 -> ixplens_write_perm ix1 ⊥ ixplens_write_perm ix2.
  Proof.
    constructor; intros.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; assumption.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; try assumption.
      intro; subst; apply H; reflexivity.
  Qed.

  (* Write and read with different indices are separate *)
  Lemma ixplens_write_read_sep ix1 ix2 :
    ix1 <> ix2 -> ixplens_write_perm ix1 ⊥ ixplens_read_perm ix2.
  Proof.
    constructor; intros.
    - inversion H2; reflexivity.
    - destruct H2 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      intro; symmetry; apply iGetPut_neq; try assumption.
      intro; subst; apply H; reflexivity.
  Qed.


  (* A set of indices is self-contained iff writing to any of them only affects
  other indices in the set *)
  (*
  Definition self_contained_ixs (ixs : Ix -> Prop) (st:St) : Prop :=
    forall ix_in ix_out elem,
      ixs ix_in -> ~ ixs ix_out ->
      iget ix_out (iput ix_in st elem) = iget ix_out st.
   *)

  (* The permission to write to any index in a set *)
  Program Definition ixplens_multi_write_perm (ixs : Ix -> Prop) : @perm St :=
    {|
      pre x := True;
      rely x y := forall ix, ixs ix -> iget ix x = iget ix y;
      guar x y :=
        clos_refl_trans _ (fun x' y' =>
                             exists ix elem, ixs ix /\ y' = iput ix x' elem) x y;
      inv x := True
    |}.
  Next Obligation.
    constructor; repeat intro.
    - reflexivity.
    - etransitivity; [ apply H | apply H0 ]; eassumption.
  Qed.


  (* A multi-write permission is always separate from a write permission to an
  index not in the set of the multi-write *)
  Lemma ixplens_write_multi_write_sep ix ixs :
    ~ ixs ix -> self_contained_ixs ixs ->
    ixplens_write_perm ix ⊥ ixplens_multi_write_perm ixs.
  Proof.
    intros not_in self_c; constructor; repeat intro.
    - clear H H0.
      assert (iget ix x = iget ix y /\ iget ix y <> None) as [? ?];
        [ | assumption ].
      induction H1.
      + destruct H as [ix' [elem [? ?]]]; subst.
        rewrite iGetPut_neq;
          [ split; [ reflexivity | assumption ] | | assumption ].
        intro; subst. apply (not_in H).
      + split; [ reflexivity | assumption ].
      + destruct (IHclos_refl_trans1 H2).
        destruct (IHclos_refl_trans2 H0).
        split; [ etransitivity | ]; eassumption.
    - destruct H1 as [? | [? [elem ?]]]; subst; [ reflexivity | ].
      symmetry; apply self_c; assumption.
  Qed.

End PLensPerms.
