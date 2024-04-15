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

End PLensPerms.
