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

  Lemma iPutPutPut i a b1 b2 b3 :
    iput i (iput i (iput i a b1) b2) b3 = iput i (iput i a b1) b3.
  Proof.
    eapply iPutPut. apply iGetPut_eq.
  Qed.

  (* The permission to write to an ixplens, assuming it already has a value *)
  Program Definition ixplens_write_perm ix : @perm St :=
    {|
      pre x := iget ix x <> None;
      rely x y := iget ix x <> None -> iget ix x = iget ix y;
      guar x y := x = y \/
                    exists elem1 elem2, y = iput ix (iput ix x elem1) elem2;
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
    - destruct H as [? | H]; [ subst; assumption | ].
      destruct H0 as [? | [elem3 [elem4 ?]]]; [ subst; right; eassumption | ].
      destruct H as [elem1 [elem2 ?]]. right; subst.
      exists elem1. exists elem4.
      rewrite iPutPutPut. apply iPutPutPut.
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


  (* Read permissions are always separate *)
  Lemma ixplens_read_read_sep ix1 ix2 : ixplens_read_perm ix1 ⊥ ixplens_read_perm ix2.
  Proof.
    constructor; intros; inversion H1; reflexivity.
  Qed.


End PLensPerms.
