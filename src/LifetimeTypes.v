
From Coq Require Import
         Lists.List.

(* NOTE: needed for \1/ notation *)
From Paco Require Import
     paco.

From ITree Require Import
     ITree
     ITreeFacts.

From Heapster Require Import
     Utils
     Permissions
     Lifetime
     SepStep
     Typing
     PermType
     LensPerms
     LifetimePerms.

Import ITreeNotations.
Import ListNotations.
Local Open Scope itree_scope.


Section LifetimeTypes.
  Context {Si Ss Ix Elem : Type} {IxPLens:IxPartialLens Ix Si Elem}.
  Context {LtLens : Lens Si Lifetimes} {IxLtSep : LensIxPLensSep LtLens IxPLens}.


  (***
   *** Permission types for lifetimes
   ***)

  (* A permission type that is valid when a lifeime is current *)
  Definition whenTp {A Bs} l (T : PermType A Bs) : PermType A Bs :=
    mkPermType (Si:=Si) (Ss:=Ss) (fun xi xss => when l (ptApp T xi xss)).

  (* A permission type that is valid after a lifeime has ended *)
  Definition afterTp {A Bs} l (T : PermType A Bs) : PermType A Bs :=
    mkPermType (Si:=Si) (Ss:=Ss) (fun xi xss => after l (ptApp T xi xss)).

  (* The permission type allowing allocation of lifetimes *)
  Definition lallocTp : PermType0 unit :=
    mkPermType0 (Ss:=Ss) (fun _ => lalloc).

  (* The permission type stating that a lifetime is finished *)
  Definition lfinishedTp : PermType1 nat unit :=
    mkPermType1 (Ss:=Ss) (fun l _ => lfinished l).

  (* The permission type stating that a lifetime is current whenever l2 is,
     i.e., that it is an ancestor of l2 / a larger lifetime containing l2 *)
  Definition lcurrentTp l2 : PermType1 nat unit :=
    mkPermType1 (Ss:=Ss) (fun l1 _ => lcurrent l1 l2).

  (* The permission type stating that we own a current lifetime, and that we can
  end it if we give up permission type Ti, in which case we get back permission
  type To *)
  Definition lownedTp ls {Bin Bout} (Tin : Bin -> Perms) (Tout : Bout -> Perms)
    : PermType1 nat (Bin -> Bout) :=
    mkPermType1 (Ss:=Ss) (fun l f => lowned l ls Tin (fun x => Tout (f x))).
  Arguments lownedTp _ {_ _} Tin%_perms Tout%_perms.

  (* Flip the argument order of ptApp *)
  Definition ptApp_flip {A Bs} (T : @PermType Si Ss A Bs) xss xi := ptApp T xi xss.

  (* The permission type giving read or write access to the value in the
  imperative state pointed to (via an ixplens) by the imperative value while the
  lifetime l is current *)
  Definition ixplensLtTp {Bs} l rw (ix : Ix) (T : PermType Elem Bs) : PermType Ix Bs :=
    mkPermType (Ss:=Ss) (fun ix xss => ixplens_ldep l rw ix (ptApp_flip T xss)).


  (***
   *** Extraction typing rules for lifetimes
   ***)

  (* If l1 contains l2 and we have a permission to l2 then we can split an
  ixplens type from lifetime l1 to lifetime l2 *)
  Lemma lownedTp_split_lifetime l1 l2 ls Bs Bin Bout T Tin Tout rw ix f xi xss :
    l1 <> l2 ->
    (l1 :: lcurrentTp l2 ▷ tt *
       xi :: @ixplensLtTp Bs l1 rw ix T ▷ xss *
       l2 :: @lownedTp ls Bin Bout Tin Tout ▷ f)
      ⊨ (xi :: ixplensLtTp l2 rw ix T ▷ xss *
           l2 :: lownedTp ls
             (fun tup => xi :: ixplensLtTp l2 Read ix T ▷ (fst tup) * Tin (snd tup))%perms
             (fun tup => xi :: ixplensLtTp l1 rw ix T ▷ (fst tup) * Tout (snd tup))%perms
             ▷ (fun tup => (fst tup, f (snd tup)))).
  Proof.
    intro; simpl; apply lowned_split_ixplens;
      try assumption; apply sep_ixplens_sep_lowned.
  Qed.


  (* Subsume lifetime l2 as a child of l1 *)
  Lemma lownedTp_subsume l1 ls1 Bin1 Bout1 Tin1 Tout1 f1 l2 ls2 Bin2 Bout2 Tin2 Tout2 f2 :
    l1 <> l2 ->
    (l1 :: @lownedTp ls1 Bin1 Bout1 Tin1 Tout1 ▷ f1 *
       l2 :: @lownedTp ls2 Bin2 Bout2 Tin2 Tout2 ▷ f2)
      ⊨
      (l1 :: @lownedTp (eq l2 \1/ ls1) Bin1 Bout1 Tin1 Tout1 ▷ f1 *
         l2 :: @lownedTp ls2 Bin2 Bout2 Tin2 Tout2 ▷ f2).
  Proof.
    intro. simpl. apply lowned_subsume. assumption.
  Qed.


End LifetimeTypes.
