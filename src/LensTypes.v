
From Coq Require Import
         Lists.List.

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
     LensPerms.

Import ITreeNotations.
Import ListNotations.
Local Open Scope itree_scope.


Section PLensTypes.
  Context {Si Ss Ix Elem : Type} {IxPLens:IxPartialLens Ix Si Elem}.


  (***
   *** The permission type associated with an indexed partial lens
   ***)

  Definition ixplensTp {Bs} rw (T : @PermType Si Ss Elem Bs) : PermType Ix Bs :=
    mkPermType (fun ix bs => ixplens_dep rw ix (fun elem => ptApp T elem bs)).

  Lemma ixplensRead Bs Ri Rss T (U : PermType Ri Rss) rw ix (bs : tuple Bs) ti ts :
    (forall elem,
        (ix :: ixplensTp rw (eqTp elem) ▷ tt * elem :: T ▷ bs)
          ⊢ ti elem ⤳ ts ::: U) ->
    ix :: ixplensTp rw T ▷ bs ⊢ (elem <- readIx ix;; ti elem) ⤳ ts ::: U.
  Proof.
    intro.
    rewrite <- (bind_ret_l tt (fun x => ts)).
    eapply typing_bind; [ | intros; apply H ].
    unfold readIx. rewrite <- (bind_ret_l tt (fun x => Ret tt)).
    eapply typing_bind; [ apply typing_read_L | ]. intros. simpl.
    rewrite (ixplens_read_ent _ _ _ (iget ix r1));
      [ | intros; destruct x; subst; reflexivity ].
    apply typing_meet. intros.
    destruct H0 as [elem [? ?]]; subst.
    rewrite H0. simpl. apply typing_ret. reflexivity.
  Qed.
