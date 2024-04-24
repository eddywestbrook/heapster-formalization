(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Logic.FunctionalExtensionality
     Logic.Decidable
     Lists.List
     Lia
     Classes.RelationClasses
     Classes.Morphisms
     FSets.FMaps.

From Heapster2 Require Import
     Utils.

From ITree Require Import
     ITree
     Events.Exception.

Import ListNotations.
Import ITreeNotations.
Local Open Scope itree_scope.
(* end hide *)

Variant status := current | finished.

Definition status_lte (s1 s2 : status) : Prop :=
  match s1, s2 with
  | finished, current => False
  | _, _ => True
  end.
Global Instance status_lte_preorder : PreOrder status_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; constructor.
  - destruct x, y, z; auto.
Qed.

Definition statusOf_lte (s1 s2 : option status) : Prop :=
  match s1, s2 with
  | Some s1, Some s2 => status_lte s1 s2
  | Some _, None => False
  | _, _ => True
  end.

(* statusOf_lte is a preorder *)
Global Instance statusOf_lte_preorder : PreOrder statusOf_lte.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; cbn; auto. reflexivity.
  - destruct x, y, z; cbn in *; intuition.
    etransitivity; eauto.
Qed.

(* Also known as antisymmetry *)
Lemma statusOf_lte_eq s1 s2 : statusOf_lte s1 s2 -> statusOf_lte s2 s1 -> s1 = s2.
Proof.
  destruct s1 as [[ | ] | ]; destruct s2 as [[ | ] | ]; simpl; intros;
    try reflexivity; elimtype False; assumption.
Qed.

(* Finished is the greatest status *)
Lemma finished_greatest s : statusOf_lte s (Some finished).
Proof.
  destruct s as [[ | ] | ]; simpl; auto.
Qed.

(* If a status is at least finished then it equals finished *)
Lemma finished_lte_eq s : statusOf_lte (Some finished) s -> s = Some finished.
Proof.
  apply statusOf_lte_eq. apply finished_greatest.
Qed.

(* If s has at least started, then it is either current or finished *)
Lemma current_lte_Some s : statusOf_lte (Some current) s ->
                           exists status, s = Some status.
Proof.
  destruct s; [ destruct s | ]; intros.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - simpl in H. elimtype False; assumption.
Qed.


(** [s1] subsumes [s2], now with unstarted lifetimes (None) *)
Definition statusOf_subsumes (s1 s2 : option status) : Prop :=
  match s1, s2 with
  (* [s1] can't end before [s2] *)
  | Some finished, Some finished => True
  | Some finished, _ => False
  (* [s2] can't start before [s1] *)
  | None, Some _ => False
  | _, _ => True
  end.

Global Instance statusOf_subsumes_preorder : PreOrder statusOf_subsumes.
Proof.
  constructor; repeat intro; subst; auto.
  - destruct x; [destruct s |]; cbn; auto.
  - destruct x, y, z; cbn in *; intuition; destruct s, s0; intuition.
Qed.

(* A lifetime state is a list of allocated lifetimes and their statuses *)
Definition Lifetimes := list status.

Section LifetimeLens.
  Context {S} `{Lens S Lifetimes}.

  (* Get the status of a lifetime *)
  Definition lifetime (st:S) l : option status := iget l st.

  (* Set the status of a lifetime in a lifetime state *)
  Definition replace_lifetime (st:S) l new := iput l st new.

  (* Set the statue of a lifetime to be finished *)
  Definition end_lifetime (st:S) l := replace_lifetime st l finished.

  Lemma replace_lifetime_eq st l new :
    lifetime (replace_lifetime st l new) l = Some new.
  Proof.
    unfold lifetime, replace_lifetime. apply iGetPut_eq.
  Qed.

  Lemma end_lifetime_eq st l : lifetime (end_lifetime st l) l = Some finished.
  Proof. apply replace_lifetime_eq. Qed.

  (* If l has at least started then it is < the # allocated lifetimes *)
  Lemma lte_current_lt_length l st :
    statusOf_lte (Some current) (lifetime st l) -> l < length (lget st).
  Proof.
    intro. unfold lifetime, Lifetimes in H0. simpl in H0.
    apply nth_error_Some; intro. rewrite H1 in H0. assumption.
  Qed.

  Lemma end_lifetime_neq st l l' :
    l' <> l -> statusOf_lte (Some current) (lifetime st l) ->
    lifetime (end_lifetime st l) l' = lifetime st l'.
  Proof.
    intros; unfold lifetime, end_lifetime, replace_lifetime.
    simpl. rewrite lGetPut.
    symmetry.
    apply nth_error_replace_list_index_neq;
      [ apply lte_current_lt_length | ]; assumption.
  Qed.

  (* Setting a lifetime to what it already is does nothing *)
  Lemma eq_replace_lifetime (st:S) l s :
    lifetime st l = Some s -> replace_lifetime st l s = st.
  Proof.
    unfold lifetime, replace_lifetime.
    intro. eapply iPutGet; assumption.
  Qed.

  Lemma replace_lifetime_twice (st:S) l s1 s2 :
    lifetime st l <> None ->
    replace_lifetime (replace_lifetime st l s1) l s2 = replace_lifetime st l s2.
  Proof.
    unfold lifetime, replace_lifetime; intros.
    eapply iPutPut; eassumption.
  Qed.

(*
(* Get the status of a lifetime in a state that contains lifetimes *)
Definition get_lt {S} {Hlens: Lens S Lifetimes} (st:S) l : option status :=
  lifetime (lget st) l.

(* Set the status of a lifetime in a state that contains lifetimes *)
Definition set_lt {S} {Hlens: Lens S Lifetimes} (st:S) l status : S :=
  lput st (replace_lifetime (lget st) l status).

(* Set the status of a lifetime in a state if one is given *)
Definition set_lt_opt {S} {Hlens: Lens S Lifetimes} (st:S) l opt_s : S :=
  match opt_s with
  | None => st
  | Some s => set_lt st l s
  end.

(* The get-put rule for get_lt and set_lt *)
Lemma get_lt_set_lt {S} {Hlens: Lens S Lifetimes} (st:S) l status :
  get_lt (set_lt st l status) l = Some status.
Proof.
  unfold get_lt, set_lt, replace_lifetime, lifetime. intros.
  rewrite lGetPut. apply nth_error_replace_list_index_eq.
Qed.

(* The put-get rule for get_lt and set_lt *)
Lemma set_lt_get_lt {S} {Hlens: Lens S Lifetimes} (st:S) l :
  set_lt_opt st l (get_lt st l) = st.
Proof.
  unfold set_lt_opt, set_lt, get_lt, replace_lifetime, lifetime.
  case_eq (@nth_error status (lget (B:=Lifetimes) st) l);
    [ | reflexivity ].
  intros. rewrite replace_list_index_eq; [ apply lPutGet | assumption ].
Qed.

(* set_lt is idempotent *)
Lemma set_lt_idem {S} {Hlens: Lens S Lifetimes} (st:S) l status :
  set_lt (set_lt st l status) l status = set_lt st l status.
Proof.
  unfold set_lt, replace_lifetime. rewrite lPutPut.
  rewrite lGetPut. rewrite replace_list_index_idem.
  reflexivity.
Qed.

(* Setting a lifetime twice keeps the final value if it was already set *)
Lemma set_lt_set_lt {S} {Hlens: Lens S Lifetimes} (st:S) l s0 s1 s2 :
  get_lt st l = Some s0 ->
  set_lt (set_lt st l s1) l s2 = set_lt st l s2.
Proof.
  unfold get_lt, set_lt, replace_lifetime, lifetime. intros.
  rewrite lPutPut. rewrite lGetPut.
  rewrite replace_list_index_twice; [ reflexivity | ].
  apply nth_error_Some. intro. rewrite H0 in H. discriminate.
Qed.

(* Setting a lifetime to what it already is does nothing *)
Lemma set_lt_eq {S} {Hlens: Lens S Lifetimes} (st:S) l s :
  lifetime (lget st) l = Some s -> set_lt st l s = st.
Proof.
  unfold lifetime, set_lt, replace_lifetime. intros.
  rewrite replace_list_index_eq; [ | assumption ].
  apply lPutGet.
Qed.

(* End a lifetime in a state that contains lifetimes *)
Definition end_lt {S} {Hlens: Lens S Lifetimes} (st:S) l : S :=
  set_lt st l finished.

(* end_lt is idempotent *)
Lemma end_lt_end_lt {S} {Hlens: Lens S Lifetimes} (st:S) l :
  end_lt (end_lt st l) l = end_lt st l.
Proof. apply set_lt_idem. Qed.


(** [n1] in the lifetime list [x1] subsumes [n2] in the lifetime list [x2] *)
Definition subsumes n1 n2 x1 x2 :=
  statusOf_subsumes (lifetime x1 n1) (lifetime x2 n2).
*)

  (* All the lifetimes have not gone backwards in going between two states *)
  Definition Lifetimes_lte (st1 st2 : S) : Prop :=
    forall l, statusOf_lte (lifetime st1 l) (lifetime st2 l).

  Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
  Proof.
    constructor; repeat intro.
    - destruct (lifetime x l); [destruct s |]; cbn; auto.
    - specialize (H0 l). specialize (H1 l). etransitivity; eauto.
  Qed.

  Lemma Lifetimes_lte_update st l new :
    statusOf_lte (Some current) (lifetime st l) ->
    statusOf_lte (lifetime st l) (Some new) ->
    Lifetimes_lte st (replace_lifetime st l new).
  Proof.
    repeat intro. unfold lifetime, replace_lifetime. destruct (Nat.eq_dec l0 l).
    - subst. rewrite iGetPut_eq. assumption.
    - case_eq (iget l0 st); intros; [ | apply I ].
      erewrite iGetPut_neq; try rewrite H2;
        [ reflexivity | assumption | intro; discriminate ].
  Qed.

  (* Lifetimes_lte implies the length gets no shorter *)
  Lemma Lifetimes_lte_length_lte st1 st2 :
    Lifetimes_lte st1 st2 -> length (lget st1) <= length (lget st2).
  Proof.
    unfold Lifetimes_lte, lifetime, Lifetimes. simpl.
    generalize (@lget S (list status) _ st2). clear st2.
    generalize (@lget S (list status) _ st1). clear st1.
    intro l1; induction l1; intros l2 ?; [ | destruct l2 ].
    - apply le_0_n.
    - elimtype False; apply (H0 0).
    - simpl. apply le_n_S. apply IHl1. intro n.
      apply (H0 (Datatypes.S n)).
  Qed.


  (* l is lte all lifetimes in a set, i.e., it subsumes them *)
  Definition all_lte l (ls : nat -> Prop) st : Prop :=
    forall l', ls l' -> statusOf_lte (lifetime st l) (lifetime st l').

  (* l is lte all lifetimes in the emptty set *)
  Lemma all_lte_empty l st : all_lte l (fun _ : nat => False) st.
  Proof. repeat intro; elimtype False; assumption. Qed.

  (* All lifetimes in a set are finished *)
  Definition all_finished (ls : nat -> Prop) st : Prop :=
    forall l, ls l -> lifetime st l = Some finished.

  (* If all lifetime in ls are finished, then l is lte all of them *)
  Lemma all_lte_finish l ls st :
    all_finished ls st -> all_lte l ls (replace_lifetime st l finished).
  Proof.
    repeat intro. destruct (Nat.eq_dec l' l).
    - subst. reflexivity.
    - unfold lifetime, replace_lifetime.
      rewrite iGetPut_eq.
      assert (iget l' st = Some finished); [ apply H0; assumption | ].
      erewrite iGetPut_neq; try rewrite H2;
        [ reflexivity | assumption | intro; discriminate ].
  Qed.


(* FIXME: remove all this

Lemma subsumes_1_none_inv : forall s n1 n2,
    lifetime s n1 = None ->
    subsumes n1 n2 s s ->
    lifetime s n2 = None.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n2); auto. destruct s0; contradiction.
Qed.

Lemma subsumes_1_finished_inv : forall s n1 n2,
    lifetime s n1 = Some finished ->
    subsumes n1 n2 s s ->
    lifetime s n2 = Some finished.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n2); auto. 2: inversion H0. destruct s0; auto; contradiction.
Qed.

Lemma subsumes_2_none_inv : forall s n1 n2,
    lifetime s n2 = None ->
    subsumes n1 n2 s s ->
    lifetime s n1 = None \/ lifetime s n1 = Some current.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. destruct s0; auto. contradiction.
Qed.

Lemma subsumes_2_current_inv : forall s n1 n2,
    lifetime s n2 = Some current ->
    subsumes n1 n2 s s ->
    lifetime s n1 = Some current.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. 2: inversion H0.
  destruct s0; auto. contradiction.
Qed.

Lemma subsumes_2_finished_inv : forall s n1 n2,
    lifetime s n2 = Some finished ->
    subsumes n1 n2 s s ->
    lifetime s n1 = Some current \/ lifetime s n1 = Some finished.
Proof.
  intros. red in H0. rewrite H in H0.
  destruct (lifetime s n1); auto. 2: inversion H0.
  destruct s0; auto.
Qed.
*)

End LifetimeLens.


(** * Lifetime operations *)

Section LifetimeOps.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  (* Create and return a new lifetime as the length of the Lifetimes state *)
  Definition newLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify (fun s => iput (length (lget s)) s current));;
    Ret (length (lget s)).

  (* End a lifetime by setting it to finished *)
  Definition endLifetime (l : nat) : itree (sceE Si) unit :=
    trigger (Modify (fun s => iput l s finished));;
    Ret tt.

End LifetimeOps.
