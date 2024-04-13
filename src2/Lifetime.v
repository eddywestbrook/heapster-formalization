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
Lemma current_lte_or_eq s : statusOf_lte (Some current) s ->
                            s = Some current \/ s = Some finished.
Proof.
  destruct s; [ destruct s | ]; intros.
  - left; reflexivity.
  - right; reflexivity.
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

(* Get the status of a lifetime *)
Definition lifetime : Lifetimes -> nat -> option status :=
  @nth_error status.

(* Set the status of a lifetime in a lifetime state *)
Definition replace_lifetime (l : Lifetimes) (n : nat) (new : status) : Lifetimes :=
  replace_list_index l n new.

(* FIXME: change all this to a partial lens *)

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

Definition Lifetimes_lte (ls ls' : Lifetimes) : Prop :=
  forall l, statusOf_lte (lifetime ls l) (lifetime ls' l).

Global Instance Lifetimes_lte_preorder : PreOrder Lifetimes_lte.
Proof.
  constructor; repeat intro.
  - destruct (lifetime x l); [destruct s |]; cbn; auto.
  - specialize (H l). specialize (H0 l). etransitivity; eauto.
Qed.

Lemma Lifetimes_lte_update ls l new :
  l < length ls -> statusOf_lte (lifetime ls l) (Some new) ->
  Lifetimes_lte ls (replace_list_index ls l new).
Proof.
  repeat intro. unfold lifetime. destruct (Nat.eq_dec l0 l).
  - subst. rewrite nth_error_replace_list_index_eq. assumption.
  - rewrite <- nth_error_replace_list_index_neq; try assumption.
    reflexivity.
Qed.


(* l is lte all lifetimes in a set, i.e., it subsumes them *)
Definition all_lte l (ls : nat -> Prop) lts : Prop :=
  forall l', ls l' -> statusOf_lte (lifetime lts l) (lifetime lts l').

(* All lifetimes in a set are finished *)
Definition all_finished (ls : nat -> Prop) lts : Prop :=
  forall l, ls l -> lifetime lts l = Some finished.

(* If all lifetime in ls are finished, then l is lte all of them.
   NOTE: l < length lts is probably not strictly necessary, but removing it
   would require a different version of nth_error_replace_list_index_neq *)
Lemma all_lte_finish l ls lts : l < length lts -> all_finished ls lts ->
                                all_lte l ls (replace_list_index lts l finished).
Proof.
  repeat intro. destruct (Nat.eq_dec l' l).
  - subst. reflexivity.
  - unfold lifetime.
    rewrite <- (nth_error_replace_list_index_neq _ l' l); try assumption.
    unfold all_finished, lifetime in H0.
    rewrite (H0 l' H1). apply finished_greatest.
Qed.

(* If l has at least started then it is < the # allocated lifetimes *)
Lemma lte_current_lt_length l lts :
  statusOf_lte (Some current) (lifetime lts l) -> l < length lts.
Proof.
  intro. simpl in H. unfold lifetime, Lifetimes in H.
  apply nth_error_Some; intro. rewrite H0 in H. assumption.
Qed.


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

Section LifetimeOps.
  Context {Si Ss : Type}.
  Context `{Hlens: Lens Si Lifetimes}.

  (** * Lifetime operations *)
  Definition newLifetime : itree (sceE Si) nat :=
    s <- trigger (Modify id);; (* do read first to use length without subtraction *)
    trigger (Modify (fun s =>
                       (lput s ((lget s) ++ [current]))));;
    Ret (length (lget s)).

  Definition endLifetime (l : nat) : itree (sceE Si) unit :=
    s <- trigger (Modify id);;
    match nth_error (lget s) l with
    | Some current =>
        trigger (Modify (fun s =>
                           (lput s (replace_list_index
                                      (lget s)
                                      l
                                      finished))));;
        Ret tt
    | _ => throw tt
    end.
End LifetimeOps.
