(* begin hide *)
From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.OptionMonad.

From Heapster Require Import
     Utils
     Permissions
     SepStep
     Typing.

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

From Paco Require Import
     paco.

Import ListNotations.
Import ITreeNotations.

(* end hide *)

Section PermType.
  Context {Si Ss : Type}.

  (***
   *** Generalized tuple types
   ***)

  (* The tuple of 0 or more types, with the special case that a list of a single
  type maps to that type *)
  Fixpoint tuple (Ts : list Type) : Type :=
    match Ts with
    | nil => unit
    | [T] => T
    | T :: Ts' => T * tuple Ts'
    end.

  (* Cons together a head and tail of a tuple *)
  Definition consTuple {T Ts} : T -> tuple Ts -> tuple (T :: Ts) :=
    match Ts return T -> tuple Ts -> tuple (T :: Ts) with
    | nil => fun x _ => x
    | T :: Ts' => fun x xs => (x,xs)
    end.

  (* Uncons a tuple into a head and tail *)
  Definition unconsTuple {T Ts} : tuple (T :: Ts) -> T * tuple Ts :=
    match Ts return tuple (T :: Ts) -> T * tuple Ts with
    | nil => fun x => (x, tt)
    | T :: Ts' => fun tup => tup
    end.

  (* The cons of an uncons is the identity *)
  Lemma consUnconsTuple T Ts (ts : tuple (T :: Ts)) :
    consTuple (fst (unconsTuple ts)) (snd (unconsTuple ts)) = ts.
  Proof.
    destruct Ts; [ | destruct ts ]; reflexivity.
  Qed.

  (* The uncons of a cons is the identity *)
  Lemma unconsConsTuple T Ts (t : T) (ts : tuple Ts) :
    unconsTuple (consTuple t ts) = (t, ts).
  Proof.
    destruct Ts; [ destruct ts | ]; reflexivity.
  Qed.

  (* Combine two tuples into a tuple of the append of their type lists *)
  Fixpoint combineTuple {Ts Us} {struct Ts} : tuple Ts -> tuple Us -> tuple (Ts ++ Us) :=
    match Ts return tuple Ts -> tuple Us -> tuple (Ts ++ Us) with
    | [] => fun _ us => us
    | T :: Ts' =>
        fun ts us =>
          consTuple (fst (unconsTuple ts))
            (combineTuple (snd (unconsTuple ts)) us)
    end.

  (* Split a tuple of two type lists into tuples of each type list *)
  Fixpoint splitTuple {Ts Us} {struct Ts} : tuple (Ts ++ Us) -> tuple Ts * tuple Us :=
    match Ts return tuple (Ts ++ Us) -> tuple Ts * tuple Us with
    | [] => fun tup => (tt, tup)
    | T :: Ts' =>
        fun tup =>
          (consTuple (fst (unconsTuple tup))
             (fst (splitTuple (snd (unconsTuple tup)))),
            snd (splitTuple (snd (unconsTuple tup))))
    end.

  (* The beta rule for tuples: building then eliminating is the identity *)
  Lemma tupleBeta Ts Us (ts : tuple Ts) (us : tuple Us) :
    splitTuple (combineTuple ts us) = (ts, us).
  Proof.
    revert ts us; induction Ts; intros.
    - destruct ts. reflexivity.
    - simpl. rewrite unconsConsTuple. simpl. rewrite IHTs. simpl.
      rewrite consUnconsTuple. reflexivity.
  Qed.

  (* The eta rule for tuples: eliminating then building them is the identity *)
  Lemma tupleEta Ts Us (ts : tuple (Ts ++ Us)) :
    combineTuple (fst (splitTuple ts)) (snd (splitTuple ts)) = ts.
  Proof.
    revert ts; induction Ts; intros.
    - reflexivity.
    - simpl. rewrite unconsConsTuple. simpl. rewrite IHTs.
      apply consUnconsTuple.
  Qed.


  (***
   *** Permission Types
   ***)

  (* A permission type is a relation between an implementation type A and a
     list of specification types Bs as a permission set *)
  Record PermType (A : Type) (Bs : list Type) : Type :=
    { ptApp : A -> tuple Bs -> @Perms (Si * Ss) }.

  (* Helper function to build a PermType using Perms notation *)
  Definition mkPermType {A Bs} f : PermType A Bs := {| ptApp := f |}.
  Global Arguments mkPermType {_ _} f%_perms.
  (* Notation mkPermType f := {| ptApp := f |} (f in scope perms). *)

  (* Give * for permission sets higher precedence locally than multiplication *)
  Open Scope perms.

  (* We create a new scope for permission types *)
  Declare Scope perm_type.
  Delimit Scope perm_type with perm_type.
  Bind Scope perm_type with PermType.

  Global Arguments ptApp {_ _} _ _ _.
  Notation "xi :: T ▷ xss" := (ptApp T xi xss) (at level 35).


  (* A permission type with no specification types *)
  Definition PermType0 A := PermType A [].

  (* Make a PermType0 with a fixed permission set for each imperative value *)
  Definition mkPermType0 {A} (P : A -> Perms) : PermType0 A :=
    mkPermType (fun a _ => P a).

  (* A permission type with a single specification type *)
  Definition PermType1 A B := PermType A [B].
  Bind Scope perm_type with PermType1.

  (* Helper function to build a PermType with a single specification type *)
  Definition mkPermType1 {A B} (f : A -> B -> Perms) : PermType1 A B :=
    {| ptApp := f : A -> tuple [B] -> Perms |}.

  (* Imperative computation ti extracts to specification computation ts wrt
     input permission set P and output permission type U *)
  Definition extractsTo {A Bs} (P : Perms) (U : PermType A Bs) ti ts : Prop :=
    typing P (ptApp U) ti ts.

  Notation "P ⊢ ti ⤳ ts ::: U" := (extractsTo P U ti ts) (at level 60).

  (* Map a function across the specification type of a permission type, making
  permission types a form of functor; note that this mapping is contravariant,
  meaning that f : B -> C maps permission type with spec type C to B *)
  Definition mapSpecTp {A Bs Cs} (f:tuple Bs -> tuple Cs) (T:PermType A Cs) : PermType A Bs :=
    mkPermType (fun a b => a :: T ▷ (f b)).

  (* Mapping the spec type is equivalent to applying the function to xss *)
  Lemma mapSpecTpEq A Bs Cs f T xi xss :
    xi :: @mapSpecTp A Bs Cs f T ▷ xss = xi :: T ▷ f xss.
  Proof. reflexivity. Qed.

  (* Map a function across the implementation type of a permission type, making
  permission types a form of functor; note that this mapping is contravariant,
  meaning that f : B -> C maps implementation type with spec type C to B *)
  Definition mapImpTp {A B Cs} (f:A -> B) (T:PermType B Cs) : PermType A Cs :=
    mkPermType (fun a b => f a :: T ▷ b).

  (* Mapping the imp type is equivalent to applying the function to xi *)
  Lemma mapImpTpEq A B Cs f T xi xss :
    xi :: @mapImpTp A B Cs f T ▷ xss = f xi :: T ▷ xss.
  Proof. reflexivity. Qed.


  (***
   *** Simple permission types and rules for them
   ***)

  (* Turn a type with N spec types into a type with 1 spec type *)
  Definition tupleTp {Ai Bss} (T : PermType Ai Bss) : PermType1 Ai (tuple Bss) :=
    mkPermType1 (ptApp T).

  (* A tuple type can be proved from the type it is a tuple of *)
  Lemma introTupleTp Ai Bss (T : PermType Ai Bss) xi xss :
    xi :: T ▷ xss ⊨ xi :: (tupleTp T) ▷ xss.
  Proof. reflexivity. Qed.

  (* A tuple type can eliminated to the type it is a tuple of *)
  Lemma elimTupleTp Ai Bss (T : PermType Ai Bss) xi xss :
    xi :: (tupleTp T) ▷ xss ⊨ xi :: T ▷ xss.
  Proof. reflexivity. Qed.


  (* Conjoin a fixed permission set with a permission type *)
  Definition withPerms {A Bs} P (T : PermType A Bs) : PermType A Bs :=
    mkPermType (fun a b => P * a :: T ▷ b).

  (* withPerms is equivalent to a conjunction *)
  Lemma withPermsEq A Bs P (T : PermType A Bs) xi xss :
    xi :: withPerms P T ▷ xss = P * xi :: T ▷ xss.
  Proof. reflexivity. Qed.

  (* The frame rule for specification extraction *)
  Lemma extractsFrame A Bs P Q (U : PermType A Bs) ti ts :
    P ⊢ ti ⤳ ts ::: U ->
    Q * P ⊢ ti ⤳ ts ::: withPerms Q U.
  Proof.
    intro. unfold extractsTo. simpl.
    setoid_rewrite (sep_conj_Perms_commut Q).
    apply typing_frame. assumption.
  Qed.


  (* The trivially "true" permission type *)
  Definition trueTp {A} : PermType0 A := mkPermType0 (fun _ => bottom_Perms).

  (* True can be trivially added to any permission type *)
  Lemma introTrueTp P A (xi:A) : P ⊨ P * xi :: trueTp ▷ tt.
  Proof.
    simpl. rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.

  (* True can be trivially eliminated from any permission type *)
  Lemma elimTrueTp P A (xi:A) : P * xi :: trueTp ▷ tt ⊨ P.
  Proof.
    simpl. rewrite sep_conj_Perms_commut.
    rewrite sep_conj_Perms_bottom_identity. reflexivity.
  Qed.


  (* The trivially "false" or contradictory permission type *)
  Definition falseTp {A} : PermType0 A := mkPermType0 (fun _ => top_Perms).

  (* False can be eliminated to any permission set *)
  Lemma elimFalseTp P A (xi:A) : xi :: falseTp ▷ tt ⊨ P.
  Proof.
    apply bigger_Perms_entails. apply top_Perms_is_top.
  Qed.


  (***
   *** The separating conjunction permission type
   ***)

  (* The separating conjunction of two permission types. The permission types
     both apply to the same implementation value of type Ai, but each relates
     this value to different specification values *)
  Definition starTp {Ai Bs1 Bs2} (T1 : PermType Ai Bs1) (T2 : PermType Ai Bs2)
    : PermType Ai (Bs1 ++ Bs2) :=
    {| ptApp := fun ai bs =>
                  (ai :: T1 ▷ fst (splitTuple bs)) * (ai :: T2 ▷ snd (splitTuple bs)) |}.
  Notation "T1 * T2" := (starTp T1 T2) : perm_type.

  (* Commutativity for the star type *)
  Lemma starTpCommute Ai Bs1 Bs2
    (T1 : PermType Ai Bs1) (T2 : PermType Ai Bs2) xi xss1 xss2
    : xi :: T1 * T2 ▷ combineTuple xss1 xss2
        ⊨ xi :: T2 * T1 ▷ combineTuple xss2 xss1.
  Proof.
    simpl. rewrite sep_conj_Perms_commut. repeat rewrite tupleBeta. reflexivity.
  Qed.

  (* Associativity for the star type *)
  Lemma starTpAssoc Ai Bs1 Bs2 Bs3
    (T1 : PermType Ai Bs1) (T2 : PermType Ai Bs2) (T3 : PermType Ai Bs3)
    xi xss1 xss2 xss3
    : xi :: (T1 * (T2 * T3)) ▷ combineTuple xss1 (combineTuple xss2 xss3)
        ⊨ xi :: ((T1 * T2) * T3) ▷ combineTuple (combineTuple xss1 xss2) xss3.
  Proof.
    simpl. rewrite sep_conj_Perms_assoc. repeat rewrite tupleBeta. simpl.
    repeat rewrite tupleBeta. reflexivity.
  Qed.


  (***
   *** Permission type constructors that operate on both spec and impl types
   ***)

  (* The sum of two permission types *)
  Definition sumTp {A1 A2 B1 B2} (T1 : PermType1 A1 B1) (T2 : PermType1 A2 B2)
    : PermType1 (A1 + A2) (B1 + B2) :=
    mkPermType1 (fun eithA eithB =>
                   match (eithA, eithB) with
                   | (inl a1, inl b1) => a1 :: T1 ▷ b1
                   | (inr a2, inr b2) => a2 :: T2 ▷ b2
                   | _ => top_Perms
                   end).
  Notation "T1 + T2" := (sumTp T1 T2) : perm_type.

  (* The left introduction rule for sum types *)
  Lemma introSumTpL {A1 A2 B1 B2} (T1 : PermType1 A1 B1) (T2 : PermType1 A2 B2) xi xs :
    xi :: T1 ▷ xs ⊨ inl xi :: T1 + T2 ▷ inl xs.
  Proof. reflexivity. Qed.

  (* The right introduction rule for sum types *)
  Lemma introSumTpR {A1 A2 B1 B2} (T1 : PermType1 A1 B1) (T2 : PermType1 A2 B2) xi xs :
    xi :: T2 ▷ xs ⊨ inr xi :: T1 + T2 ▷ inr xs.
  Proof. reflexivity. Qed.

  (* The elimination rule for sum types relates pattern-matches on both sides *)
  Lemma elimSumTp {Ai Bi As Bs Ri Rss} (T1 : PermType1 Ai As) (T2 : PermType1 Bi Bs)
    (U : PermType Ri Rss) xi ti1 ti2 xs ts1 ts2 :
    (forall xi1 xs1, xi1 :: T1 ▷ xs1 ⊢ ti1 xi1 ⤳ ts1 xs1 ::: U) ->
    (forall xi2 xs2, xi2 :: T2 ▷ xs2 ⊢ ti2 xi2 ⤳ ts2 xs2 ::: U) ->
    xi :: T1 + T2 ▷ xs ⊢ sum_rect _ ti1 ti2 xi ⤳ sum_rect _ ts1 ts2 xs ::: U.
  Proof.
    intros; destruct xi; destruct xs; simpl;
      solve [apply typing_top | apply H | apply H0].
  Qed.


  (* The product of two permission types *)
  Definition prodTp {A1 A2 Bs1 Bs2} (T1 : PermType A1 Bs1) (T2 : PermType A2 Bs2)
    : PermType (A1 * A2) (Bs1 ++ Bs2) :=
    {| ptApp := fun a12 b12 =>
                  fst a12 :: T1 ▷ fst (splitTuple b12)
                  * snd a12 :: T2 ▷ snd (splitTuple b12) |}.
  Notation "T1 ⊗ T2" := (prodTp T1 T2) (at level 40) : perm_type.

  (* FIXME: intro and elim rules for products *)


  (***
   *** Permission type constructors that operate on spec types
   ***)

  (* The existential type, where the existential is in the specification *)
  Definition existsTp {Ai As} {Bs : As -> Type}
             (F : forall a, PermType1 Ai (Bs a)) : PermType1 Ai (sigT Bs) :=
    mkPermType1 (fun ai abs => ai :: F (projT1 abs) ▷ (projT2 abs)).
  Notation "'ex' ( x 'oftype' A ) T" :=
    (existsTp (As:=A) (fun x => T)) (at level 70) : perm_type.

  (* An existential type can be proved from any instance of the existential *)
  Lemma introExistsTp Ai As Bs (F : forall (a:As), PermType1 Ai (Bs a)) xi a xss :
      xi :: (F a) ▷ xss ⊨ xi :: (existsTp F) ▷ existT _ a xss.
  Proof. reflexivity. Qed.

  (* An existential type can be eliminated to an instance of the existential *)
  Lemma elimExistsTp Ai As Bs (F : forall (a:As), PermType1 Ai (Bs a)) xi xss :
      xi :: (existsTp F) ▷ xss ⊨ xi :: F (projT1 xss) ▷ projT2 xss.
  Proof. reflexivity. Qed.


  (* The disjunctive type, where the disjunction is in the specification *)
  Definition orTp {Ai As Bs} (T1 : PermType1 Ai As) (T2:PermType1 Ai Bs)
    : PermType1 Ai (As + Bs) :=
    mkPermType1 (fun ai abs => sum_rect _ (ptApp T1 ai) (ptApp T2 ai) abs).

  (* A disjunctive type can be proved from the LHS type *)
  Lemma introOrTp1 Ai As Bs (T1 : PermType1 Ai As) (T2:PermType1 Ai Bs) xi xs :
      xi :: T1 ▷ xs ⊨ xi :: (orTp T1 T2) ▷ inl xs.
  Proof. reflexivity. Qed.

  (* A disjunctive type can be proved from the RHS type *)
  Lemma introOrTp2 Ai As Bs (T1 : PermType1 Ai As) (T2:PermType1 Ai Bs) xi xs :
      xi :: T2 ▷ xs ⊨ xi :: (orTp T1 T2) ▷ inr xs.
  Proof. reflexivity. Qed.

  (* A disjunctive type can be eliminated by a match in the specification *)
  Lemma elimOrTp Ai As Bs (T1 : PermType1 Ai As) (T2:PermType1 Ai Bs)
                 Ri Rss (U : PermType Ri Rss) xi xs ti ts1 ts2 :
      (forall xs1, xi :: T1 ▷ xs1 ⊢ ti ⤳ ts1 xs1 ::: U) ->
      (forall xs2, xi :: T2 ▷ xs2 ⊢ ti ⤳ ts2 xs2 ::: U) ->
      xi :: orTp T1 T2 ▷ xs ⊢ ti ⤳ sum_rect _ ts1 ts2 xs ::: U.
  Proof.
    intros. destruct xs; simpl; [ apply H | apply H0 ].
  Qed.


  (***
   *** Permission type constructors that operate on impl types
   ***)

  (* The permission type stating that an imperative object equals a *)
  Definition eqTp {A} (a : A): PermType0 A :=
    mkPermType0 (fun a' => prop_Perms (a' = a)).

  (* FIXME: add rules for eqTp *)


  (* Permission type stating that an optional implementation value is a Some
  value that relates to the specification value via the supplied T *)
  Definition someImplTp {Ai Bss} (T : PermType Ai Bss) : PermType (option Ai) Bss :=
    mkPermType (fun opt_xi xss =>
                  match opt_xi with
                  | Some xi => xi :: T ▷ xss
                  | None => top_Perms
                  end).

  (* Some introduction rule for optionImplTp *)
  Lemma introSomeImplTp Ai Bss T xi xss :
    xi :: T ▷ xss ⊨ Some xi :: @someImplTp Ai Bss T ▷ xss.
  Proof. reflexivity. Qed.

  (* Elimination rule for optionImplTp has a getOpt in the implementation *)
  Lemma elimSomeImplTp Ai Bss T Ri Rss (U : PermType Ri Rss) opt_xi xss ti ts :
      (forall xi, xi :: T ▷ xss ⊢ ti xi ⤳ ts ::: U) ->
      opt_xi :: @someImplTp Ai Bss T ▷ xss ⊢ (xi <- getOpt opt_xi;; ti xi) ⤳ ts ::: U.
  Proof.
    intro. destruct opt_xi; [ | apply typing_top ]. simpl.
    unfold extractsTo. rewrite bind_ret_l. apply H.
  Qed.


  (***
   *** Recursive and reachability permissions
   ***)

  (** The ordering on permission types is just the lifting of that on Perms *)
  Definition lte_PermType {A Bs} (T1 T2 : PermType A Bs): Prop :=
    forall a b, lte_Perms (ptApp T1 a b) (ptApp T2 a b).

  (** Equals on PermType is just the symmetric closure of the ordering *)
  Definition eq_PermType {A Bs} (T1 T2 : PermType A Bs): Prop :=
    lte_PermType T1 T2 /\ lte_PermType T2 T1.

  Global Instance PreOrder_lte_PermType A B : PreOrder (@lte_PermType A B).
  Proof.
    constructor; intro; intros; intros a b.
    - reflexivity.
    - etransitivity; [ apply H | apply H0 ].
  Qed.

  Global Instance Equivalence_eq_PermType A B : Equivalence (@eq_PermType A B).
  Proof.
    constructor; intro; intros.
    - split; reflexivity.
    - destruct H; split; assumption.
    - destruct H; destruct H0; split; etransitivity; eassumption.
  Qed.

  Global Instance Proper_eq_PermType_ptApp A B :
    Proper (eq_PermType ==> eq ==> eq ==> eq_Perms) (@ptApp A B).
  Proof.
    intros T1 T2 eT a1 a2 ea b1 b2 eb. rewrite ea; rewrite eb.
    destruct eT. split; [ apply H | apply H0 ].
  Qed.

  (** The meet on permission types is just the lifitng of that on Perms *)
  Definition meet_PermType {A B} (Ts : PermType A B -> Prop) : PermType A B :=
    {| ptApp := fun a b => meet_Perms (fun P => exists T, Ts T /\ P = (a :: T ▷ b)) |}.

  (** Meet is a lower bound for PermType *)
  Lemma lte_meet_PermType {A B} (Ts : PermType A B -> Prop) T:
    Ts T -> lte_PermType (meet_PermType Ts) T.
  Proof.
    intros ts_t a b. apply lte_meet_Perms. exists (ptApp T a b); split; eauto.
    reflexivity.
  Qed.

  (** Meet is the greatest lower bound for PermType *)
  Lemma meet_PermType_max {A B} (Ts : PermType A B -> Prop) T:
    (forall T', Ts T' -> lte_PermType T T') ->
    lte_PermType T (meet_PermType Ts).
  Proof.
    intros lte_T_Ts a b. apply meet_Perms_max. intros P [ T' [ Ts_T' P_eq ]].
    rewrite P_eq. apply (lte_T_Ts T' Ts_T' a b).
  Qed.

  (* The least fixed-point permission type is defined via the standard
     Knaster-Tarski construction as the meet of all F-closed permission types.
     Note that F is required to preserve the specification type list *)
  Definition fixTp {A B} (F : PermType A B -> PermType A B)
             {prp : Proper (lte_PermType ==> lte_PermType) F} : PermType A B :=
    meet_PermType (fun T => lte_PermType (F T) T).

  (** First we prove that fixTp is itself F-closed *)
  Lemma fixTp_F_closed {A B} (F : PermType A B -> PermType A B)
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    lte_PermType (F (fixTp F)) (fixTp F).
  Proof.
    intros a b. apply meet_PermType_max. intros T' lte_FT'.
    transitivity (F T'); [ | assumption ]. apply prp.
    apply lte_meet_PermType. assumption.
  Qed.

  (** Then we prove that fixTp is a fixed-point *)
  Lemma fixTp_fixed_point {A B} (F : PermType A B -> PermType A B)
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    eq_PermType (fixTp F) (F (fixTp F)).
  Proof.
    split; [ | apply fixTp_F_closed ].
    apply lte_meet_PermType. apply prp. apply fixTp_F_closed.
  Qed.

  (* Typeclass capturing that X is a fixed-point of G *)
  Class FixedPoint (G : Type -> Type) X : Type :=
    { foldFP : G X -> X;
      unfoldFP : X -> G X;
      foldUnfold : forall gx, unfoldFP (foldFP gx) = gx;
      unfoldFold : forall x, foldFP (unfoldFP x) = x; }.

  (* A generalization of the least fixed-point type that allows the functor F to
     change the specification type using a type function G, and uses a
     fixed-point X of G as the specification type *)
  Program Definition muTp {A G X} `{FixedPoint G X}
             (F : PermType1 A X -> PermType1 A (G X))
             {prp : Proper (lte_PermType ==> lte_PermType) F}
    : PermType1 A X :=
    @fixTp A [X] (fun T => mapSpecTp unfoldFP (F T)) _.
  Next Obligation.
    intros T1 T2 leqT a x. simpl. apply prp. assumption.
  Defined.

  (* muTp is a fixed-point wrt mapSpecTp *)
  Lemma muTp_fixed_point {A G X} `{FixedPoint G X}
        (F : PermType1 A X -> PermType1 A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    eq_PermType (muTp F) (mapSpecTp unfoldFP (F (muTp F))).
  Proof.
    apply (fixTp_fixed_point (fun T : PermType1 A X => mapSpecTp unfoldFP (F T))).
  Qed.

  Lemma muTp_fixed_point' {A G X} `{FixedPoint G X}
        (F : PermType1 A X -> PermType1 A (G X))
        {prp : Proper (lte_PermType ==> lte_PermType) F} :
    lte_PermType (mapSpecTp unfoldFP (F (muTp F))) (muTp F).
  Proof.
    apply (fixTp_fixed_point (fun T : PermType1 A X => mapSpecTp unfoldFP (F T))).
  Qed.

  (* The functor whose fixed-point generates the list type *)
  Definition mu_list A := fun R => sum unit (A * R).

  (* Proof that the list type is the fixed-point of mu_list *)
  Global Program Instance fixed_point_list A : FixedPoint (mu_list A) (list A)
    :=
    {
      foldFP := fun s => match s with
                      | inl _ => @nil A
                      | inr (h, t) => (cons h t)
                      end;
      unfoldFP := fun l => match l with
                        | nil => inl tt
                        | cons h t => inr _ (h, t)
                        end;
    }.
  Next Obligation.
    destruct gx.
    - destruct u. auto.
    - destruct p. auto.
  Defined.
  Next Obligation.
    destruct x; auto.
  Defined.

End PermType.


(* Re-declaring notations and scopes outside the section *)

Declare Scope perm_type.
Delimit Scope perm_type with perm_type.
Bind Scope perm_type with PermType.

(* Notation mkPermType f := {| ptApp := f |} (f in scope perms). *)
Notation "P ⊢ ti ⤳ ts ::: U" := (typing P (@ptApp _ _ _ _ U) ti ts) (at level 60).
Notation "xi :: T ▷ xs" := (@ptApp _ _ _ _ T xi xs) (at level 35).
Notation "T1 + T2" := (sumTp T1 T2) : perm_type.
Notation "T1 ⊗ T2" := (prodTp T1 T2) (at level 40) : perm_type.
Notation "T1 * T2" := (starTp T1 T2) : perm_type.
Notation "'ex' ( x 'oftype' A ) T" :=
  (existsTp (As:=A) (fun x => T)) (at level 70) : perm_type.
