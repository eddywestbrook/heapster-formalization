From Coq Require Import
     Classes.Morphisms
     Relations.Relation_Operators
     Logic.JMeq
     Lists.List
     Arith.PeanoNat
     Logic.FunctionalExtensionality.

Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

From Heapster Require Export
     Permissions
     Memory
     SepStep
     Functional.

From ITree Require Import
     ITree
     ITreeFacts
     Basics.MonadState
     Basics.MonadProp
     Events.State
     Events.Exception
     Events.Nondeterminism
     Eq.Eq
     Eq.UpToTaus
     Eq.EqAxiom.

From Paco Require Import
     paco.

Import MonadNotation.
Import ListNotations.
Import ITreeNotations.

Context (Si Ss:Type).
Record PermType (A B:Type) : Type :=
  { ptApp : A -> B -> @Perms (Si*Ss) }.
Definition VPermType A := PermType Value A.
Notation "xi : T @ xs" := (ptApp _ _ T xi xs) (at level 35).

Definition starPT {Ai As Bs} (T:PermType Ai As) (U:PermType Ai Bs)
  : PermType Ai (As * Bs) :=
  {| ptApp := fun ai abs => ai : T @ fst abs * ai : U @ snd abs |}.


Definition exPerms {Ai As} {Bs:As -> Type}
  (F : forall a, PermType Ai (Bs a)) : PermType Ai (sigT Bs) :=
  {| ptApp := fun ai abs => ai : F (projT1 abs) @ (projT2 abs) |}.
Notation "'ex' ( x : A ) . T" := (exPerms (As:=A) (fun x => T)) (at level 70).

Definition either {A B C} (f:A -> C) (g:B -> C) (x:A+B): C :=
  match x with inl a => f a | inr b => g b end.
Definition or {Ai As Bs} (T1:PermType Ai As)
  (T2:PermType Ai Bs) : PermType Ai (As + Bs) :=
  {| ptApp := fun ai abs =>
     either (ptApp _ _ T1 ai) (ptApp _ _ T2 ai) abs |}.


Variant RW: Type := R | W.

Definition trueP {A B} : PermType A B :=
  {| ptApp := fun _ _ => bottom_Perms |}.

Definition ptr_perm (rw:RW) (v x:Value) : @Perms(Si*Ss) := bottom_Perms.
Definition offset (x:Value) (o:nat) : Value := x.

Definition ptr {A} '(rw,o,T) : VPermType A :=
  {| ptApp := fun x a => let p := offset x o in
     meet_Perms (fun P => exists v,
     P=ptr_perm rw v p * (p : T @ a) ) |}.

Fixpoint arr_perm {A} rw o l T
  : VPermType (Vector.t A l) :=
  match l with 0 => trueP | S l' =>
    {| ptApp := fun xi xss =>
         xi:ptr(rw,o,T)@(Vector.hd xss) *
         offset xi 1:arr_perm rw (S o) l' T@(Vector.tl xss)
    |} end.

Notation "'arr' ( rw , o , l , T )":=(arr_perm rw o l T).

Definition plusPT {A1 A2 B1 B2}
           (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1+A2) (B1+B2) :=
  {| ptApp := fun eithA eithB =>
                match (eithA,eithB) with
                | (inl a1, inl b1) => a1 : T1 @ b1
                | (inr a2, inr b2) => a2 : T2 @ b2
                | _ => top_Perms
                end |}.
Notation "T1 +T+ T2" := (plusPT T1 T2) (at level 50).

Definition timesPT {A1 A2 B1 B2}
           (T1:PermType A1 B1) (T2:PermType A2 B2) : PermType (A1*A2) (B1*B2) :=
  {| ptApp := fun a12 b12 =>  fst a12 : T1 @ fst b12 * snd a12 : T2 @ snd b12 |}.
Notation "T1 *T* T2" := (plusPT T1 T2) (at level 40).

Program Definition equals_perm {A} (a1 a2 : A): @perm (Si*Ss) := {|
  rely _ _ := True; guar s1 s2 := s1=s2; pre _ := a1=a2; |}.
Next Obligation.
repeat constructor.
Defined.
Next Obligation.
repeat constructor. intros x y z e1 e2. transitivity y; assumption.
Defined.

Definition eqp {A} (a:A): PermType A unit :=
  {| ptApp := fun a' _ => singleton_Perms (equals_perm a a') |}.

Class Lens (A B:Type) : Type :=
  { lget: A -> B; lput: A -> B -> A;
    lGetPut: forall a b, lget (lput b a) = a;
    lPutGet: forall b, lput b (lget b) = b;
    lPutPut: forall a a' b, lput (lput b a) a' = lput b a' }.
