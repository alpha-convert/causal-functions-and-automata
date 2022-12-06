Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

Variable A : Type.

CoInductive autom : Type := 
| Step : (A -> A * autom) -> autom.

Definition step (m : autom) (x : A) : A * autom :=
    match m with
    | Step f => f x
    end.

Inductive lengthN : nat -> Type :=
| Empty_lengthN : lengthN 0
| Cons_lengthN : forall n (x : A), lengthN n -> lengthN (S n).

(* remove the last element *)
Definition truncate (n : nat) (l : lengthN (S n)) : lengthN n.
Proof.
  inversion l. apply X.
Defined.

Theorem trunc0 : truncate 0 = (fun _ => Empty_lengthN).
Proof.
extensionality l.
inversion l.
unfold truncate.
Admitted.

Theorem lengthN_eta_0 : forall (l : lengthN 0), l = Empty_lengthN.
Proof.
Admitted.

(* remove the first element *)
Fixpoint unshift (n : nat) (l : lengthN (S n)) : lengthN n.
Proof.
  induction n.
   - apply Empty_lengthN.
   - inversion l. apply (Cons_lengthN n x). apply IHn. exact X.
Qed.

Record omega_presheaf : Type := mkPresheaf {
  fam : nat -> Type;
  trunc : forall n, fam (S n) -> fam n
}.

Definition lengthN_pshf : omega_presheaf := mkPresheaf lengthN truncate.

Record omega_presheaf_nt (P : omega_presheaf) (Q : omega_presheaf) : Type := mkNT {
  component : forall n, fam P n -> fam Q n;
  squares : forall n, compose (component n) (trunc P n) = compose (trunc Q n) (component (S n))
}.

(* Is this the same as later???*)
Definition shift (P : omega_presheaf) : omega_presheaf :=
  mkPresheaf (fun n => fam P (S n)) (fun n => trunc P (S n)).

Definition shiftNT_component {P Q} (alpha : omega_presheaf_nt P Q) : forall n, fam (shift P) n -> fam (shift Q) n :=
  fun n => component P Q alpha (S n).

Theorem shiftNT_squares {P Q} (alpha : omega_presheaf_nt P Q) : forall n : nat,
compose
  (shiftNT_component alpha n)
  (trunc (shift P) n) =
compose (trunc (shift Q) n)
  (shiftNT_component alpha (S n)).
Proof.
  simpl. unfold shiftNT_component in *. intro n. apply (squares P Q alpha (S n)).
Qed.

Definition shiftNT {P Q} (alpha : omega_presheaf_nt P Q) : omega_presheaf_nt (shift P) (shift Q) :=
  mkNT (shift P) (shift Q) (shiftNT_component alpha) (shiftNT_squares alpha).


Definition unshiftlengthNNT_component (alpha : omega_presheaf_nt (shift lengthN_pshf) (shift lengthN_pshf)) : forall n : nat, fam lengthN_pshf n -> fam lengthN_pshf n :=
    fun n => match n with
             | 0 => fun _ => Empty_lengthN
             | S n' => component (shift lengthN_pshf) (shift lengthN_pshf) alpha n'
    end.

Theorem unshiftlengthNNT_squares (alpha : omega_presheaf_nt (shift lengthN_pshf) (shift lengthN_pshf)) : forall n : nat,
compose
  (unshiftlengthNNT_component alpha n)
  (trunc lengthN_pshf n) =
compose (trunc lengthN_pshf n)
  (unshiftlengthNNT_component alpha (S n)).
Proof.
simpl. induction n.
 - extensionality l. cbn. unfold compose. rewrite trunc0. reflexivity.
 - simpl in *. apply (squares (shift lengthN_pshf) (shift lengthN_pshf) alpha).
Qed.

(* There's a nice picture to draw here of the commutative diagrram: shiftNT pushes the indexing up by one, so
   you have squares like
   A^{n+1} <-- A^{n+2}
   |           |
   v           v
   A^{n+1} <-- A^{n+2}

   but then, since P(0) = 1, you can glue on a square like
   1 <-- A
   |     |
   v     v
   1 <-- A

   to get a full NT.
   This should probably work for any NT shift P => shift Q, by tainng a singleton set to be the zero component.
   But this happens to be a lengthN_pshf anyway.
*)
Definition unshiftlengthNNT (alpha : omega_presheaf_nt (shift lengthN_pshf) (shift lengthN_pshf)) : omega_presheaf_nt lengthN_pshf lengthN_pshf :=
    mkNT lengthN_pshf lengthN_pshf (unshiftlengthNNT_component alpha) (unshiftlengthNNT_squares alpha).

Definition len1Proj (x : fam lengthN_pshf 1) : A.
Proof.
simpl in *. inversion x. apply x0.
Qed.

Definition headApply (alpha : omega_presheaf_nt lengthN_pshf lengthN_pshf) : A -> A :=
  fun a => let l1 : fam lengthN_pshf 1 := Cons_lengthN 0 a Empty_lengthN in
           let l2 : fam lengthN_pshf 1 := component _ _ alpha 1 l1 in
           len1Proj l2.

CoFixpoint fromNT (alpha : omega_presheaf_nt lengthN_pshf lengthN_pshf) : autom :=
  Step (fun a => (headApply alpha a, fromNT (unshiftlengthNNT (shiftNT alpha)))).

Fixpoint stepN (m : autom) (n : nat) (l : lengthN n) : lengthN n :=
    match n