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

Definition exec (m : autom) (x : A) : A :=
    fst (step m x).

Inductive lengthN : nat -> Type :=
| Empty_lengthN : lengthN 0
| Snoc_lengthN {n} : lengthN n -> A -> lengthN (S n).


(* remove the first element *)
Definition truncate {n : nat} (l : lengthN (S n)) : lengthN n := 
  match l in lengthN (S n) return lengthN n with
  | Snoc_lengthN l _ => l
  end.


Theorem trunc_0 : forall (l : lengthN 1), truncate l = Empty_lengthN.
Proof.
Admitted.

Theorem lengthN_eta_0 : forall (l : lengthN 0), l = Empty_lengthN.
Proof.
Admitted.

Theorem lengthN_eta_S : forall n, forall (l : lengthN (S n)), exists x , l = Snoc_lengthN (truncate l) x.
Proof.
Admitted.


Record omega_presheaf : Type := mkPresheaf {
  fam : nat -> Type;
  restrict : forall n, fam (S n) -> fam n
}.

Definition lengthN_pshf : omega_presheaf := mkPresheaf lengthN (fun _ => truncate).

Record omega_presheaf_nt (P : omega_presheaf) (Q : omega_presheaf) : Type := mkNT {
  component : forall n, fam P n -> fam Q n;
  squares : forall n, compose (component n) (restrict P n) = compose (restrict Q n) (component (S n))
}.

(* Is this the same as later???*)
Definition shift (P : omega_presheaf) : omega_presheaf :=
  mkPresheaf (fun n => fam P (S n)) (fun n => restrict P (S n)).

Definition shiftNT_component {P Q} (alpha : omega_presheaf_nt P Q) : forall n, fam (shift P) n -> fam (shift Q) n :=
  fun n => component P Q alpha (S n).

Theorem shiftNT_squares {P Q} (alpha : omega_presheaf_nt P Q) : forall n : nat,
compose
  (shiftNT_component alpha n)
  (restrict (shift P) n) =
compose (restrict (shift Q) n)
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
  (restrict lengthN_pshf n) =
compose (restrict lengthN_pshf n)
  (unshiftlengthNNT_component alpha (S n)).
Proof.
simpl. induction n.
 - extensionality l. cbn. unfold compose. rewrite trunc_0. reflexivity.
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
simpl in *. inversion x. apply X0.
Qed.

Definition headApply (alpha : omega_presheaf_nt lengthN_pshf lengthN_pshf) : A -> A :=
  fun a => let l1 : fam lengthN_pshf 1 := Snoc_lengthN Empty_lengthN a in
           let l2 : fam lengthN_pshf 1 := component _ _ alpha 1 l1 in
           len1Proj l2.

CoFixpoint fromNT (alpha : omega_presheaf_nt lengthN_pshf lengthN_pshf) : autom :=
  Step (fun a => (headApply alpha a, fromNT (unshiftlengthNNT (shiftNT alpha)))).

Check lengthN_rec.

Fixpoint stepN {n} (m : autom) (l : lengthN n) : autom * lengthN n :=
    match l with
    | Empty_lengthN => (m,Empty_lengthN)
    | Snoc_lengthN l' x => let (m',l'') := stepN m l' in
                              let (y,m'') := step m x in
                              (m'',Snoc_lengthN l'' y)
    end.

Definition execN {n} (m : autom) (l : lengthN n) := snd (stepN m l).

Theorem exec_S : forall n m (l : lengthN n) x, exists l' y, (execN m (Snoc_lengthN l x) = Snoc_lengthN l' y) /\ (l' = execN m l).
Proof.
Admitted.

Theorem toNT_squares (m : autom) :
  forall n : nat,
   compose (execN m) (restrict lengthN_pshf n) =
   compose (restrict lengthN_pshf n) (execN m).
Proof.
intros.
induction n.
- simpl. extensionality l. unfold compose. rewrite trunc_0. simpl. rewrite trunc_0. reflexivity.
- extensionality l. simpl in *. unfold compose in *.
  assert (exists x , l = Snoc_lengthN (truncate l) x) by (apply lengthN_eta_S).
  destruct H.
  rewrite -> H.
  cbn.
  assert (exists l' y, (execN m (Snoc_lengthN (truncate l) x) = Snoc_lengthN l' y) /\ (l' = execN m (truncate l))) by (apply exec_S).
  destruct H0 as [l' [y [HSnoc Hl']]].
  rewrite -> HSnoc.
  rewrite -> Hl'.
  cbn.
  reflexivity.
Qed.

Definition toNT (m : autom) : omega_presheaf_nt lengthN_pshf lengthN_pshf :=
    mkNT lengthN_pshf lengthN_pshf (fun n => execN m) (toNT_squares m).

(*
* - Clear conception of who the audience is –– why do they care about this equivalence?
* - Rewrite the prof in places where it's not easy to follow: naming, tactics, etc. Make it maximally understandable.
* - Critical pass w/ alectryon for state management.
* - Potentailly, an appenndix with thoughts on the process of turning the proof into a literate one.
* - Ensure you have a trial reader!
*)