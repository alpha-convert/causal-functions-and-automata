Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.

(*|
================================
Transducers are Causal Functions
================================

|*)


(*|
Consider the set :math:`2^\omega` of infinite lists of natural numbers.

What are the "nice" functions :math:`2^\omega \to 2^\omega`? 
As indicated by the quotes, the answer to this question is highly dependent on your aesthetic preferences.
Naturally, different people with different needs have proposed different answers based on a wide variety of values of "nice".

One potential value of "nice" is the vacuous one: all (mathematically definable) functions :math:`2^\omega \to 2^\omega` are allowed!
Among these are functions that aren't even definable as functions in your favorite programming language,
such as the function :math:`f : 2^\omega \to 2^\omega` defined by :math:`f(1^\omega) = 0^\omega` and  :math:`f(s) = s`: the function
which is the identity everywhere, except for on the stream of all ones, where it's the stream of all zeroes.
This function is clearly not computable in any sense: in order to determine even the first element of the output stream,
all infinitely-many elements of the input need to be inspected.

Restricting "nice" to mean "computable" restricts the class significantly. Indeed, the main result is 
the rule out functions like the one above. A classic result in computability theory is that the computable
functions :math:`f : 2^\omega \to 2^\omega` are *continous* in a particular sense [#]_ which means that any finite prefix
of the output of :math:`f` can only depend on a finite prefix of its input.

However, the computable functions can include some unwanted behavior. Of particular interest for the purposes of this
piece is functions that "go back on their word".
A simple example of this is the function defined by the equations :math:`f(00s) = 01s`, :math:`f(01s) = 10s`, :math:`f(1s) = 1s`.
To see why this might be undesierable, consider a situation where the input list to the function is being *streamed in*, bit by bit, from
some outside source. Similarly, suppose the output is being produced bit by bit, and is fed to some similar transformation down the line.
Unfortunately, the function :math:`f` cannot be implemented in this manner: if the first bit of input is a :math:`0`,
the implementation must wait until the *second* bit arrives to emit the first bit of output. To faithfully implement this
in such a "stream transformer" machine model, the machine would need the ability to either (a) block until the second bit arrives, or
(b) emit a dummy value for the first output and then "retract" it once it got the second bit of input.

Our goal in this **???* is to characterize the stream functions :math:`f : 2^\omega \to 2^\omega` which
can be implemented as stream processing machines which are both (a) productive, in the sense that they always
emit an output for each input, and (b) are *causal* in the sense that they


|*)

Variable A : Type.

Coinductive stream : Type :=
| SCons : A -> stream -> stream.

(*|

==========
Transducer
==========

|*)


CoInductive transd : Type := 
| Step : (A -> A * transd) -> transd.

Definition step (m : transd) (x : A) : A * transd :=
    match m with
    | Step f => f x
    end.


Inductive listn : nat -> Type :=
| Empty : listn 0
| Snoc {n} : listn n -> A -> listn (S n).

Fixpoint stepN {n} (m : transd) (l : listn n) : transd * listn n :=
    match l with
    | Empty => (m,Empty)
    | Snoc l' x => let (m',l'') := stepN m l' in
                              let (y,m'') := step m' x in
                              (m'',Snoc l'' y)
    end.

Definition execN {n} (m : transd) (l : listn n) := snd (stepN m l).

Definition exec (m : transd) (x : A) : A :=
    fst (step m x).

Record omega_presheaf : Type := mkPresheaf {
  fam : nat -> Type;
  restrict : forall n, fam (S n) -> fam n
}.


(* remove the first element *)
Definition truncate {n : nat} (l : listn (S n)) : listn n := 
  match l in listn (S n) return listn n with
  | Snoc l _ => l
  end.


Theorem trunc_0 : forall (l : listn 1), truncate l = Empty.
Proof.
Admitted.

Theorem listn_eta_0 : forall (l : listn 0), l = Empty.
Proof.
Admitted.

Theorem listn_eta_S : forall n, forall (l : listn (S n)), exists x , l = Snoc (truncate l) x.
Proof.
Admitted.

Definition listn_pshf : omega_presheaf := mkPresheaf listn (fun _ => truncate).

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


Definition unshiftlistnNT_component (alpha : omega_presheaf_nt (shift listn_pshf) (shift listn_pshf)) : forall n : nat, fam listn_pshf n -> fam listn_pshf n :=
    fun n => match n with
             | 0 => fun _ => Empty
             | S n' => component (shift listn_pshf) (shift listn_pshf) alpha n'
    end.

Theorem unshiftlistnNT_squares (alpha : omega_presheaf_nt (shift listn_pshf) (shift listn_pshf)) : forall n : nat,
compose
  (unshiftlistnNT_component alpha n)
  (restrict listn_pshf n) =
compose (restrict listn_pshf n)
  (unshiftlistnNT_component alpha (S n)).
Proof.
simpl. induction n.
 - extensionality l. cbn. unfold compose. rewrite trunc_0. reflexivity.
 - simpl in *. apply (squares (shift listn_pshf) (shift listn_pshf) alpha).
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
   But this happens to be a listn_pshf anyway.
*)
Definition unshiftlistnNT (alpha : omega_presheaf_nt (shift listn_pshf) (shift listn_pshf)) : omega_presheaf_nt listn_pshf listn_pshf :=
    mkNT listn_pshf listn_pshf (unshiftlistnNT_component alpha) (unshiftlistnNT_squares alpha).

Definition len1Proj (x : fam listn_pshf 1) : A.
Proof.
simpl in *. inversion x. apply X0.
Qed.

Definition headApply (alpha : omega_presheaf_nt listn_pshf listn_pshf) : A -> A :=
  fun a => let l1 : fam listn_pshf 1 := Snoc Empty a in
           let l2 : fam listn_pshf 1 := component _ _ alpha 1 l1 in
           len1Proj l2.

CoFixpoint fromNT (alpha : omega_presheaf_nt listn_pshf listn_pshf) : transd :=
  Step (fun a => (headApply alpha a, fromNT (unshiftlistnNT (shiftNT alpha)))).

Check listn_rec.



Theorem exec_S {n} : forall m (l : listn n) x, exists y, (execN m (Snoc l x) = Snoc (execN m l) y /\ (y = let (m',l') := stepN m l in fst (step m' x))).
Proof.
  intros.
  exists (let (m',_) := stepN m l in fst (step m' x)).
  unfold execN.
  cbn.
  destruct (stepN m l) as [m' l'].
  destruct (step m' x) as [y m''].
  cbn.
  auto.
Qed.

Theorem toNT_squares (m : transd) :
  forall n : nat,
   compose (execN m) (restrict listn_pshf n) =
   compose (restrict listn_pshf n) (execN m).
Proof.
intros.
induction n.
- simpl. extensionality l. unfold compose. rewrite trunc_0. simpl. rewrite trunc_0. reflexivity.
- extensionality l. simpl in *. unfold compose in *.
  assert (exists x , l = Snoc (truncate l) x) by (apply listn_eta_S).
  destruct H.
  rewrite -> H.
  cbn.
  assert (exists y, (execN m (Snoc (truncate l) x) = Snoc (execN m (truncate l)) y) /\ _) by (apply exec_S).
  destruct H0 as [y [HSnoc _]].
  rewrite -> HSnoc.
  cbn.
  reflexivity.
Qed.

Definition toNT (m : transd) : omega_presheaf_nt listn_pshf listn_pshf :=
    mkNT listn_pshf listn_pshf (fun n => execN m) (toNT_squares m).

(*
* - Clear conception of who the audience is –– why do they care about this equivalence?
* - Rewrite the prof in places where it's not easy to follow: naming, tactics, etc. Make it maximally understandable.
* - Critical pass w/ alectryon for state management.
* - Potentailly, an appenndix with thoughts on the process of turning the proof into a literate one.
* - Ensure you have a trial reader!
*)

Theorem inv1 : forall alpha n, component _ _ (toNT (fromNT alpha)) n = component _ _ alpha n.
Proof.
  intros.
  cbn.
  extensionality l.
Admitted.

(*|
.. [#] For the curious: by endowing :math:`2` with the discrete topology and :math:`2^\omega` with the product topology,
the computable functions :math:`2^\omega \to 2^\omega` are continuous.
|*)