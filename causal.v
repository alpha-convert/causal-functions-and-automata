Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
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

Our goal in this document is to characterize the stream functions :math:`f : 2^\omega \to 2^\omega` which
can be implemented as stream processing machines which are both (a) "productive", in the sense that they always
emit an output for each input, and (b) are "truthful" in the sense that they never have to go back on their word.

|*)

(*|
To begin, let's define a coinductive [#]_. type of streams, with elements drawn from a type `A`.
|*)

Variable A : Type.

CoInductive stream : Type :=
| SCons : A -> stream -> stream.

(*|

More or less by definition, the functions `stream -> stream` which can be written in Coq
are computable. Unfortunately, we must work a bit harder to get the other properties.

Intuitively, both the truthfulness and productivity properties are facts about *prefixes* of streams.
Truthfulness says that passing a larger prefix yields only a larger output, while productivity says
precisely by how much the output should grow. Of course, while this makes intuitive sense, it's not
immediately clear how to define these properties formally. After all, stream functions `f : stream -> streamm`
are defined on *entire* streams, not prefixes!

The insight required to guide us past this quandry is that truthful, productive functions on prefixes of streams
should naturally "lift" to functions on whole streams.

|*)

Inductive vec : nat -> Type :=
| Empty : vec 0
| Snoc {n} : vec n -> A -> vec (S n).

(*|
Above is a definition of length-indexed vectors, represented as snoc-lists.
These will represent prefixes of streams.


The most important (for our purposes) operation on vectors is truncation: deleting the
last element. Because we've implemented vectors as length-indexed snoc lists,
truncate is trivial to implment, as shown below.
|*)

Definition truncate {n : nat} (l : vec (S n)) : vec n := 
  match l in vec (S n) return vec n with
  | Snoc l _ => l
  end.

(*|
Truncation is particularly interesting because it lets us reframe streams in terms of their prefixes.
A stream can be thought of as a family of vectors `vs : forall n, vec n`, one of each length,
such that the :math:`n+1`st is just the :math:`n`th with one element tacked on to the end.
Swapping the perspective around, this is to say that that `vs n = truncate (vs (n + 1))`.
Intuitively, this view of streams is consistent with their view as coinductively defined objects:
they are lists that we may unfold them to any finite depth.

Viewing streams this way leads us to our first definition of productive & truthful functions on streams.
|*)


Record causal : Type := mkCausal {
  f : forall n, vec n -> vec n;
  caused : forall n l, f n (truncate l) = truncate (f (S n) l)
}.

(*|

|*)

Definition causalApply1 (c : causal) (x : A) : A.
Admitted.

(* remove the first element *)
Fixpoint tail {n : nat} (l : vec (S n)) : vec n.
Admitted.

Fixpoint cons {n : nat} (x : A) (l : vec n) : vec (S n).
Admitted.

Theorem cons_snoc : forall n (l : vec n) x y, cons x (Snoc l y) = Snoc (cons x l) y.  
Proof. 
intros n l.
dependent induction l.
Admitted.

Theorem truncate_cons : forall n (l : vec (S n)) x, truncate (cons x l) = cons x (truncate l).
Proof.
  intros n l.
  dependent induction l.
  - intros. rewrite cons_snoc. cbn. reflexivity.
Qed.

Theorem truncate_tail : forall n (l : vec (S (S n))) , truncate (tail l) = tail (truncate l).
Admitted.

Definition consMap (x : A) (f : forall n, vec n -> vec n) : forall n, vec n -> vec n :=
  fun n => fun xs => tail (f (S n) (cons x xs)).

Theorem cons_caused  : forall x c n l,
consMap x (f c) n (truncate l) =
truncate (consMap x (f c) (S n) l).
Proof.
  intros.
  destruct c as [f pf].
  unfold consMap.
  cbn.
  rewrite <- truncate_cons.
  rewrite pf.
  rewrite truncate_tail.
  reflexivity.
Qed.

Definition consCausal (x : A) (c : causal) : causal := mkCausal (consMap x (f c)) (cons_caused x c).

(*|
**Picture here!!**

Causal maps interpret as streams.
|*)


CoFixpoint interpCausal (c : causal) (s : stream) : stream :=
  match s with
  | SCons x s' => let y := causalApply1 c x in
                  SCons y (interpCausal (consCausal x c) s')
  end.



(*|There's also automata!|*)

CoInductive transd : Type := 
| Step : (A -> A * transd) -> transd.

Definition step (t : transd) (x : A) : A * transd :=
    match t with
    | Step f => f x
    end.

(*|These also interpret as stream maps|*)

CoFixpoint interpTransd (t : transd) (s : stream) : stream :=
  match s with
  | SCons x s' => let (y,t') := step t x in
                  SCons y (interpTransd t' s')
  end.

(*| and as vector maps |*)

Fixpoint stepN {n} (t : transd) (l : vec n) : transd * vec n :=
    match l with
    | Empty => (t,Empty)
    | Snoc l' x => let (t',l'') := stepN t l' in
                              let (y,t'') := step t' x in
                              (t'',Snoc l'' y)
    end.

Definition execN (t : transd) : forall n, vec n -> vec n := fun n l => snd (stepN t l).

(*| and these vector maps are causal! We can take an automata, and turn its execN into a causal map|*)

Theorem execN_snoc : forall t n l x, execN t (S n) (Snoc l x) = Snoc (execN t n l) (let (t',_) := stepN t l in fst (step t' x)).
Proof.
  intros.
  unfold execN.
  cbn.
  destruct (stepN t l).
  destruct (step t0 x).
  cbn.
  reflexivity.
Qed.


Theorem execN_caused (t : transd) :
forall (n : nat) (l : vec (S n)),
  execN t n (truncate l) = truncate (execN t (S n) l).
Proof.
  intros.
  dependent induction l.
  cbn.
  rewrite execN_snoc.
  cbn.
  reflexivity.
Qed.

Definition transdToCausal (t : transd) : causal := mkCausal (execN t) (execN_caused t).

(*| We can also go backwards! Causal maps define automata. |*)

CoFixpoint causalToTransd (c : causal) : transd :=
  Step (fun x => let y := causalApply1 c x in (y, causalToTransd (consCausal x c))).

(*|This begs the roundtrip questions.|*)

Theorem vec_eta_0 : forall (l : vec 0), l = Empty.
Proof.
  intros.
  dependent destruction l.
  reflexivity.
Qed.

Theorem vec_eta_S : forall n, forall (l : vec (S n)), exists x , l = Snoc (truncate l) x.
Proof.
  intros.
  dependent destruction l.
  exists a.
  auto.
Qed.

Theorem causalAndBack : forall c n l, f (transdToCausal (causalToTransd c)) n l = f c n l.
Proof.
  intros.
  dependent induction l.
  - cbn. unfold execN. rewrite vec_eta_0. reflexivity.
  - cbn. rewrite execN_snoc.
    unfold execN.
Qed.



(*Record omega_presheaf : Type := mkPresheaf {
  fam : nat -> Type;
  restrict : forall n, fam (S n) -> fam n
}.
*)




(**
Theorem trunc_0 : forall (l : vec 1), truncate l = Empty.
Proof.
Admitted.



Definition vec_pshf : omega_presheaf := mkPresheaf vec (fun _ => truncate).

Record omega_presheaf_nt (P : omega_presheaf) (Q : omega_presheaf) : Type := mkNT {
  component : forall n, fam P n -> fam Q n;
  squares : forall n, compose (component n) (restrict P n) = compose (restrict Q n) (component (S n))
}.
*)

(* Is this the same as later???*)
(*
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


Definition unshiftvecNT_component (alpha : omega_presheaf_nt (shift vec_pshf) (shift vec_pshf)) : forall n : nat, fam vec_pshf n -> fam vec_pshf n :=
    fun n => match n with
             | 0 => fun _ => Empty
             | S n' => component (shift vec_pshf) (shift vec_pshf) alpha n'
    end.

Theorem unshiftvecNT_squares (alpha : omega_presheaf_nt (shift vec_pshf) (shift vec_pshf)) : forall n : nat,
compose
  (unshiftvecNT_component alpha n)
  (restrict vec_pshf n) =
compose (restrict vec_pshf n)
  (unshiftvecNT_component alpha (S n)).
Proof.
simpl. induction n.
 - extensionality l. cbn. unfold compose. rewrite trunc_0. reflexivity.
 - simpl in *. apply (squares (shift vec_pshf) (shift vec_pshf) alpha).
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
   But this happens to be a vec_pshf anyway.
*)
Definition unshiftvecNT (alpha : omega_presheaf_nt (shift vec_pshf) (shift vec_pshf)) : omega_presheaf_nt vec_pshf vec_pshf :=
    mkNT vec_pshf vec_pshf (unshiftvecNT_component alpha) (unshiftvecNT_squares alpha).

Definition len1Proj (x : fam vec_pshf 1) : A.
Proof.
simpl in *. inversion x. apply X0.
Qed.

Definition headApply (alpha : omega_presheaf_nt vec_pshf vec_pshf) : A -> A :=
  fun a => let l1 : fam vec_pshf 1 := Snoc Empty a in
           let l2 : fam vec_pshf 1 := component _ _ alpha 1 l1 in
           len1Proj l2.

CoFixpoint fromNT (alpha : omega_presheaf_nt vec_pshf vec_pshf) : transd :=
  Step (fun a => (headApply alpha a, fromNT (unshiftvecNT (shiftNT alpha)))).

Check vec_rec.



Theorem exec_S {n} : forall m (l : vec n) x, exists y, (execN m (Snoc l x) = Snoc (execN m l) y /\ (y = let (m',l') := stepN m l in fst (step m' x))).
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
   compose (execN m) (restrict vec_pshf n) =
   compose (restrict vec_pshf n) (execN m).
Proof.
intros.
induction n.
- simpl. extensionality l. unfold compose. rewrite trunc_0. simpl. rewrite trunc_0. reflexivity.
- extensionality l. simpl in *. unfold compose in *.
  assert (exists x , l = Snoc (truncate l) x) by (apply vec_eta_S).
  destruct H.
  rewrite -> H.
  cbn.
  assert (exists y, (execN m (Snoc (truncate l) x) = Snoc (execN m (truncate l)) y) /\ _) by (apply exec_S).
  destruct H0 as [y [HSnoc _]].
  rewrite -> HSnoc.
  cbn.
  reflexivity.
Qed.

Definition toNT (m : transd) : omega_presheaf_nt vec_pshf vec_pshf :=
    mkNT vec_pshf vec_pshf (fun n => execN m) (toNT_squares m).

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

*)

(*|
.. [#] For the curious: by endowing :math:`2` with the discrete topology and :math:`2^\omega` with the product topology,
the computable functions :math:`2^\omega \to 2^\omega` are continuous.

.. [#] We will not be discussing coinduction or cofixpoints in this document, but the unfamiliar reader can safely ignore
this detail, and treat the coinductive definitions as just special syntax for defining datatypes that have infinite
values.
|*)