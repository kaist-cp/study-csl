---
title: An Overview of Concurrent Separation Logic and Iris
author: Jaehwang Jung
institute: KAIST CP
date: "2019-12-31, 2020-01-07, 2020-01-14, 2020-01-21"
theme: metropolis
toc: true
slide_level: 2
header-includes:
- \metroset{progressbar=frametitle,sectionpage=progressbar}
- \usepackage{stuff}
urlcolor: blue
linkcolor: black
highlight-style: kate
---

# Introduction

## Introduction
* Concurrent Separation Logic(CSL): a tool for formal verification of correctness of concurrent programs
* Iris: SOTA CSL _framework_. You can
    * instantiate Iris with your own programming language, and
    * encode various reasoning mechanisms from other CSLs.
    * Caveat: the property is valid only when the program terminates (partial correctness)

What's your goal?

## Resources
* Iris
    * [**tutorial-POPL18**](https://gitlab.mpi-sws.org/iris/tutorial-popl18)
    * [**Lecture Notes**](https://iris-project.org/tutorial-material.html)
    * [Iris examples](https://gitlab.mpi-sws.org/iris/examples)
    * [Iris from the ground up (theories)](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf)
    * [documentations](https://gitlab.mpi-sws.org/iris/iris/tree/master/docs):
      Iris Proof Mode, Heap lang, editor setups, ...

## Supplementary Resources
* Hoare logic
    * [2017fall CS492 Program Analysis](https://plrg.kaist.ac.kr/doku.php?id=home:lectures:cs492_2017_2)
        - basic: section 5 of "Proof Methods"
        - weakest preconditions: "Predicate Transformers"
* Separation logic
    * [CACM 2019-2](https://cacm.acm.org/magazines/2019/2/234356-separation-logic/pdf)
* [Formal Reasoning About Programs](https://frap.csail.mit.edu/main)

# Basics of (Sequential) Separation Logic

## Hoare Logic
A logic for proving program specifications (a.k.a. Hoare triples) of form
$$
\hoare{\text{precondition}}{\texttt{code}}{\text{postcondition}}
$$

* Run the code in a state satisfying the precondition.
    * It runs safely (\eg doesn't get stuck).
    * If it terminates, the resulting state satisfies the postcondition.
$$
\hoare{x=0,y=1}{\texttt{x := x + 1; y := x + y}}{x=1,y=2}
$$
How to prove the specification systematically?

## Hoare Logic Inference Rules
Hoare logic inference rules for each programming language construct:
$$
\infer [HOARE-SEQ] {
    \hoare{P_0}{\texttt{b0}}{P_1}\\
    \hoare{P_1}{\texttt{b1}}{P_2}
} {
    \hoare{P_0}{\texttt{b0; b1}}{P_2}
}
$$
$$
\infer [HOARE-IF] {
    \hoare{P\land e}{\texttt{b0}}{Q}\\
    \hoare{P\land \neg e}{\texttt{b1}}{Q}
} {
    \hoare{P}{\texttt{if (e) b0 else b1}}{Q}
}
$$
Note: inference rules themselves should be proved sound \wrt the semantics of the language.

## Separation Logic
Problem: Hoare logic doesn't work well for _large_ programs involving _pointers_ (shared mutable states $\to$ lots of interference to consider).

Solution: Separation Logic introduces the concept of the **"exclusive ownership of resources"** to enable enables the modular & scalable verification of pointer-manipulating programs.

Intuitive understanding of a separation logic proposition:

* it asserts the ownership of resources.
* it describes resources.

Resource? \eg heap memory $Loc\xrightarrow{\text{fin}}Val$.

## "Points-to" $l\mapsto v$
* Ownership of a heap fragment (heaplet) at location $l$ with value $v$
    * The owner can modify what $l$ points to
    * without invalidating invariants of other parts/threads of the program.
* $\hoare{l\mapsto 5}{l\leftarrow !l+1}{v,v=()\land l\mapsto 6}$
* $\hoare{True}{ref(123)}{v,\exists l.v=l\land l\mapsto 123}$

## Separating conjunction $P\ast Q$
* A resource that can be **separated** into 2 resources $P$ and $Q$
$$\hoare{l_1\mapsto v_1\ast l_2\mapsto v_2}{\texttt{swap}\,l_1\,l_2}{v,v=()\land l_1\mapsto v_2\ast l_2\mapsto v_1}$$
* _frame rule_: irrelevant resources remain the same
$$\infer{\hoare{P}{e}{v,Q}}{\hoare{P\ast R}{e}{v,Q\ast R}}$$
\begin{gather*}
\{l_1\mapsto v_1\ast l_2\mapsto v_2\ast l_3\mapsto v_3\}\\
\texttt{swap}\,l_1\,l_2 \\
\{v,v=()\land l_1\mapsto v_2\ast l_2\mapsto v_1\ast l_3\mapsto v_3\}
\end{gather*}
* $P$ and $Q$ are disjoint:
    * $l\mapsto v_1 \ast l\mapsto v_2 \proves False$
* vs. $P\land Q$: resource satisfying both $P$ and $Q$
    * $l\mapsto v_1 \land l\mapsto v_2 \proves v_1 = v_2$ (agreement)

## Magic wand $P\wand Q$
* Resources that satisfies $Q$ when extended with resources satisfying $P$ ($Q$ minus $P$)
    * $x\mapsto u \wand (x\mapsto u\ast y\mapsto v)$ is like $y\mapsto v$
    * $\exists v. (x\mapsto v) \ast (x\mapsto 3 \wand Q)$:
      $x$ is allocated, if you mutate its contents to 3 then you get a resource that satisfies $Q$
* vs. $P\Rightarrow Q$: satisfies $Q$ if the same resource additionally satisfies $P$

## Laws of (affine) separation logic
\begin{gather*}
\TRUE * P \provesIff P\qquad
P * Q \proves Q * P \qquad
(P * Q) * R \proves P * (Q * R)\\
P\ast Q\proves P\\
\infer[$*$-mono]
  {P_1 \proves Q_1 \\ P_2 \proves Q_2}
  {P_1 * P_2 \proves Q_1 * Q_2} \qquad
\infer[$\wand$I]
  {R\ast P \proves Q}
  {R \proves P \wand Q}\qquad
\infer[$\wand$E]
  {R_1 \proves P\wand Q \\ R_2\proves P}
  {R_1\ast R_2 \proves Q}
\end{gather*}

Note

* $P\ast Q\proves P\land Q$
* $P\land Q\proves P\ast Q$ if $P$ _persistent_

# Separation Logic of Iris

## Demo 1: POPL18 tutorial `exercises/ex_01_swap.v`
<https://gitlab.mpi-sws.org/iris/tutorial-popl18>

## Encoding of Hoare triples (a.k.a. [Texan triples](https://gitlab.mpi-sws.org/iris/iris/merge_requests/9#nomenclature))
$$
\hoare{P}{e}{v,Q}\triangleq \always(P\wand \wpre{e}{v,Q})
$$

* $\wpre{e}{v,Q}$?: the weakest(most general) precondition of program $e$ and postcondition $Q$
    * why? systematic proof process. (`wp_*` tactics)
    * Start with the postcondition, go backwards, and try to get to something the precondition implies
    * $\wpre{x\leftarrow 3}{Q}= \exists v. (x\mapsto v) \ast (x\mapsto 3 \wand Q)$

## Weakest preconditions
$$
\infer[WP-STORE]{}{
    l\mapsto v\ast\later(l\mapsto w\wand\Phi())\proves \wpre{l\leftarrow w}{\Phi}
}
$$
$$
\infer[WP-ALLOC]{}{
    \later(\forall l. l\mapsto v \wand\Phi())\proves \wpre{\texttt{ref}(v)}{\Phi}
}
$$
$$
\infer[WP-$\lambda$]{}{
    \later\wpre{e[v/x]}{\Phi} \proves
    \wpre{(\lambda x.e) v}{\Phi}
}
$$
$$
\infer[wp-mono] {
    \forall v. P(v) \proves Q(v) \\
} {
    \wpre\expr{\Ret\var.P} \proves
    \wpre\expr{\Ret\var.Q}}
$$

## Encoding of Hoare triples (cont.)
Another equivalence (continuation)
\begin{align*}
\hoare{P}{e}{v,Q}&\triangleq \always(P\wand \wpre{e}{v,Q})\\&\cong
\always(\forall\Phi, P\wand (Q\wand \Phi\,v) \wand \wpre{e}{v,\Phi\, v})
\end{align*}

* why? convenience of application of the spec to other proofs

## `wp_bind`
* evaluation context: $(1+2)+4 \to (\Box + 4)[1+2]\to (\Box + 4)[3]\to 3+4 \to 7$

$$
\infer[HT-BIND]{
    \hoare{P}{e}{v,Q}\\ \forall v.\hoare{Q}{E[v]}{w.R}
} {
    \hoare{P}{E[e]}{w.R}
}
$$
$$
\infer[WP-BIND]{}{\wpre{e}{v, \wpre{E[v]}{\Phi}} \proves \wpre{E[e]}{\Phi}}
$$

## Modalities: "later" $\later$
* $\later P$ holds if $P$ holds after a reduction step
* why? logical soundness (details in "group up" paper)
* introduction
    * weaken: $P\proves \later P$, `iNext` tactic
    * opening invariants
* elimination
    * step
        * strengthened Hoare triples (lecture note 5.1), `wp_*` tactics
          $$\hoare{\later l\mapsto u}{!l}{v, v=u\land l\mapsto u}$$
        * HT-FRAME-ATOMIC
    * timeless (propositions that doesn't refer to other invariants, most of innocent propositions): FUP-TIMELESS, `> ipat` intro pattern

## Löb induction
$$
\infer[Lőb]{Q\land\later P\proves P}{Q\proves P}
$$
\todo

## Modalities: "persistently", "always" $\always$
* non-exclusive, shareable (duplicable) "knowledge"
* equality, Hoare triples, **invariants**, induction hypothesis, ...
$$
\infer{P\proves\always P\ (P\text{ is persistent})}{P\proves P\ast P}\quad
\inferB [HT-ALWAYS]
    { \always Q\land S \proves \hoare{P}{e}{v,R} }
    { S \proves \hoare{\always Q\land P}{e}{v,R} }
$$
$$
\hoare{P}{e}{v,Q}\triangleq \always(P\wand \wpre{e}{v,Q})
$$
Using the $\always$ modality guarantees that all the non-persistent (exclusive)
resources required by $e$ are contained in $P$.

\todo

# Concurrent Separation Logic: \ Invariants

## Invariant $\knowInv{\iota}{P}$
See [lecture 9 (invariants) slides](https://iris-project.org/tutorial-pdfs/lecture9-invariants.pdf)

### Summary
* Shareable knowledge that there exists a resource satisfying $P$ (think: pointer)
* To establish $\knowInv{\iota}{P}$, sacrifice $P$.
* Use with care!
    * Each thread can temporarily (for a single atomic step) own $P$.
    * The user should return $P$ to the $\knowInv{\iota}{P}$.
    * The user cannot access the same invariant at the same time (thus the name $\iota$ and mask $\mask$ are needed).

# Invariants in Iris

## Demo 2: coin flip
<!-- <https://gitlab.mpi-sws.org/iris/examples/blob/master/theories/lecture_notes/coq_intro_example_1.v> -->
<https://gitlab.mpi-sws.org/iris/tutorial-popl18/blob/master/talks/demo/part3.v>

## Invariant namespace $\namesp$
* similar to the concept of namespace in programming
\begin{align*}
\namesp &= \texttt{org.iris.lock}\\
\namecl\namesp &= \texttt{org.iris.lock.*}
\end{align*}
* used for controlling set of invariants names easily
$$
\knowInv{\namesp}{P}\triangleq \exists \iota\in \namecl\namesp. \knowInv{\iota}{P}
$$

\begin{tiny}
(Details in Lecture Note 11.5)
\end{tiny}

## Invariant rules with $\namesp$
$$
\infer[HT-INV-ALLOC] {
    \mask \textsf{ infinite} \\
    \knowInv{\namesp}{I}\proves
    \hoare{P}{e}{v,Q}[\mask]
} {
    \hoare{\later I\ast P}{e}{v,Q}[\mask]
}
$$
$$
\infer[HT-INV-ACESS] {
    e \textsf{ atomic} \\
    \namesp\subset\mask\\
    \hoare{\later I\ast P}{e}{v,\later I\ast Q}[\mask\setminus\namesp]
} {
    \knowInv{\namesp}{I}\proves
    \hoare{P}{e}{v,Q}[\mask]
}
$$

## Invariants + weakest preconditions
$$
\infer{
    e \textsf{ atomic} \\
    \namesp\subset\mask\\
    \hoare{\later I\ast P}{e}{v,\later I\ast Q}[\mask\setminus\namesp]
} {
    \knowInv{\namesp}{I}\proves
    \hoare{P}{e}{v,Q}[\mask]
}
$$
$$
\infer[WP-INV] {
    e \textsf{ atomic} \\
    \namesp\subset\mask\\
    \later I\proves \wpre{e}[\mask\setminus\namesp]{v,\later I\ast Q}
} {
    \knowInv{\namesp}{I}\proves \wpre{e}[\mask]{v,Q}
}
$$

* INV-ALLOC?: Soon
<!-- WP-FRAME-STEP (lecture note 113, not necessarily atomic, but at least reducible) -->

##
\begin{tiny} Group-up page 61 \end{tiny}
![](res/wp-inv.png)

3rd floor (the one right on top of INV-ACCESS) of the proof tree is what we actually prove in Iris Prove mode with `iInv` tactic.


## Fancy update modality $\pvs[\mask_1][\mask_2]$
$\pvs[\mask_1][\mask_2]$ contains resources which,
together with resources in invariants names $\mask_1$,
can be updated (via _frame preserving update_) to resources which can be split into
resources satisfying $P$ and resources in invariants named $\mask_2$.

The meaning of "updating" will be discussed more in the next part (_ghost states_).
For now, we focus on the difference of the masks $\mask_1$ and $\mask_2$.

$$
\infer[fup-intro-mask]
{\mask_2 \subseteq \mask_1}
{P \proves \pvs[\mask_1][\mask_2]\pvs[\mask_2][\mask_1] P}\qquad
\infer[fup-trans] {}
{\pvs[\mask_1][\mask_2] \pvs[\mask_2][\mask_3] P \proves \pvs[\mask_1][\mask_3] P}
$$
$$
\infer[fup-intro] {}
{P\proves \pvs[\mask]P}
$$

##
$$
\infer[inv-alloc]{}{\later P \proves \pvs[\mask] \knowInv{\namesp}{P}}
$$
$$
\infer[inv-access(open\&close)] {\namesp \subseteq \mask} {
    \knowInv{\namesp}{P} \proves
    \pvs[\mask][\mask\setminus\namesp] (
        \later P \ast (\later P \wand \pvs[\mask\setminus\namesp][\mask] \TRUE)
    )
}
$$
$\pvs[\mask\setminus\namesp][\mask] \TRUE$: resources which can be combined
with resources in invariants in $\mask\setminus\namesp$ to get resources in
invariants in $\mask$, \ie it contains the resources in the invariants in
$\namesp$.
$$
\infer[fup-timeless] {\timeless P}
{\later P \proves \pvs[\mask]  P}
$$

<!-- * FUP-FRAME: 2 simpler parts -->

<!-- ground up figure 15 -->

## Fancy view shift $\vs[\mask_1][\mask_2]$
$$
P\vs[\mask_1][\mask_2]Q\triangleq \always(P\wand\pvs[\mask_1][\mask_2]Q),\quad
P\vsW[\mask_1][\mask_2]Q\triangleq P\wand\pvs[\mask_1][\mask_2]Q
$$
Just a matter of presentation.
$$
\infer[INV-ALLOC]{}{P\vs[\mask]\knowInv{\namesp}{P}}\qquad
\infer[HOARE-VS] {
    P\vs[\mask]P'\\
    \hoare{P'}{e}{v,Q'}[\mask]\\
    Q\vs[\mask]Q'\\
} {
    \hoare{P}{e}{v,Q}[\mask]
}\qquad
$$
$$
\infer[fvs-timeless] {\timeless P}
{\later P \vs[\mask]  P}
$$

<!--
$$
\infer[HT-FRAME-STEP] {
    e\notin\Val\\
    \mask_2\subset\mask_1\\
    R_1\vs[\mask_1][\mask_2]\later R_2\\
    \hoare{P}{e}{v,Q}[\mask_2]\\
    R_2\vs[\mask_2][\mask_1] R_3
} {
    \hoare{P\ast R_1}{e}{v,Q\ast R_3}[\mask_1]
}\qquad
$$
proof? why is this necessary and how is it difference from timeless stuff??  -->

<!--
* ground up figure 4
* how to connect the result of timeless stuff to proof?
* vs elimination: wp-vup and wp-atomic
-->


# Concurrent Separation Logic: \ Ghost States

## `mk_oneshot`

\footnotesize
```ocaml
(* Example from "Iris from the ground up" section 2 *)
let mk_oneshot () = let x = ref(None) in
(* CAS(loc, cur, new): atomically Compare `!loc` and `cur`
   And Set it to `new` if they are the same *)
    { try_set = fun n -> CAS(x, None, Some(n)),
      check = fun () ->
        let y = !x in
        fun () ->
            match y, !x with
            | None, _ => ()
            | Some(n), None => assert(false)
            | Some(n), Some(m) => assert(n == m)
            end }
```

* Allocates a location that can be set only once by `c.try_set`.
* `c.check()` takes a snapshot of the value and `c.check()()` crashes if the current value differs from the snapshot.

\normalsize

## `mk_oneshot`

\footnotesize

```ocaml
let mk_oneshot () = let x = ref(None) in
    { try_set = fun n -> CAS(x, None, Some(n)),
      check = fun () ->
        let y = !x in
        fun () ->
            match y, !x with
            | None, _ => ()
            | Some(n), None => assert(false)
            | Some(n), Some(m) => assert(n == m)
            end
    }
```

Prove that `c.check()()` does not crash.
$$
\{\TRUE\}\ \texttt{mk\_oneshot()} \left\{ c, \forall v.
    \begin{array}{l}
    \hoare{\TRUE}{\texttt{c.tryset(v)}}{w, w\in \{\texttt{true},\texttt{false}\}} \ast\\
    \hoare{\TRUE}{\texttt{c.check()}}{f, \hoare{\TRUE}{\texttt{f()}}{\TRUE}}\\
    \end{array}
\right\}
$$

\normalsize

## Key points
* Problem 1: Sharing of $x\mapsto v$ among multiple threads.
    * Use an invariant containing $x\mapsto v$.
* Problem 2: Guaranteeing that the value of $x\mapsto \texttt{Some(n)}$ cannot change.
    * There are 2 _logical_ states of the program associated to the physical state $x\mapsto v$.
        * In the initial $\textsf{NotSet}$ state, `c.try_set(v)` succeeds and updates the state to $\textsf{Set}(v)$ state.
        * Once the state becomes $\textsf{Some}(v)$, the state doesn't change anymore.

## High-level proof idea
\scriptsize
```ocaml
let mk_oneshot () =
    let x = ref(None) in (* Initiate the logical state to NotSet *)
    { try_set = fun n ->
        CAS(x, None, Some(n)), (* Update the state to Set(n) *)
      check = fun () ->
        (* Record the snapshot of the state *)
        let y = !x in fun () ->
            match y, !x with
            | None, _ => () (* easy *)
            | Some(n), None =>
                (* The logical state never changes from Set(n). Impossible. *)
                assert(false)
            | Some(n), Some(m) =>
                (* The logical state never changes from Set(n). n == m *)
                assert(n == m)
            end
    }
```
\normalsize


## Modeling the logical states of `mk_oneshot`
* Unique token: Only the first execution of `c.try_set(v)` succeeds. The execution _consumes_ a unique token need for updating the logical state.
    * The logical state never changes once it's set.
* Broadcasting the message: The first executor consumes the token to generate & broadcast a message that the value is set to `v`.
* Duplicable messages: Threads can keep a copy of the message and use it later.
    * Models the record of the snapshot of the state.
* Agreement of messages: The contents of the copy are the same.
    * $n == m$

## Formalizing the token & message model
* Allocate a "logical" variable $\gamma$ and initialize it with the token for broadcasting.
  $\ownGhost{\gamma}{\textsf{token}}$
    * a fancy notation for $\gamma\mapsto\textsf{token}$, a.k.a. "ghost state"
* The thread that first calls `c.try_set(v)` consumes the token to make a message $\textsf{msg}(v)$.
  $\ownGhost{\gamma}{\textsf{token}}\vs\ownGhost{\gamma}{\textsf{msg}(v)}$
* The message state is duplicable (to be precise, it's persistent). $\ownGhost{\gamma}{\textsf{msg}(v)}\vs\ownGhost{\gamma}{\textsf{msg}(v)}\ast\ownGhost{\gamma}{\textsf{msg}(v)}$
* Any two messages agree on the value.
  $V(\textsf{msg}(n)\cdot\textsf{msg}(m))\implies n=m$.
    * $V(e)$ asserts that $e$ is a valid element.
* If the message is broadcast, the value can't be updated.
  $V(\textsf{msg}(n)\cdot\textsf{token})\implies \FALSE$.

## Associating the logical state with the physical state
* $x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}$
* $x\mapsto\texttt{Some}(n)\ast\ownGhost{\gamma}{\textsf{msg}(n)}$

Invariant?  All possible states and the association of physical & logical state.
$$
I\triangleq
(x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}) \lor
(\exists n.\ x\mapsto\texttt{Some}(n)\ast\ownGhost{\gamma}{\textsf{msg}(n)})
$$

* When the program updates the physical state $x\mapsto...$, the logical state $\ownGhost{\gamma}{...}$ should be updated($\vs$) accordingly in order to reestablish $I$.
$$
\infer[HOARE-VS] {
    P\vs P'\\
    \hoare{P'}{e}{v,Q'} \\
    Q\vs Q'\\
} {
    \hoare{P}{e}{v,Q}
}
$$

## Proof outline
```ocaml
let x = ref(None) in { try_set = ..., check = ... }
```
 Allocate the invariant $\knowInv{\namesp}{I\triangleq
(x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}) \lor
(\exists n.\ x\mapsto\texttt{Some}(n)\ast\ownGhost{\gamma}{\textsf{msg}(n)})
}$
```ocaml
try_set = fun n -> CAS(x, None, Some(n))
```
 Open $\knowInv{\namesp}{I}$ and case analysis.

* $x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}$:
  `CAS` succeeds.
  $\ownGhost{\gamma}{\textsf{token}}\vs\ownGhost{\gamma}{\textsf{msg}(v)}$
* $\exists n.\ x\mapsto\texttt{Some}(n)\ast\ownGhost{\gamma}{\textsf{msg}(n)}$:
  `CAS` fails.

## Proof outline (`check`)
\footnotesize
```ocaml
check = fun () -> let y = !x in
  fun () -> match y with
            | None => ()
            | Some(n) => match !x with ... end
```
\normalsize
 Open $\knowInv{\namesp}{I}$ and case analysis.

* (Case 1) $x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}$: Done.
* (Case 2) $\exists n.\ x\mapsto\texttt{Some}(n)\ast\ownGhost{\gamma}{\textsf{msg}(n)}$:
    * physical snapshot $y\mapsto n$
    * Keep the copy of $\ownGhost{\gamma}{\textsf{msg}(n)}$ by
      $\ownGhost{\gamma}{\textsf{msg}(n)}\vs\ownGhost{\gamma}{\textsf{msg}(n)}\ast\ownGhost{\gamma}{\textsf{msg}(n)}$


## Proof outline (`check`)
$\left\{\knowInv{\namesp}{I}\ast y\mapsto n \ast \ownGhost{\gamma}{\textsf{msg}(n)}\right\}$
\footnotesize
```ocaml
Some(n) => match !x with
           | None => assert(false)
           | Some(m) => assert(n == m)
           end
```
\normalsize
 Open $\knowInv{\namesp}{I}$ and case analysis.

* (Case 2-1) $x\mapsto\texttt{None}\ast\ownGhost{\gamma}{\textsf{token}}$:
    * We have $\textsf{msg}(n)\cdot\textsf{token}$. Contradiction.
* (Case 2-2) $\exists m.\ x\mapsto\texttt{Some}(m)\ast\ownGhost{\gamma}{\textsf{msg}(m)}$:
    * We have $\textsf{msg}(n)\cdot\textsf{msg}(m)$. So $n=m$.

## Resource Algebra (RA)
Read "Ground up" Section 2.1, 3.1 and "Lecture notes" 7.4.

### RA
1. carrier set $M$
2. validity $\mvalFull:M\to\mProp$
3. (partial) core $\mcore{{-}}:M \to \maybe M$
4. composition $(\cdot):M \times M \to M$
* extension order $(\mincl)$
* frame-preserving update

### etc.
* connection of the RA and the logic (ghost state rules)
* view shifts


## Today' Goal: concurrent counter
```ocaml
let newcounter () = ref 0
let rec incr l =
    let n = !l in
    if CAS l n (n+1)
    then ()
    else incr l.
let read l = !l.
```


Provide specifications for counter functions that can be used to prove
$$
\bigg\{\TRUE\bigg\}\quad
\begin{array}{l}
\texttt{let c = newcounter ();}\\
\texttt{(incr c || incr c);}\\
\texttt{read c}
\end{array}\quad
\bigg\{v,\ v=2\bigg\}
$$

## Key points
* Problem 1: Sharing of $l\mapsto n$ among multiple threads.
    * Use an invariant containing $\exists n.\ l\mapsto n$ with some ghost states.
* Problem 2: Tracking increments of other threads.
    * Take 1: Each thread tracks a lower bound(snapshot) of the counter value.
        * When `incr` runs, both the actual value and the thread's snapshot increase by 1.
        * A lower bound is a knowledge (can be duplicated).
* Problem 3: Recursion in `incr`.
    * Apply the spec of `incr` recursively??

## Specification of the counter functions. Take 1.
$$\hoare{\TRUE}{\texttt{newcounter()}}{l, \texttt{counter}(l)\ast \texttt{snapshot}(0)}$$
\begin{gather*}
\{\texttt{counter}(l)\ast\texttt{snapshot}(n)\}\\
{\texttt{incr }l}\\
\{(), \texttt{counter}(l)\ast \texttt{snapshot}(n+1)\}
\end{gather*}
\begin{gather*}
\{\texttt{counter}(l)\ast\texttt{snapshot}(n)\}\\
{\texttt{read }l}\\
\{v, v\ge n \land \texttt{counter}(l)\ast \texttt{snapshot}(n)\}
\end{gather*}

## High-level proof idea for `incr`
```ocaml
let rec incr l =
    (* open invariant, run, close, ....*)
    let n = !l in
    if CAS l n (n+1)
    then ()      (* update the snapshot and return *)
    else incr l. (* recursively apply the spec *)
```

## Formalizing the lower bound (snapshot) model
* $\texttt{snapshot}(\gamma,n)=\ownGhost{\gamma}{\authfrag n}$ (_fragmental_ view)
* a piece of ghost state $\ownGhost{\gamma}{\authfull m}$ (_authoritative view_) that is directly associated with the physical resource and interacts with the snapshots.
    * $\texttt{counter}(\gamma,l)\triangleq \knowInv{\namesp}{\exists m.\ l\mapsto m\ast \ownGhost{\gamma}{\authfull m}}$
* The snapshot is the lower bound of the _actual_ value.
    * $\mval(\authfull m\cdot\authfrag n)\implies n\le m$
* When `incr` runs, both the actual value and the thread's snapshot increase by 1.
    * $\authfull m\cdot\authfrag n\mupd \authfull (m+1)\cdot\authfrag (n+1)$
* The snapshot can be duplicated
    * $\authfrag n\mupd \authfrag n\cdot\authfrag n$
* The snapshot can be updated to newer value
    * $\authfull m\cdot\authfrag n\mupd \authfull m\cdot\authfrag m$
$$ \text{a.k.a.}\ \authm(\mathbb{N}_{\max}) $$


## Proving Recursion
Suppose we prove $\hoare{P}{e}{Q}$ where $e$ is recursive.

* Can we just apply $\hoare{P}{e}{Q}$ for the recursive occurrences?
    * NO: $(P\Ra P)\Ra P$. $(\FALSE\Ra\FALSE)\proves\FALSE$
* Suppose $e$ terminates in $n$ steps. Then the recursive use of $e$ will terminate in at most $n-1$ steps.
    * So it's actually OK to use the spec recursively, if we can express that the spec is applied at a _lower step index_. But we need the notion of reduction steps baked into the logic.
* "later modality" $\later P$: $P$ holds from the next reduction step
* Löb Introduction: $(\later P\Ra P)\proves P$
* Note: Iris's assertions guarantee nothing about termination (_partial correctness_).

## More on $\later$
* Introduction
    * $\later P$ is weaker than $P$. $P\proves\later P$ (`iNext`)
    * Opening invariants
* Elimination
    * Reduction step. `wp_*` tactics automatically strip $\later$ in the context.
    * Timeless propositions: most of innocent propositions like $l\mapsto v$ that don't refer to other invariants. `>ipat`.

## So...
Can you prove
$$
\bigg\{\TRUE\bigg\}\quad
\begin{array}{l}
\texttt{let c = newcounter ();}\\
\texttt{(incr c || incr c);}\\
\texttt{read c}
\end{array}\quad
\bigg\{v,\ v=2\bigg\}
$$
with this spec?
\footnotesize
$$\hoare{\TRUE}{\texttt{newcounter()}}{l, \texttt{counter}(l)\ast \texttt{snapshot}(0)}$$
$$
\hoare{\texttt{counter}(l)\ast\texttt{snapshot}(n)}
{\texttt{incr }l}
{(), \texttt{counter}(l)\ast \texttt{snapshot}(n+1)}
$$
$$
\hoare{\texttt{counter}(l)\ast\texttt{snapshot}(n)}
{\texttt{read }l}
{v, v\ge n \land \texttt{counter}(l)\ast \texttt{snapshot}(n)}
$$
\normalsize

No.

Why? No meaningful interaction between snapshots.

We need to combine the _contribution_ of each thread.

## Take 2
* Each thread holds a share of $\authfrag n$.
    * fractional ownership $\authfrag(q,n)\ (0<q<1)$.
    * full ownership $\authfrag(1, n)$: no other threads are accessing the counter
* Instead of recording the lower bound, record the threads' contribution to the counter value which can be accumulated
    * use the RA $\mathbb{N}_{(+)}$ instead of $\mathbb{N}_{\max}$

$$\texttt{contrib}(\gamma,q,n)=\ownGhost{\gamma}{\authfrag(q,n)}$$
$$
\texttt{contrib}(\gamma,q_1+q_2, n_1+n_2) \provesIff
\texttt{contrib}(\gamma,q_1,n_1)\ast\texttt{contrib}(\gamma,q_2, n_2)
$$
$$
\text{a.k.a.}\ \authm(\maybe{(\mathbb{Q}_{01}\times\mathbb{N})})
$$

## new spec
\footnotesize
$$\hoare{\TRUE}{\texttt{newcounter()}}{l, \texttt{counter}(l)\ast \texttt{contrib}(1,0)}$$
$$
\hoare{\texttt{counter}(l)\ast\texttt{contrib}(q,n)}
{\texttt{incr }l}
{(), \texttt{counter}(l)\ast \texttt{contrib}(q,n+1)}
$$
$$
\hoare{\texttt{counter}(l)\ast\texttt{contrib}(q,n)}
{\texttt{read }l}
{v, v\ge n \land \texttt{counter}(l)\ast \texttt{contrib}(q,n)}
$$
$$
\hoare{\texttt{counter}(l)\ast\texttt{contrib}(1,n)}
{\texttt{read }l}
{v, v=n \land \texttt{counter}(l)\ast \texttt{contrib}(q,n)}
$$
\normalsize

## But..
```ocaml
let rec incr l =
    let n = !l in
    if CAS l n (n+1)
    then n  (* return the previous value *)
    else incr l.
```

$$
\bigg\{\TRUE\bigg\}\
\begin{array}{l}
\texttt{let c = newcounter ();}\\
\texttt{(incr c || incr c)}\\
\end{array}\ \left\{(v_1, v_2),
\begin{array}{l}
(v_1=0\land v_2=1)\lor\\(v_1=1\land v_2=0)
\end{array}
\right\}
$$

# Ghost States in Iris

## Demo
* `oneshot.v` <https://github.com/kaist-cp/study-csl/blob/master/oneshot.v>
* `counter.v`<https://github.com/kaist-cp/study-csl/blob/master/counter.v>

<!-- NOTE:
* https://github.com/matze/mtheme
* slide_level:2 -> all contents under at least 2 #'s
* setting `urlcolor` sets `colorlinks` which changes toc color too
* TODO: \pause, handout
* https://github.com/matze/mtheme/issues/280
* lol this comment block creates a new empty slide if it's placed at the top
-->
