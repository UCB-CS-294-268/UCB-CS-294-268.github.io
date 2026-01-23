---
layout: lecture
title: "Lecture 1: Syntax, Goals & Tactics"
date: 2026-01-23
slides_url: https://docs.google.com/presentation/d/1zfPAqFHUYklI_ZA3TF1IO7hFyTTQfFoJBE7cW4x0oVM/edit?usp=sharing
demo_url: https://live.lean-lang.org/#codez=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
---

* TOC
{:toc}

## Motivation for this Course

* **The "Paper Review" Crisis:** As proofs become increasingly intricate, with
subtle corner cases, complex inductive steps, probability bounds that are easy
to hand-wave, it is important to have a foundation that is formally verified
to ensure that our foundational results are built on bedrock rather than sand.
* **Lean is Ready for "Real" Math:** Interactive theorem proving is no longer
a wishful dream. Lean has achieved stunning milestones:
[Liquid Tensor Experiment](https://github.com/leanprover-community/lean-liquid),
[Kepler conjecture](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/formal-proof-of-the-kepler-conjecture/78FBD5E1A3D1BCCB8E0D5B0C463C9FBC),
[Polynomial Freiman-Ruzsa (PFR) theorem](https://teorth.github.io/pfr/).
* **The TCS Frontier (Our Opportunity):** While pure mathematics has huge
coverage in Lean's `Mathlib`, theoretical computer science remains a largely
unexplored frontier. We hope that through course projects, the students of this
course would advance the state of Lean for TCS.
* **Improving AI through formal verification:** Pairing AI with a formal
verification system can unlock new capabilities. Some relevant references:
[AlphaProof](https://www.nature.com/articles/s41586-025-09833-y),
[DeepSeek-Prover](https://arxiv.org/abs/2504.21801),
[LeanCopilot](https://github.com/lean-dojo/LeanCopilot),
[Harmonic Aristotle](https://aristotle.harmonic.fun/). See also
[LeanDojo](https://leandojo.org/) and
[Open AI Lean Gym](https://github.com/openai/lean-gym).

## Installing / Running Lean

There are two main ways to use Lean:

#### VS Code (Recommended)

The best experience is obtained by installing Lean locally, by following a three
step process listed [here](https://lean-lang.org/install/).
1. Install [VS Code](https://code.visualstudio.com/).
2. Install the official **Lean 4** extension in VS Code (search for "lean4" in
   the Extensions view (`Ctrl+Shift+X`)).
3. Complete the extension setup by following the steps in VSCode.

#### Lean 4 Web

You can also try Lean in your browser without installation using
[Lean 4 Web](https://live.lean-lang.org/).


## 1\. Terms and Types

In Lean, everything is a **term**, and every term has a **type**. This is the core judgment of the system, written as `t : T` (read: "term $t$ has type $T$").

Think of this like checking dimensions in physics or data types in programming, but much more powerful.

  * **Data Examples:**
      * `5` is a term. Its type is `Nat`.
      * `"Hello"` is a term. Its type is `String`.
  * **The "Type" of Types:**
      * `Nat` is a term. Its type is `Type`.
      * `Type` is a term. Its type is `Type 1`. (It's turtles all the way up\!)
  * **Logical Examples:**
      * `2 + 2 = 4` is a term (a proposition). Its type is `Prop`.
      * `rfl` (reflexivity) is a term. Its type is `2 + 2 = 4` (it is the *proof*).

## 2\. Transient Commands

These are commands used to query the system. They do not affect the environment permanently.

`#check <term>`: Asks Lean "What is the type of this?" (The most useful command).
```lean
#check 5
-- 5 : Nat
```
`#eval <term>`: Asks Lean's Virtual Machine to compute the value *Note:* You cannot `#eval` a theorem, only data.
```lean
#eval 2 + 2
-- 4
```

`#print <name>`: Shows internal definition of object.


## 3\. Definitions and Theorems

Lean distinguishes between *data* (programs we run) and *propositions* (statements we prove).

**`def`**: Used for data, functions, and definitions where the *computational content* matters.
```lean
def functionName (arg1 : Type1) (arg2 : Type2) : ReturnType :=
  body
```

For example,
```lean
def addOne (n : Nat) : Nat := n + 1
```

**`theorem`** (or **`lemma`**): Used for mathematical statements. *Note:* Semantically, `theorem` and `lemma` are identical. We use them to signal intent. We usually don't care *how* a theorem is proved (proof irrelevance), only that it is true.
```lean
theorem theoremName (arg1 : Type1) (arg2 : Type2) : theoremStatement :=
  body
```

**`example`**: An anonymous definition. Great for scratchpad work or testing a proof without adding it to the global namespace.
```lean
example (arg1 : Type1) (arg2 : Type2) : exampleStatement :=
  body
```

**`abbrev`**: Like `def`, but tells the kernel to unfold (expand) the definition eagerly. Useful for type aliases.

```lean
abbrev NatPairList := List (Nat × Nat)
```

## 4\. Binders: Explicit, Implicit, and Instance

This is the machinery that allows Lean to be concise.

### A. Explicit Binders `(x : α)`

This is the standard function argument. You must provide it every time.

**Example: The Identity Function**

```lean
-- We define a function 'f' that takes a type 'α' (which is a Sort)
-- and a value 'a' of that type, and returns 'a'.
def f (α : Type) (a : α) : α := a

#eval f Nat 5       -- Output: 5
#eval f String "Hi" -- Output: "Hi"
```

*Problem:* It is tedious to type `Nat` or `String` every time. Lean should be able to guess `α` based on the fact that `5` is a `Nat`.

### B. Implicit Binders `{x : α}`

Curly braces tell Lean: "Figure this argument out yourself from context."

**Example: The Implicit Identity**

```lean
def g {α : Type} (a : α) : α := a

#check g 5        -- Lean infers α = Nat
#eval g "Hello"   -- Lean infers α = String

-- If Lean can't guess it, we can force it using `@`:
#check @g Nat 5
```

### C. Instance Binders `[x : α]`

Square brackets tell Lean: "Look in your database of known classes to find this." This is used for Type Classes (like definitions of groups, rings, or simpler things like 'Printable' or 'Addable').

**Motivation:**
If we try to write a generic addition function:

```lean
def add_generic {α : Type} (a b : α) : α := a + b -- ERROR!
```

Lean complains: "I don't know if type `α` supports addition\!"

**Solution:**

```lean
def add_generic {α : Type} [Add α] (a b : α) : α := a + b
```

When we call `add_generic 5 3`, Lean looks for an "Instance" that explains how `Nat` supports `Add`.

-----

## 5\. Structure and Inductive Types (Data Structures)

We can define our own types from scratch using `structure` and `inductive`.

### Structure ("Product") types

```lean
structure Rectangle where
  width : Float
  height : Float

namespace Rectangle

  /-- Area of the rectangle. -/
  def area (r: Rectangle) : Float := r.width * r.height

  /-- Perimeter of the rectangle. -/
  def perimeter (r: Rectangle) : Float := 2 * (r.width + r.height)

end Rectangle

def r : Rectangle := { width := 2.0, height := 3.0 }

#eval r.area        -- 6.0000
#eval r.perimeter   -- 10.0000
```

### Inductive ("Sum") types

**Example: A Binary Tree**

```lean
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

open BinTree

-- A tree containing the numbers 1 and 2
def myTree : BinTree Nat :=
  node leaf 1 (node leaf 2 leaf)
```

## 6\. Motivating Example: Formalizing a Theorem

Let's look at how we translate a math problem into Lean.

### Simple Arithmetic

```lean
theorem simple_math : 2 + 5 = 7 := by
  rfl -- "Reflexivity" (by definition, they are equal)
```

### Fermat's Last Theorem
For all $n > 2$, there do not exist $a, b, c > 0$ such that $a^n + b^n = c^n$.

```lean
theorem fermatsLastTheorem
  (n a b c : Nat) (hn : n > 2) (ha : a > 0) (hb : b > 0) (hc : c > 0)
:
  a^n + b^n ≠ c^n
:= by
```

### Sum of squares of first $n$ natural numbers
To formalize
$$\sum_{i=0}^{n-1} i = \frac{n(n-1)}{2},$$
we need:

1.  A definition of `sum` (recursive function).
2.  Implicit binders (so we don't have to specify we are working in `Nat`).
3.  The theorem statement.

<!-- end list -->

```lean
/--
  Sum of first n natural numbers.
-/
def sumFirstN (n : Nat) :=
  match n with
  | 0 => 0
  | k + 1 => sumUptoN k + k

/--
  Identity: sum_{i=0}^{n-1} i = n * (n - 1) / 2
-/
theorem sumOfFirstNFormula (n : Nat) :
  2 * sumFirstN n = n * (n - 1) := by
  sorry -- Proof left as an exercise
```

Or let's consider something more general.

$$\sum_{i=0}^n i^2 = \frac{n(n+1)(2n+1)}6$$

```lean
/--
 Sum of f(k) for k = 0, 1, 2, ... , n
-/
def sumSeq {α : Type} [Add α] (f : Nat → α) (n : Nat) :=
  match n with
  | 0 => f 0
  | Nat.succ d => sumSeq f d + f n

def square (x : Nat) := x * x

-- or more generally:
def square {α : Type} [Mul α] (x : α) := x * x

theorem sum_of_squares (n : Nat) :
  6 * sumSeq square n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ d hd => sorry
```

### Collatz conjecture

The Collatz conjecture states that for all $n > 0$, repeated application of the following function makes the value $1$:

$$
f(x) := \begin{cases}
x/2 & \text{if } x \text{ is even} \\
3x + 1 & \text{if } x \text{ is odd}
\end{cases}
$$

```lean
/--
  The Collatz Map: if n is even, n/2, else 3n + 1.
-/
def collatzMap (n : Nat) : Nat :=
  if n % 2 == 0 then
    n / 2
  else
    3 * n + 1

/--
  Returns f applied d times on n.
  Note: In Lean's standard library, this is `Nat.iterate`.
-/
def applyN (f : Nat → Nat) (d n : Nat) : Nat :=
  match d with
  | 0 => n  -- Base case: Applying f zero times returns n (Identity)
  | k + 1 => applyN f k (f n)  -- Recursive step

/--
  The Collatz conjecture: For all n > 0, there exists d such that
  f^d(n) = 1, for the Collatz map f.
-/
theorem collatz_conjecture (n : Nat) (h : n > 0) :
  ∃ d : Nat, applyN collatzMap d n = 1 := by
  sorry
```

## Side notes

These are some advanced notes that can be skipped for now (or addressed only if asked).

**1. "Is there anything else?" regarding Transient commands:**

  * `#reduce <term>`: stronger than `#eval`. It uses the kernel to reduce terms to their normal form.
    * *Warning:* `#reduce` is trustworthy but slow. Don't run `#reduce` on large numbers\!
  * `#synth`: "Synthesize". Useful for debugging instances. e.g., `#synth Add Nat` checks if Lean knows how to add numbers.
  * `#check_failure`: Useful for teaching. It succeeds only if the term causes an error.

**2. "What are other keywords? Is it possible to define one's own?"**

  * **Other standard keywords:** `inductive` (for types), `structure` (for records/classes), `class` (for type classes), `axiom` (to postulate truths without proof—dangerous\!), `opaque` (a constant with a hidden definition).

```lean
axiom two_plus_two_equals_five_ax : 2 + 2 = 5

theorem two_plus_two_equals_five : 2 + 2 = 5 := by
  apply two_plus_two_equals_five_ax
```

  * **Custom keywords:** Yes, Lean is fully extensible. You can write your own keywords and syntax (DSLs) using Lean's metaprogramming framework (`macro`, `syntax`, `elab`). However, this is an advanced topic (Lecture 10+).




## 7\. Introduction to Simple Tactics

### rfl (Reflexivity)

The `rfl` tactic is used to prove goals that are true **by definition**
(*definitionally equal*).

**Usage**
- Use it when the Left Hand Side (LHS) evaluates to exactly the same term as the Right Hand Side (RHS).
- Automatically handles simple computations.

```lean
example : 2 + 2 = 4 := by
  rfl

example (a : Nat) : a = a := by
  rfl
````

---

### intro (Introducing Hypotheses)

The `intro` tactic moves premises from the goal into the local context.

**Usage**

* Essential for proving implications (`→`) and universal quantifiers (`∀`).
* You can name introduced variables immediately.

```lean
example (p q : Prop) : p → q → p := by
  intro h_p h_q
  exact h_p
```

---

### exact (Exact Match)

The `exact` tactic closes the goal by providing a term whose type **exactly matches** the goal.

**Usage**

* If you already have a hypothesis of the required type, `exact` finishes the proof.
* The match must be definitional.

```lean
example (p : Prop) (h : p) : p := by
  exact h
```

---

### apply (Backward Reasoning)

The `apply` tactic works backwards by matching the goal with the conclusion of a lemma or function.

**Usage**

* If the goal is `Q` and you have `h : P → Q`, `apply h` changes the goal to `P`.

```lean
example (p q : Prop)
        (h_imp : p → q) (h_p : p) : q := by
  apply h_imp
  exact h_p
```

---

### rw (Rewrite)

The `rw` tactic rewrites terms using an equality hypothesis.

**Usage**

* If `h : a = b`, then `rw [h]` replaces `a` with `b`.
* Use `rw [← h]` to rewrite right-to-left.

```lean
example (a b c : Nat)
        (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  exact h2
```

---

### simp (Simplifier)

The `simp` tactic automatically simplifies goals using a database of rewrite rules.

**Usage**

* Very effective for arithmetic identities, boolean logic, and standard definitions.
* Unlike `rw`, it performs many rewrites automatically.

```lean
example (x : Nat) : x + 0 = x := by
  simp

example (p : Prop) : p ∧ True ↔ p := by
  simp
```

---

### cases (Case Analysis)

The `cases` tactic performs case analysis on inductive types.

**Common uses**

* `∨` (Or): splits into left and right cases
* `∧` (And): extracts components
* `Nat`: splits into `zero` and `succ n`

```lean
example (n : Nat) : n = 0 ∨ n ≠ 0 := by
  cases n with
  | zero =>
      left --we will get to this in Lecture 3
      rfl
  | succ k =>
      right --we will get to this in Lecture 3
      intro h
      cases h
```

---

### have (Intermediate Goals)

The `have` tactic introduces and proves a local lemma inside a proof.

**Usage**

* Useful for structuring longer proofs.
* Adds the proven statement to the context.

```lean
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := by 
    apply hpq
    exact hp
  exact hq
```

---

### induction (Inductive Proofs)

The `induction` tactic is like `cases`, but also provides an **induction hypothesis**.

**Usage**

* Essential for `Nat`, `List`, `Tree`, and other inductive types.
* Produces a base case and an inductive step.

```lean
example (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Nat.add_succ, ih]
```

---

### constructor (Constructing Data)

The `constructor` tactic applies the canonical constructor of the goal’s inductive type.

**Usage**

* `∧` (And): splits into two subgoals
* `∃` (Exists): prepares the goal to provide a witness

```lean
example (p q : Prop)
        (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
  /- the symbol · is syntax for "fill in the current subgoal"
  it makes goal structure explicit, the proof will not be affected if removed. -/
```

## 8. Natural Numbers

In Lean 4, natural numbers are defined inductively, forming the foundation for arithmetic proofs. This section covers the definition, core axioms, basic operations, and fundamental theorems essential for proving properties about numbers.

---

### 8.1 Inductive Definition

The set of natural numbers ($\mathbb{N}$) is defined as an inductive type with two constructors: a base case and a successor function.

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
````

* **`zero`**: Represents the number $0$.
* **`succ`**: Represents the successor function; `succ n` corresponds to $n + 1$.

**Intuition:** Every natural number is either `0` or the successor of another natural number.

---

### 8.2 The Peano Axioms

The inductive definition of `Nat` in Lean satisfies the Peano axioms, which characterize the natural numbers:

* **Zero exists:** $0 \in \mathbb{N}$.
* **Successor:** For every $n \in \mathbb{N}$, there is a successor $S(n) \in \mathbb{N}$.
* **Injectivity:** The successor function is injective.
  If $S(n) = S(m)$, then $n = m$.
* **Disjointness:** Zero is not the successor of any natural number:
  $\forall n,; S(n) \neq 0$.
* **Induction:**
  If a property $P$ holds for $0$, and
  if $P(n) \Rightarrow P(S(n))$ for all $n$,
  then $P$ holds for all natural numbers.

---

### 8.3 Basic Operations

Standard arithmetic operations are defined recursively on the structure of `Nat`.

#### Addition (`Nat.add`)

Defined by recursion on the second argument:

* $n + 0 = n$
* $n + \text{succ } m = \text{succ } (n + m)$

#### Multiplication (`Nat.mul`)

Defined as repeated addition:

* $n * 0 = 0$
* $n * \text{succ } m = n * m + n$

#### Power (`Nat.pow`)

Defined as repeated multiplication:

* $n^0 = 1$
* $n^{\text{succ } m} = (n^m) * n$

---

### 8.4 Fundamental Theorems

These theorems are frequently used in proofs to rewrite terms into canonical forms.

#### Associativity

Allows regrouping of operations.

```lean
Nat.add_assoc (a b c : Nat) : (a + b) + c = a + (b + c)
Nat.mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c)
```

#### Commutativity

Allows swapping the order of operands.

```lean
Nat.add_comm (a b : Nat) : a + b = b + a
Nat.mul_comm (a b : Nat) : a * b = b * a
```

#### Identity & Zero Properties

**Additive identity:** $0$

```lean
Nat.add_zero (n : Nat) : n + 0 = n
Nat.zero_add (n : Nat) : 0 + n = n
```

**Multiplicative identity:** $1$

```lean
Nat.mul_one (n : Nat) : n * 1 = n
Nat.one_mul (n : Nat) : 1 * n = n
```

**Zero property of multiplication:**

```lean
Nat.mul_zero (n : Nat) : n * 0 = 0
Nat.zero_mul (n : Nat) : 0 * n = 0
```

#### Distributivity

Connects addition and multiplication.

**Left distributivity:**

```lean
Nat.mul_add (a b c : Nat) : a * (b + c) = a * b + a * c
```

**Right distributivity:**

```lean
Nat.add_mul (a b c : Nat) : (a + b) * c = a * c + b * c
```

---

### 8.5 Useful Tactics for `Nat`

* **`simp`**
  Automatically simplifies goals using lemmas marked with the `@[simp]` attribute (e.g. `Nat.add_zero`).

* **`rw` (rewrite)**
  Manually applies specific theorems to transform the goal or hypotheses, e.g.

  ```lean
  rw [Nat.add_comm]
  ```

* **`ac_rfl`**
  Proves equalities up to associativity and commutativity.

* **`ring`**
  Solves equalities in commutative semirings and rings, handling associativity, commutativity, and distributivity automatically.

* **`linarith`**
  Solves goals involving linear arithmetic inequalities.


### 8.6 Examples
Example of using **`simp`** with `Nat` properties:
```lean
example (a b c : Nat) : a + b + c = b + (a + c) := by
  -- reassociate and commute to match the RHS
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```
Example of using **`rw`** with `Nat` properties:
```lean
example (a b c : Nat) : a + (b + c) = b + (a + c) := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm a b]
  rw [← Nat.add_assoc]
```
Example of using **`linarith`**:
```lean
example (x y : Nat) (h1 : x + y = 10) (h2 : x ≥ 7) : y ≤ 3 := by
  linarith
```
Example of using **`ring`**:
```lean
example (a b : Nat) : (a + b) * (a + b) = a*a + 2*a*b + b*b := by
  ring
```