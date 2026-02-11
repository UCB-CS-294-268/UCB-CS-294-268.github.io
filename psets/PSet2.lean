/-
  CS 294-268 (Spring 2026)
  Homework 2: Structured Proofs & DFA Correctness

  Instructions:
  1. Please the PSet2.lean file in any working mathlib project folder (for example PSet1 folder)
  2. Replace every `sorry` with a valid proof.
  3. If a task asks for an `#eval`, uncomment the line and check the output.
  4. Prefer the tactics listed in each task.
  5. Submit your completed .lean file.

  Topics practiced:
  - Essential logical reasoning (∧, ∨, ∃, ∀, ∃!)
  - Deterministic Finite Automata (DFAs)
  - Proving DFA correctness
-/

import Mathlib.Tactic

-- =================================================================
-- PART 1: ESSENTIAL LOGIC WARMUP
-- =================================================================

/-
  Task 1: And commutativity.
  Prove that P ∧ Q is equivalent to Q ∧ P.
  Tactics: `constructor`, `intro`, `cases`, `exact`.
-/
theorem my_and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  sorry

/-
  Task 2: Existential introduction.
  Prove that there exists a natural number equal to 5.
  Tactics: `exists`, `rfl`.
-/
theorem exists_five : ∃ n : Nat, n = 5 := by
  sorry

/-
  Task 3: Universal quantifier exercise.
  If ∀ x, P x, then for any specific y, we have P y.
  Tactics: `intro`, `apply`.
-/
theorem forall_elim {α : Type} (P : α → Prop) (y : α) :
  (∀ x, P x) → P y := by
  sorry

/-
  Task 4: Uniqueness of zero.
  Prove that there is a unique natural number n such that n = 0.
  Tactics: `refine`, `intro`, `simp`.
  Hint: Use `refine ⟨0, rfl, ?_⟩` to provide witness and existence proof.
-/
theorem my_unique_zero : ∃! n : Nat, n = 0 := by
  sorry

/-
  Task 5: Case analysis with decidable.
  Prove: For any n : Nat, either n = 0 or n ≠ 0.
  Tactics: `by_cases`, `left`, `right`, `exact`.
-/
theorem nat_eq_zero_or_not (n : Nat) : n = 0 ∨ n ≠ 0 := by
  sorry

-- =================================================================
-- PART 2: DETERMINISTIC FINITE AUTOMATA (DFA) - DEFINITIONS
-- =================================================================

/-
  DFA structure from Lecture 3.
  A DFA has:
  - A type of states
  - A start state
  - A step function (state × symbol → state)
  - An accept predicate (state → Bool)
-/
structure DFA (α : Type) where
  State  : Type
  start  : State
  step   : State → α → State
  accept : State → Bool

/-
  Run a DFA on a word (list of symbols).
  Returns the final state reached.
-/
def run {α : Type} (M : DFA α) : M.State → List α → M.State
| q, []     => q
| q, a::w  => run M (M.step q a) w

/-
  A DFA accepts a word if the final state is accepting.
-/
def accepts {α : Type} (M : DFA α) (w : List α) : Bool :=
  M.accept (run M M.start w)

/-
  FORMAL LANGUAGES

  A language over alphabet α is a set of words (lists of symbols from α).
  We use Lean's Set type to represent languages.
-/
abbrev Language (α : Type) := Set (List α)

/-
  The language recognized/accepted by a DFA M is the set of all words
  that M accepts.
-/
def DFA.language {α : Type} (M : DFA α) : Language α :=
  { w | accepts M w = true }

/-
  Alternative notation: w ∈ M.language means M accepts w.
  This connects the Boolean predicate `accepts` with set membership.
-/
theorem mem_language_iff {α : Type} (M : DFA α) (w : List α) :
  w ∈ M.language ↔ accepts M w = true :=
  sorry

/-
  Two-symbol alphabet (0 and 1, represented as O and I).
-/
inductive Bit where
  | O | I
deriving Repr, DecidableEq

open Bit

-- =================================================================
-- PART 3: THE endsWithI DFA
-- =================================================================

/-
  DFA that accepts exactly the words ending with I.

  States: Bool
  - false = "last symbol was O (or no symbol seen yet)"
  - true = "last symbol was I"
-/
def endsWithI : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun _ b =>
    match b with
    | O => false
    | I => true
, accept := fun st => st
}

/-
  Uncomment to test the DFA.
-/
-- #eval accepts endsWithI [O, I, O, I]  -- true
-- #eval accepts endsWithI [I, O]        -- false
-- #eval accepts endsWithI []            -- false

-- =================================================================
-- PART 4: HELPER LEMMAS ABOUT run
-- =================================================================

/-
  Task 6: run on empty word.
  Running a DFA on an empty word leaves the state unchanged.
  Tactics: `rfl`.
-/
theorem run_nil {α : Type} (M : DFA α) (q : M.State) :
  run M q [] = q := by
  sorry

/-
  Task 7: run on singleton.
  Running on a single symbol is just one step.
  Tactics: `simp [run]`.
-/
theorem run_singleton {α : Type} (M : DFA α) (q : M.State) (a : α) :
  run M q [a] = M.step q a := by
  sorry

/-
  Task 8: run is compositional.
  Running on w₁ ++ w₂ is the same as running on w₁, then running on w₂.
  Tactics: `induction w₁`, `simp [run]`.
  Hint: Use induction on w₁.
-/
theorem run_append {α : Type} (M : DFA α) (q : M.State) (w₁ w₂ : List α) :
  run M q (w₁ ++ w₂) = run M (run M q w₁) w₂ := by
  sorry

-- =================================================================
-- PART 5: PROVING endsWithI CORRECTNESS - STEP FUNCTION
-- =================================================================

/-
  Task 9: endsWithI step function on O.
  After reading O, the state becomes false.
  Tactics: `rfl`.
-/
theorem endsWithI_step_O (st : Bool) :
  endsWithI.step st O = false := by
  sorry

/-
  Task 10: endsWithI step function on I.
  After reading I, the state becomes true.
  Tactics: `rfl`.
-/
theorem endsWithI_step_I (st : Bool) :
  endsWithI.step st I = true := by
  sorry

-- =================================================================
-- PART 6: PROVING endsWithI CORRECTNESS - RUN BEHAVIOR
-- =================================================================

/-
  Task 11: Running endsWithI from false on [O].
  Prove that run endsWithI false [O] = false.
  Tactics: `simp [run, endsWithI]`.
-/
theorem endsWithI_run_false_O :
  run endsWithI false [O] = false := by
  sorry

/-
  Task 12: Running endsWithI from false on [I].
  Prove that run endsWithI false [I] = true.
  Tactics: `simp [run, endsWithI]`.
-/
theorem endsWithI_run_false_I :
  run endsWithI false [I] = true := by
  sorry

/-
  Task 13: Running endsWithI on any word ending with I.
  If w ends with I, then run endsWithI false w = true.
  Tactics: `simp [run_append, run, endsWithI]`.
  Hint: Use run_append to split the word.
-/
theorem endsWithI_run_ends_with_I (w : List Bit) :
  run endsWithI false (w ++ [I]) = true := by
  sorry

/-
  Task 14: Running endsWithI on any word ending with O.
  If w ends with O, then run endsWithI false w = false.
  Tactics: `simp [run_append, run, endsWithI]`.
-/
theorem endsWithI_run_ends_with_O (w : List Bit) :
  run endsWithI false (w ++ [O]) = false := by
  sorry

-- =================================================================
-- PART 7: LANGUAGES AND CORRECTNESS
-- =================================================================

/-
  Helper definition: a word ends with I if its last element is I.
-/
def endsWithIWord : List Bit → Prop
  | [] => False
  | [O] => False
  | [I] => True
  | _ :: w' => endsWithIWord w'

/-
  The language of words ending with I, defined as a set.
-/
def endsWithI_lang : Language Bit :=
  { w | endsWithIWord w }

/-
  Task 15: Membership in endsWithI_lang.
  Prove that [I] is in the language of words ending with I.
  Tactics: `simp [endsWithI_lang, endsWithIWord]`.
-/
theorem I_in_endsWithI_lang : [I] ∈ endsWithI_lang := by
  sorry

/-
  Task 16: Non-membership in endsWithI_lang.
  Prove that [O] is not in the language of words ending with I.
  Tactics: `simp [endsWithI_lang, endsWithIWord]`.
-/
theorem O_not_in_endsWithI_lang : [O] ∉ endsWithI_lang := by
  sorry

/-
  Task 17: endsWithI accepts [I].
  Prove that endsWithI accepts the single-symbol word [I].
  Tactics: `simp [accepts, run, endsWithI]`.
-/
theorem endsWithI_accepts_I :
  accepts endsWithI [I] = true := by
  sorry

/-
  Task 18: endsWithI rejects [O].
  Prove that endsWithI rejects the single-symbol word [O].
  Tactics: `simp [accepts, run, endsWithI]`.
-/
theorem endsWithI_rejects_O :
  accepts endsWithI [O] = false := by
  sorry

/-
  Task 19: endsWithI rejects empty word.
  Prove that endsWithI rejects the empty word.
  Tactics: `simp [accepts, run, endsWithI]`.
-/
theorem endsWithI_rejects_empty :
  accepts endsWithI [] = false := by
  sorry

/-
  Task 20: endsWithI accepts words ending with I.
  For any word w, endsWithI accepts w ++ [I].
  Tactics: `simp [accepts, endsWithI_run_ends_with_I]`.
  Hint: Use endsWithI_run_ends_with_I.
-/
theorem endsWithI_accepts_suffix_I (w : List Bit) :
  accepts endsWithI (w ++ [I]) = true := by
  sorry

/-
  Task 21: endsWithI rejects words ending with O.
  For any word w, endsWithI rejects w ++ [O].
  Tactics: `simp [accepts, endsWithI_run_ends_with_O]`.
-/
theorem endsWithI_rejects_suffix_O (w : List Bit) :
  accepts endsWithI (w ++ [O]) = false := by
  sorry

/-
  Task 22: Language equality for endsWithI.
  Prove that the language recognized by endsWithI equals endsWithI_lang.
  Tactics: `ext w`, `simp [DFA.language, endsWithI_lang, mem_language_iff]`.
  This requires proving the iff in both directions.
-/
theorem endsWithI_language_correct :
  endsWithI.language = endsWithI_lang := by
  sorry

-- =================================================================
-- PART 8: THE evenIs DFA
-- =================================================================

/-
  DFA that accepts words with an even number of I's.

  States: Bool
  - false = "even number of I's seen so far"
  - true = "odd number of I's seen so far"
-/
def evenIs : DFA Bit :=
{ State  := Bool
, start  := false
, step   := fun st b =>
    match b with
    | O => st
    | I => !st
, accept := fun st => !st
}

-- #eval accepts evenIs []                -- true (0 I's is even)
-- #eval accepts evenIs [I, I]            -- true (2 I's is even)
-- #eval accepts evenIs [O, I, O, I]      -- true (2 I's is even)
-- #eval accepts evenIs [I, O, O]         -- false (1 I is odd)

-- =================================================================
-- PART 9: PROVING evenIs CORRECTNESS
-- =================================================================

/-
  Task 20: evenIs step on O preserves state.
  Reading O doesn't change the state.
  Tactics: `rfl`.
-/
theorem evenIs_step_O (st : Bool) :
  evenIs.step st O = st := by
  sorry

/-
  Task 21: evenIs step on I flips state.
  Reading I flips the state.
  Tactics: `rfl`.
-/
theorem evenIs_step_I (st : Bool) :
  evenIs.step st I = !st := by
  sorry

/-
  Helper: count the number of I's in a word.
-/
def countI : List Bit → Nat
  | [] => 0
  | O :: w => countI w
  | I :: w => 1 + countI w

/-
  The language of words with an even number of I's, defined as a set.
-/
def evenI_lang : Language Bit :=
  { w | Even (countI w) }

/-
  Task 23: Membership in evenI_lang.
  Prove that the empty word is in the language (0 is even).
  Tactics: `simp [evenI_lang, countI]`, `decide`.
-/
theorem empty_in_evenI_lang : [] ∈ evenI_lang := by
  sorry

/-
  Task 24: Membership in evenI_lang.
  Prove that [I, I] is in the language (2 is even).
  Tactics: `simp [evenI_lang, countI]`, `decide`.
-/
theorem II_in_evenI_lang : [I, I] ∈ evenI_lang := by
  sorry

/-
  Task 25: Non-membership in evenI_lang.
  Prove that [I] is not in the language (1 is odd).
  Tactics: `simp [evenI_lang, countI]`, `decide`.
-/
theorem I_not_in_evenI_lang : [I] ∉ evenI_lang := by
  sorry

/-
  Task 26: evenIs accepts empty word.
  The empty word has 0 I's, which is even.
  Tactics: `simp [accepts, run, evenIs]`.
-/
theorem evenIs_accepts_empty :
  accepts evenIs [] = true := by
  sorry

/-
  Task 27: evenIs accepts [I, I].
  Two I's is an even number.
  Tactics: `simp [accepts, run, evenIs]`.
-/
theorem evenIs_accepts_II :
  accepts evenIs [I, I] = true := by
  sorry

/-
  Task 28: evenIs rejects [I].
  One I is an odd number.
  Tactics: `simp [accepts, run, evenIs]`.
-/
theorem evenIs_rejects_I :
  accepts evenIs [I] = false := by
  sorry

/-
  Task 29: Reading two I's returns to the same state.
  Prove that after reading I twice, we return to the original state.
  Tactics: `cases st`, `simp [run, evenIs]`.
  Hint: Do case analysis on the starting state st.
-/
theorem evenIs_two_I_same_state (st : Bool) :
  run evenIs st [I, I] = st := by
  sorry

/-
  Task 30: Language equality for evenIs.
  Prove that the language recognized by evenIs equals evenI_lang.
  Tactics: `ext w`, `simp [DFA.language, evenI_lang, mem_language_iff]`.
  This is the main correctness theorem for evenIs!
-/
theorem evenIs_language_correct :
  evenIs.language = evenI_lang := by
  sorry
