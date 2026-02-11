/-
  CS 294-268 (Spring 2026)
  Homework 1: Logic, Tactics, Induction, Calculation — SOLUTIONS
-/

import Mathlib.Tactic

-- =================================================================
-- PART 1: GETTING STARTED & BASIC EVALUATION
-- =================================================================

theorem twoPlusTwoEqualsFour : 2 + 2 = 4 := by
  rfl

theorem add_zero_simp (n : Nat) : n + 0 = n := by
  simp

theorem rw_example (a b c : Nat) (h : a = b) : a + c = b + c := by
  rw [h]

-- =================================================================
-- PART 2: PROPOSITIONAL LOGIC BASICS
-- =================================================================

theorem imp_trans (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by
  intro hp
  apply h2
  apply h1
  exact hp

theorem have_example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := by
    exact hpq hp
  exact hq

theorem and_intro (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

theorem and_left (p q : Prop) (h : p ∧ q) : p := by
  cases h with
  | intro hp hq =>
    exact hp

theorem or_left (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp

theorem or_elim (p q r : Prop) (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  cases h with
  | inl hp' =>
    exact hp hp'
  | inr hq' =>
    exact hq hq'

theorem iff_intro (p q : Prop) (h1 : p → q) (h2 : q → p) : p ↔ q := by
  constructor
  · exact h1
  · exact h2

theorem my_not_not_intro (p : Prop) : p → ¬¬p := by
  intro hp hnp
  exact hnp hp

-- =================================================================
-- PART 3: PROOF BY CALCULATION (EQUATIONAL REASONING)
-- =================================================================

theorem add_assoc_calc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simp [Nat.add_assoc]

theorem add_comm_calc (a b : Nat) : a + b = b + a := by
  -- Try a calc-style proof, but using the library lemma is fine here.
  simp [Nat.add_comm]

-- =================================================================
-- PART 4: INDUCTION ON NAT
-- =================================================================

def sumFirstN (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => sumFirstN k + k

theorem sumFirstN_succ (n : Nat) : sumFirstN (n + 1) = sumFirstN n + n := by
  simp [sumFirstN]

theorem add_zero_ind (n : Nat) : n + 0 = n := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    -- simp knows (Nat.succ k) + 0 = Nat.succ (k + 0)
    simp

theorem zero_add_simp (n : Nat) : 0 + n = n := by
  simp

theorem add_one_eq_succ (n : Nat) : n + 1 = Nat.succ n := by
  simp

theorem sumOfFirstNFormula (n : Nat) : 2 * sumFirstN n = n * (n - 1) := by
  induction n with
  | zero =>
      simp [sumFirstN]
  | succ k ih =>
      cases k with
      | zero =>
          -- n = 1
          simp [sumFirstN]
      | succ t =>
          -- n = t+2, and (t+2 - 1) = t+1, (t+1 - 1) = t
          -- Expand sumFirstN once, then use IH, then finish by distributivity.
          have ih' : 2 * sumFirstN (Nat.succ t) = Nat.succ t * (Nat.succ t - 1) := ih
          calc
            2 * sumFirstN (Nat.succ (Nat.succ t))
                = 2 * (sumFirstN (Nat.succ t) + Nat.succ t) := by
                    simp [sumFirstN]
            _ = 2 * sumFirstN (Nat.succ t) + 2 * Nat.succ t := by
                    simp [Nat.mul_add]
            _ = (Nat.succ t * (Nat.succ t - 1)) + 2 * Nat.succ t := by
                    simp [ih']
            _ = (Nat.succ t * t) + 2 * Nat.succ t := by
                    simp
            _ = (Nat.succ t * t) + (Nat.succ t * 2) := by
                    simp [Nat.mul_comm]
            _ = Nat.succ t * (t + 2) := by
                    -- s*t + s*2 = s*(t+2)
                    simp [Nat.mul_add]
            _ = (t + 2) * Nat.succ t := by
                    simp [Nat.mul_comm]
            _ = Nat.succ (Nat.succ t) * (Nat.succ (Nat.succ t) - 1) := by
                    simp [Nat.add_comm, Nat.add_left_comm]


-- =================================================================
-- PART 5: RECURSION AND INDUCTION ON LISTS
-- =================================================================

def myLen {α : Type} (L : List α) : Nat :=
  match L with
  | [] => 0
  | _ :: t => 1 + myLen t

theorem len_append {α : Type} (L M : List α) :
  myLen (L ++ M) = myLen L + myLen M := by
  induction L with
  | nil =>
    simp [myLen]
  | cons x xs ih =>
    simp [myLen, ih, Nat.add_assoc, Nat.add_comm]

def myMap {α β : Type} (f : α → β) (L : List α) : List β :=
  match L with
  | [] => []
  | x :: xs => f x :: myMap f xs

theorem len_map {α β : Type} (f : α → β) (L : List α) :
  myLen (myMap f L) = myLen L := by
  induction L with
  | nil =>
    simp [myLen, myMap]
  | cons x xs ih =>
    simp [myLen, myMap, ih]

def myRev {α : Type} (L : List α) : List α :=
  match L with
  | [] => []
  | x :: xs => myRev xs ++ [x]

theorem rev_append {α : Type} (L M : List α) :
  myRev (L ++ M) = myRev M ++ myRev L := by
  induction L with
  | nil =>
    simp [myRev]
  | cons x xs ih =>
    -- myRev ((x::xs)++M) = myRev (xs++M) ++ [x]
    -- use IH and associativity of append
    simp [myRev, ih, List.append_assoc]

theorem len_rev {α : Type} (L : List α) :
  myLen (myRev L) = myLen L := by
  induction L with
  | nil =>
    simp [myRev, myLen]
  | cons x xs ih =>
    -- myRev (x::xs) = myRev xs ++ [x]
    -- then use len_append + ih
    simp [myRev, myLen, len_append, ih, Nat.add_comm]

-- =================================================================
-- PART 6: MIXING LOGIC + DATA (CASES PRACTICE)
-- =================================================================

theorem nat_zero_or_succ (n : Nat) : n = 0 ∨ ∃ k, n = k + 1 := by
  cases n with
  | zero =>
    left
    rfl
  | succ k =>
    right
    refine ⟨k, ?_⟩
    simp

theorem list_nil_or_cons {α : Type} (L : List α) :
  L = [] ∨ ∃ x xs, L = x :: xs := by
  cases L with
  | nil =>
    left
    rfl
  | cons x xs =>
    right
    refine ⟨x, xs, rfl⟩
