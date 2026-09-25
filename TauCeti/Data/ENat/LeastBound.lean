/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice

/-!
# The least natural number satisfying a predicate, in `ℕ∞`

For a predicate `P : ℕ → Prop`, `TauCeti.leastENatBound P` is the infimum in `ℕ∞` of the natural
numbers satisfying `P`. It is `⊤` exactly when no natural number satisfies `P`, so an invariant
defined as the least `n` for which some bound holds takes the value `⊤` rather than being
undefined when no bound holds at all. Invariants of this shape are cohomological dimensions,
where `P n` says that cohomology vanishes above degree `n`.

When `P` is monotone (a bound at `m` gives a bound at every `n ≥ m`), the characterization
`leastENatBound P ≤ n ↔ P n` recovers the predicate from the invariant.

## Main results

* `TauCeti.leastENatBound`: the infimum in `ℕ∞` of the natural numbers satisfying a predicate.
* `TauCeti.leastENatBound_le_iff`: for a monotone predicate, `leastENatBound P ≤ n ↔ P n`.
* `TauCeti.leastENatBound_eq_top_iff`: the value is `⊤` exactly when the predicate never holds.
* `TauCeti.leastENatBound_antitone`: a weaker predicate has a smaller least bound.
-/

public section

namespace TauCeti

variable {P Q : ℕ → Prop}

/-- The least natural number satisfying `P`, as an element of `ℕ∞`: the infimum of the natural
numbers satisfying `P`, which is `⊤` when there are none. -/
noncomputable def leastENatBound (P : ℕ → Prop) : ℕ∞ :=
  ⨅ n : {n : ℕ // P n}, ((n : ℕ) : ℕ∞)

/-- A lower bound for the least bound is a lower bound for every natural number satisfying the
predicate. -/
theorem le_leastENatBound_iff {m : ℕ∞} : m ≤ leastENatBound P ↔ ∀ n : ℕ, P n → m ≤ n := by
  simp [leastENatBound]

/-- The least bound is at most any natural number satisfying the predicate. -/
theorem leastENatBound_le {n : ℕ} (h : P n) : leastENatBound P ≤ n :=
  iInf_le_of_le ⟨n, h⟩ le_rfl

/-- The least bound is `⊤` exactly when no natural number satisfies the predicate. -/
@[simp]
theorem leastENatBound_eq_top_iff : leastENatBound P = ⊤ ↔ ∀ n : ℕ, ¬P n := by
  simp [leastENatBound]

/-- The least bound is attained: when some natural number satisfies `P`, the least one does. -/
theorem leastENatBound_eq_find [DecidablePred P] (h : ∃ n, P n) :
    leastENatBound P = Nat.find h :=
  le_antisymm (leastENatBound_le (Nat.find_spec h))
    (le_leastENatBound_iff.2 fun _ hn ↦ ENat.natCast_le_natCast.2 (Nat.find_min' h hn))

/-- For a monotone predicate, the least bound is at most `n` exactly when `n` satisfies the
predicate. -/
theorem leastENatBound_le_iff (hP : Monotone P) (n : ℕ) : leastENatBound P ≤ n ↔ P n := by
  classical
  refine ⟨fun hle ↦ ?_, leastENatBound_le⟩
  by_cases h : ∃ m, P m
  · rw [leastENatBound_eq_find h, ENat.natCast_le_natCast] at hle
    exact hP hle (Nat.find_spec h)
  · rw [leastENatBound_eq_top_iff.2 (not_exists.1 h), top_le_iff] at hle
    exact absurd hle (ENat.natCast_ne_top n)

/-- A weaker predicate has a smaller least bound. -/
theorem leastENatBound_antitone : Antitone leastENatBound :=
  fun _ _ hPQ ↦ le_leastENatBound_iff.2 fun _ hn ↦ leastENatBound_le (hPQ _ hn)

end TauCeti
