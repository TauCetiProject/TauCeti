/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Simple-pole divisor and continuation helpers at zero and one

Completed zeta functions (`riemannZetaData`, `dedekindZetaData`) share the polar divisor
`Finsupp.single 0 1 + Finsupp.single 1 1` consisting of simple poles at `0` and `1`. This module
collects the symmetry lemmas for that divisor under `s ↦ conj s` and `s ↦ 1 - conj s`, together
with a `HasMeromorphicContinuation` constructor deriving global meromorphy from simple-pole orders
at `0` and `1` and analyticity elsewhere.

## Main results

* `TauCeti.LFunctions.AnalyticLFunctionData.single_zero_add_single_one_conj`: invariance of
  `Finsupp.single 0 1 + Finsupp.single 1 1` under `conj`.
* `TauCeti.LFunctions.AnalyticLFunctionData.single_zero_add_single_one_one_sub_conj`: invariance of
  `Finsupp.single 0 1 + Finsupp.single 1 1` under `s ↦ 1 - conj s`.
* `TauCeti.LFunctions.AnalyticLFunctionData.hasMeromorphicContinuation_of_simple_poles_zero_one`:
  `HasMeromorphicContinuation` from simple-pole orders at `0` and `1` and analyticity away from
  `{0, 1}`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under complex
conjugation. -/
theorem single_zero_add_single_one_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
    map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under
`s ↦ 1 - conj s`. -/
theorem single_zero_add_single_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have e0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
  have e1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
  conv_lhs => arg 2; rw [← map_one (starRingEnd ℂ), ← map_sub]
  rw [single_zero_add_single_one_conj]
  simp only [Finsupp.add_apply, Finsupp.single_apply, e0, e1]
  rw [add_comm]

/-- Construct `HasMeromorphicContinuation` for a card whose polar divisor is
`Finsupp.single 0 1 + Finsupp.single 1 1` from simple-pole orders at `0` and `1` and analyticity
away from `0` and `1`. Global meromorphy is derived from the local orders at `0` and `1` and
analyticity elsewhere. -/
theorem hasMeromorphicContinuation_of_simple_poles_zero_one
    {d : AnalyticLFunctionData}
    (hpolar : d.polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1)
    (h0 : meromorphicOrderAt d.completed 0 = (-1 : ℤ))
    (h1 : meromorphicOrderAt d.completed 1 = (-1 : ℤ))
    (ha : ∀ p : ℂ, p ≠ 0 → p ≠ 1 → AnalyticAt ℂ d.completed p) :
    d.HasMeromorphicContinuation where
  meromorphic p := by
    by_cases hp0 : p = 0
    · subst hp0
      by_contra hm0
      rw [meromorphicOrderAt_of_not_meromorphicAt hm0] at h0
      simp at h0
    by_cases hp1 : p = 1
    · subst hp1
      by_contra hm1
      rw [meromorphicOrderAt_of_not_meromorphicAt hm1] at h1
      simp at h1
    exact (ha p hp0 hp1).meromorphicAt
  meromorphicOrderAt_eq p hp := by
    rw [hpolar] at hp ⊢
    by_cases hp0 : p = 0
    · subst hp0; simp [h0]
    by_cases hp1 : p = 1
    · subst hp1; simp [h1]
    simp [Ne.symm hp0, Ne.symm hp1] at hp
  analyticAt p hp := by
    rw [hpolar] at hp
    refine ha p ?_ ?_ <;> rintro rfl <;> simp at hp

end TauCeti.LFunctions.AnalyticLFunctionData
