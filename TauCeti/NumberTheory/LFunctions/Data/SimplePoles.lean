/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Simple-pole divisor helpers at zero and one

Completed zeta functions (`riemannZetaData`, `dedekindZetaData`) share the polar divisor
`Finsupp.single 0 1 + Finsupp.single 1 1` consisting of simple poles at `0` and `1`. This module
collects the symmetry lemmas for that divisor under `s ↦ conj s` and `s ↦ 1 - conj s`.

## Main results

* `TauCeti.LFunctions.AnalyticLFunctionData.single_zero_one_add_single_one_one_conj`: invariance
  of `Finsupp.single 0 1 + Finsupp.single 1 1` under `conj`.
* `TauCeti.LFunctions.AnalyticLFunctionData.single_zero_one_add_single_one_one_one_sub_conj`:
  invariance of `Finsupp.single 0 1 + Finsupp.single 1 1` under `s ↦ 1 - conj s`.
* `hasMeromorphicContinuation_of_polarOrder_eq_single_zero_one_add_single_one_one`:
  shared `HasMeromorphicContinuation` constructor for cards with simple poles at `0` and `1`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under complex
conjugation. -/
theorem single_zero_one_add_single_one_one_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  simp [Finsupp.single_apply, eq_comm (a := (0 : ℂ)), eq_comm (a := (1 : ℂ)),
    map_eq_one_iff _ (starRingEnd ℂ).injective]

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under
`s ↦ 1 - conj s`. -/
theorem single_zero_one_add_single_one_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  have e0 : (0 : ℂ) = 1 - s ↔ 1 = s := by rw [eq_comm, sub_eq_zero]
  have e1 : (1 : ℂ) = 1 - s ↔ 0 = s := by rw [eq_comm, sub_eq_self, eq_comm]
  conv_lhs => arg 2; rw [← map_one (starRingEnd ℂ), ← map_sub]
  rw [single_zero_one_add_single_one_one_conj]
  simp only [Finsupp.add_apply, Finsupp.single_apply, e0, e1]
  rw [add_comm]

/-- Construct `HasMeromorphicContinuation` for an `AnalyticLFunctionData` card whose polar divisor
is `Finsupp.single 0 1 + Finsupp.single 1 1` from simple poles at `0` and `1` and analyticity off
`{0, 1}`. -/
theorem hasMeromorphicContinuation_of_polarOrder_eq_single_zero_one_add_single_one_one
    {d : AnalyticLFunctionData}
    (hpol : d.polarOrder = Finsupp.single 0 1 + Finsupp.single 1 1)
    (h0 : meromorphicOrderAt d.completed 0 = (-1 : ℤ))
    (h1 : meromorphicOrderAt d.completed 1 = (-1 : ℤ))
    (ha : ∀ p : ℂ, p ≠ 0 → p ≠ 1 → AnalyticAt ℂ d.completed p) :
    d.HasMeromorphicContinuation :=
  hasMeromorphicContinuation_of_meromorphicOrderAt
    (fun p hp ↦ by
      rw [hpol] at hp ⊢
      rcases eq_or_ne p 0 with rfl | hp0
      · simp [h0]
      rcases eq_or_ne p 1 with rfl | hp1
      · simp [h1]
      · simp [Ne.symm hp0, Ne.symm hp1] at hp)
    fun p hp ↦ by
      rw [hpol] at hp
      exact ha p (by rintro rfl; simp at hp) (by rintro rfl; simp at hp)

end TauCeti.LFunctions.AnalyticLFunctionData
