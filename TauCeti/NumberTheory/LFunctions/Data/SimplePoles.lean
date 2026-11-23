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

* `TauCeti.LFunctions.single_zero_one_add_single_one_one_conj`: invariance of
  `Finsupp.single 0 1 + Finsupp.single 1 1` under `conj`.
* `TauCeti.LFunctions.single_zero_one_add_single_one_one_one_sub_conj`: invariance of
  `Finsupp.single 0 1 + Finsupp.single 1 1` under `s ↦ 1 - conj s`.
* `hasMeromorphicContinuation_of_polarOrder_eq_single_add_single`:
  shared `HasMeromorphicContinuation` constructor in `AnalyticLFunctionData` for cards with simple
  poles at two distinct points `a` and `b`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

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

namespace AnalyticLFunctionData

/-- Construct `HasMeromorphicContinuation` for an `AnalyticLFunctionData` card whose polar divisor
is `Finsupp.single a 1 + Finsupp.single b 1` for distinct `a ≠ b`, from simple poles at `a` and `b`
and analyticity off `{a, b}`. -/
theorem hasMeromorphicContinuation_of_polarOrder_eq_single_add_single
    {d : AnalyticLFunctionData} {a b : ℂ} (hab : a ≠ b)
    (hpol : d.polarOrder = Finsupp.single a 1 + Finsupp.single b 1)
    (ha : meromorphicOrderAt d.completed a = (-1 : ℤ))
    (hb : meromorphicOrderAt d.completed b = (-1 : ℤ))
    (han : ∀ p : ℂ, p ≠ a → p ≠ b → AnalyticAt ℂ d.completed p) :
    d.HasMeromorphicContinuation :=
  hasMeromorphicContinuation_of_meromorphicOrderAt
    (fun p hp ↦ by
      rw [hpol] at hp ⊢
      rcases eq_or_ne p a with rfl | hpa
      · simp [hab, ha]
      rcases eq_or_ne p b with rfl | hpb
      · simp [hab.symm, hb]
      · simp [Ne.symm hpa, Ne.symm hpb] at hp)
    fun p hp ↦ by
      rw [hpol] at hp
      exact han p (by rintro rfl; simp at hp) (by rintro rfl; simp at hp)

end AnalyticLFunctionData

end TauCeti.LFunctions
