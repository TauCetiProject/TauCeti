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
  simp only [Finsupp.add_apply]
  have h0 := Finsupp.single_apply_left (starRingEnd ℂ).injective (0 : ℂ) s (1 : ℕ)
  have h1 := Finsupp.single_apply_left (starRingEnd ℂ).injective (1 : ℂ) s (1 : ℕ)
  simp only [map_zero, map_one] at h0 h1
  rw [h0, h1]

/-- The simple-pole divisor `Finsupp.single 0 1 + Finsupp.single 1 1` is invariant under
`s ↦ 1 - conj s`. -/
theorem single_zero_one_add_single_one_one_one_sub_conj (s : ℂ) :
    (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) (1 - conj s) =
      (Finsupp.single (0 : ℂ) (1 : ℕ) + Finsupp.single 1 1 : ℂ →₀ ℕ) s := by
  simp only [Finsupp.add_apply]
  have hinj : Function.Injective (fun z : ℂ ↦ 1 - conj z) :=
    fun x y h ↦ (starRingEnd ℂ).injective (sub_right_injective h)
  have h0 := Finsupp.single_apply_left hinj (1 : ℂ) s (1 : ℕ)
  have h1 := Finsupp.single_apply_left hinj (0 : ℂ) s (1 : ℕ)
  simp only [map_one, sub_self, map_zero, sub_zero] at h0 h1
  rw [h0, h1, add_comm]

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
