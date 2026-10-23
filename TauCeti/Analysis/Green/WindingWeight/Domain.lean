/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.Basic
import Mathlib.Basic.Complex.BigOperators

/-!
# Winding weights on a field domain

Vanishing of the index outside a domain implies that restricting a single winding weight
leaves it unchanged. For finite families, trace containment also ensures that zeroing weights
on individual traces does not disturb cancellation of the total index outside the domain.
-/

public section

open Set

namespace TauCeti.Green

/-- A winding weight agrees with its restriction to a domain outside which the index vanishes.
No trace containment or regularity of the curve is required. -/
theorem indicator_windingWeight_eq_self {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) :
    U.indicator (windingWeight γ a b) = windingWeight γ a b := by
  ext z
  by_cases hz : z ∈ U
  · exact indicator_of_mem hz _
  · rw [indicator_of_notMem hz]
    symm
    by_cases ht : z ∈ γ '' uIcc a b
    · exact windingWeight_eq_zero_of_mem ht
    · rw [windingWeight_eq_of_notMem ht, hindex z hz, Complex.zero_re]

/-- A total winding weight agrees with its restriction to the field domain under a condition
on the total index, without requiring each individual index to vanish. -/
theorem indicator_sum_windingWeight_eq_self {ι : Type*} {s : Finset ι}
    {γ : ι → ℝ → ℂ} {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ}
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hindex : ∀ z ∉ U,
      ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    U.indicator (fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) =
      fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z := by
  ext z
  by_cases hz : z ∈ U
  · exact indicator_of_mem hz _
  · rw [indicator_of_notMem hz]
    have h := congrArg Complex.re (hindex z hz)
    simp only [Complex.re_sum, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      zero_mul, sub_zero, Complex.zero_re] at h
    refine h.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i hi
    rw [windingWeight_eq_of_notMem (fun ht ↦ hz (htrace i hi ht))]

end TauCeti.Green
