/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Weighted
public import TauCeti.Analysis.Green.FiniteSum
public import TauCeti.Analysis.Green.WindingWeight.Domain

/-!
# Finite winding-weighted Green families as canonical manifold integrals

The actual total winding weight multiplies the actual manifold exterior derivative. Its canonical
oriented integral is the integer-weighted sum of boundary circulations. Only the total index is
required to vanish outside the field domain, so individual contributions can cancel.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- Finite-family AC Green agrees with the actual canonical integral of the total-weighted
manifold exterior derivative, with both integrabilities derived. -/
theorem green_ac_winding_sum_integralTopForm {ι : Type*} {s : Finset ι}
    {γ : ι → ℝ → ℂ} {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : ∀ i ∈ s, a i < b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) (hU : IsOpen U)
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U,
      ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    (∀ i ∈ s, IntervalIntegrable (circulationFun P Q (γ i)) volume (a i) (b i)) ∧
      IntegrableTopForm (I := 𝓘(ℝ, ℂ))
        (fun z ↦ (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) •
            mextDeriv (manifoldOneForm P Q) z) ∧
      (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γ i) t) =
        integralTopForm (Manifold.Orientation.model (I := 𝓘(ℝ, ℂ)) Complex.orientation
          (by simp))
          (fun z ↦ (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) •
              mextDeriv (manifoldOneForm P Q) z) := by
  have hgreen := green_ac_winding_sum hab hγ hclosed hU htrace hP hQ hindex
  have hform := HasCompactSupport.weighted_mextDeriv_integralTopForm
    (hasCompactSupport_sum_windingWeight (w := w) hγ hclosed) hU.measurableSet
    (fun z hz ↦ ((hP z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    (fun z hz ↦ ((hQ z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
    hgreen.2.1
  rw [indicator_sum_windingWeight_eq_self htrace hindex] at hform
  exact ⟨hgreen.1, hform.1, hgreen.2.2.trans hform.2.symm⟩

end TauCeti.Green
