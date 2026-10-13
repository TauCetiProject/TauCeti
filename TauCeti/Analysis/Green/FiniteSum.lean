/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.FiniteSum
import TauCeti.Analysis.Green.Main

/-!
# Green's theorem for finite integer-weighted AC families

The field is localized using every trace and the support of the total winding weight.
Only the total index must vanish outside the domain: individual indices may cancel.
Global AC Green for the cutoff field then sums to the total winding-weighted identity.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function

namespace TauCeti.Green

/-- Green's theorem for a finite integer-weighted family of closed AC curves.
The domain condition concerns the total index, permitting cancellation between curves. -/
theorem green_ac_winding_sum {ι : Type*} {s : Finset ι} {γ : ι → ℝ → ℂ}
    {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : ∀ i ∈ s, a i < b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) (hU : IsOpen U)
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hindex : ∀ z ∉ U,
      ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0) :
    (∀ i ∈ s, IntervalIntegrable (circulationFun P Q (γ i)) volume (a i) (b i)) ∧
      IntegrableOn (fun z ↦
        (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P Q z) U ∧
      (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γ i) t) =
        ∫ z in U, (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) *
          curl P Q z := by
  obtain ⟨P', Q', hP', hQ', _, _, _, _, _, _, hw, hbnd, harea⟩ :=
    exists_contDiff_localization_sum hγ hclosed hU htrace hP hQ hindex
  let W : ℂ → ℝ := fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z
  have hgreen (i) (hi : i ∈ s) := green_ac (hab i hi) (hγ i hi) (hclosed i hi) hP' hQ'
  have hint : Integrable (fun z ↦ W z * curl P' Q' z) := by
    have h := integrable_finsetSum s (fun i hi ↦ (hgreen i hi).2.1.const_mul (w i : ℝ))
    convert h using 1
    ext z
    simp only [W, Finset.sum_mul, mul_assoc]
  have hWU := tsupport_sum_windingWeight_subset hγ hclosed htrace hindex
  have hzero (z) (hz : z ∉ U) : W z * curl P' Q' z = 0 := by
    have hzW : W z = 0 := by
      by_contra hn
      exact hz (hWU (subset_tsupport W hn))
    rw [hzW, zero_mul]
  have heq : (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P' Q' (γ i) t) =
      ∫ z in U, W z * curl P' Q' z := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp only [W, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum s (fun i hi ↦ (hgreen i hi).2.1.const_mul (w i : ℝ))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hgreen i hi).2.2, integral_const_mul]
  refine ⟨fun i hi ↦ intervalIntegrable_circulationFun (hγ i hi)
    (hP.continuousOn.mono (htrace i hi)) (hQ.continuousOn.mono (htrace i hi)), ?_, ?_⟩
  · exact (hint.integrableOn (s := U)).congr (Filter.Eventually.of_forall hw)
  · rw [harea] at heq
    convert heq using 1
    exact Finset.sum_congr rfl (fun i hi ↦ congrArg ((w i : ℝ) * ·) (hbnd i hi).symm)

end TauCeti.Green
