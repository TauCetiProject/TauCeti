/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.WindingWeight.FiniteSum
public import TauCeti.Analysis.Green.Basic
import TauCeti.Analysis.Green.Approximation.FiniteSum
import TauCeti.Analysis.Green.Polygonal.Green
import TauCeti.Analysis.Green.Limit
import TauCeti.Analysis.Green.Localization

/-!
# Green's theorem for finite integer-weighted AC families

The field is localized using every trace and the support of the total winding weight.
Only the total index must vanish outside the domain: individual indices may cancel.
Simultaneous polygonal approximation preserves the total index outside the domain. The actual
polygonal identities pass to the family through boundary and total-weight `L¹` convergence.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function

namespace TauCeti.Green

/-- For globally `C¹` compactly supported fields, the total winding-weighted curl of a finite
integer-weighted family of closed AC curves is integrable over the plane, and the weighted
circulation equals its integral over `U`. -/
private theorem green_ac_winding_sum_of_hasCompactSupport {ι : Type*} {s : Finset ι}
    {γ : ι → ℝ → ℂ} {a b : ι → ℝ} {w : ι → ℤ} {U : Set ℂ} {P Q : ℂ → ℝ}
    (hab : ∀ i ∈ s, a i < b i)
    (hγ : ∀ i ∈ s, AbsolutelyContinuousOnInterval (γ i) (a i) (b i))
    (hclosed : ∀ i ∈ s, γ i (a i) = γ i (b i)) (hU : IsOpen U)
    (htrace : ∀ i ∈ s, γ i '' uIcc (a i) (b i) ⊆ U)
    (hindex : ∀ z ∉ U,
      ∑ i ∈ s, (w i : ℂ) * Contour.windingNumber (γ i) (a i) (b i) z = 0)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) (hcP : HasCompactSupport P)
    (hcQ : HasCompactSupport Q) :
    Integrable (fun z ↦
        (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P Q z) ∧
      (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γ i) t) =
        ∫ z in U, (∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z) * curl P Q z := by
  let W : ℂ → ℝ := fun z ↦ ∑ i ∈ s, (w i : ℝ) * windingWeight (γ i) (a i) (b i) z
  obtain ⟨γn, hn, hu, hd, hwconv, hdomain⟩ :=
    exists_polygonal_approximation_winding_sum hab hγ hclosed hU htrace hindex
  let Wn : ℕ → ℂ → ℝ := fun n z ↦
    ∑ i ∈ s, (w i : ℝ) * windingWeight (γn n i) (a i) (b i) z
  have hAC (n) (i) (hi : i ∈ s) := (hn n i hi).2.1
  have hcl (n) (i) (hi : i ∈ s) := (hn n i hi).2.2.2.2
  have hW : Integrable W := integrable_sum_windingWeight hγ hclosed
  have hWn (n) : Integrable (Wn n) :=
    integrable_sum_windingWeight (hAC n) (hcl n)
  obtain ⟨C, hC⟩ := (HasCompactSupport.curl hcP hcQ).exists_bound_of_continuous
    (ContDiff.continuous_curl hP hQ)
  have hint : Integrable (fun z ↦ W z * curl P Q z) :=
    hW.mul_bdd (ContDiff.continuous_curl hP hQ).aestronglyMeasurable (Eventually.of_forall hC)
  have hbconv : Tendsto
      (fun n ↦ ∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γn n i) t)
      atTop (nhds (∑ i ∈ s, (w i : ℝ) *
        ∫ t in a i..b i, circulationFun P Q (γ i) t)) :=
    tendsto_finsetSum s (fun i hi ↦ tendsto_const_nhds.mul
      ((hγ i hi).tendsto_integral_circulationFun (fun n ↦ hAC n i hi) (hab i hi).le
        hP.continuous hQ.continuous hcP hcQ
        (hu i hi) (hd i hi)))
  have haconv := tendsto_integral_mul_of_integral_abs_sub hWn hW
    (ContDiff.continuous_curl hP hQ).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using Eventually.of_forall hC) hwconv
  have hzero (z) (hz : z ∉ U) : W z * curl P Q z = 0 :=
    sum_windingWeight_mul_eq_zero_of_notMem htrace hindex _ hz
  refine ⟨hint, ?_⟩
  have heq : (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γ i) t) =
      ∫ z in U, W z * curl P Q z := by
    have hzero_n : ∀ᶠ n in atTop, ∀ z ∉ U, Wn n z * curl P Q z = 0 := by
      filter_upwards [hdomain] with n hdom z hz
      exact sum_windingWeight_mul_eq_zero_of_notMem hdom.1 hdom.2 _ hz
    have harea_n : ∀ᶠ n in atTop, (∫ z : ℂ, Wn n z * curl P Q z) =
        ∫ z in U, Wn n z * curl P Q z := hzero_n.mono (fun _ hz ↦
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm)
    have hgreen_n : ∀ᶠ n in atTop,
        (∑ i ∈ s, (w i : ℝ) * ∫ t in a i..b i, circulationFun P Q (γn n i) t) =
          ∫ z in U, Wn n z * curl P Q z := by
      filter_upwards [harea_n] with n hm
      exact (green_polygonal_sum (fun i hi ↦ (hn n i hi).1) (hcl n) hP hQ).trans hm
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at haconv
    exact tendsto_nhds_unique
      (hbconv.congr' hgreen_n)
      (haconv.congr' harea_n)
  exact heq

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
  obtain ⟨P', Q', hP', hQ', hcP, hcQ, _, _, _, _, hw, hbnd, harea⟩ :=
    exists_contDiff_localization_sum hγ hclosed hU htrace hP hQ hindex
  obtain ⟨hint, heq⟩ := green_ac_winding_sum_of_hasCompactSupport hab hγ hclosed hU htrace hindex
    hP' hQ' hcP hcQ
  refine ⟨fun i hi ↦ AbsolutelyContinuousOnInterval.intervalIntegrable_circulationFun (hγ i hi)
    (hP.continuousOn.mono (htrace i hi)) (hQ.continuousOn.mono (htrace i hi)), ?_, ?_⟩
  · exact (hint.integrableOn (s := U)).congr (Filter.Eventually.of_forall hw)
  · rw [harea] at heq
    convert heq using 1
    exact Finset.sum_congr rfl (fun i hi ↦ congrArg ((w i : ℝ) * ·) (hbnd i hi).symm)

end TauCeti.Green
