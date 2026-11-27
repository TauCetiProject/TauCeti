/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.IntermediateValue

/-!
# The sharp first derivative test

The first derivative test bounds an oscillatory interval integral by the largest endpoint
value of `|h / φ'|`, divided by `π`, provided this absolute value is monotone. The proof uses
Mathlib's vector-valued second mean value theorem. Continuity ensures that the real ratio
has constant weak sign, so that the theorem applies to its absolute value.

## References

* E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*,
  second edition, Lemma 4.3 (the classical first derivative test).
* J. Arias de Reyna, *On the approximation of the zeta function by Dirichlet polynomials*,
  Lemma 2, for the sharp constant used here.
-/

public section

open Set MeasureTheory

namespace TauCeti

private theorem norm_intervalIntegral_phase_deriv_eq_abs_weight {a b : ℝ}
    {g φ φ' : ℝ → ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hm : MonotoneOn (fun x ↦ |g x|) (Icc a b) ∨
      AntitoneOn (fun x ↦ |g x|) (Icc a b)) :
    ‖∫ x in a..b, g x • (φ' x • (Real.fourierChar (φ x) : ℂ))‖ =
      ‖∫ x in a..b, |g x| • (φ' x • (Real.fourierChar (φ x) : ℂ))‖ := by
  have hs : (∀ x ∈ Icc a b, 0 ≤ g x) ∨ (∀ x ∈ Icc a b, g x ≤ 0) := by
    by_cases hn : ∃ x ∈ Icc a b, g x < 0
    · right
      obtain ⟨x, hx, hnx⟩ := hn
      intro y hy
      by_contra! hpy
      have hs : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
      obtain ⟨z, hz, hgz⟩ := intermediate_value_uIcc (hg.mono hs)
        (show 0 ∈ uIcc (g x) (g y) by
          rw [uIcc_of_le (hnx.le.trans hpy.le)]
          exact ⟨hnx.le, hpy.le⟩)
      have ha : |g z| ∈ uIcc |g x| |g y| := by
        rcases hm with hm | hm
        · exact (hm.mono hs).mapsTo_uIcc hz
        · exact (hm.mono hs).mapsTo_uIcc hz
      have hp : 0 < min |g x| |g y| := lt_min (abs_pos.mpr hnx.ne) (abs_pos.mpr hpy.ne')
      have hal : min |g x| |g y| ≤ |g z| := ha.1
      rw [hgz, abs_zero] at hal
      exact (not_lt_of_ge hal) hp
    · left
      push Not at hn
      exact hn
  rcases hs with hp | hn
  · congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    simp only [abs_of_nonneg (hp x hx)]
  · have heq : (∫ x in a..b, g x • (φ' x • (Real.fourierChar (φ x) : ℂ))) =
        -(∫ x in a..b, |g x| • (φ' x • (Real.fourierChar (φ x) : ℂ))) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      simp [abs_of_nonpos (hn x hx)]
    rw [heq, norm_neg]

private theorem norm_intervalIntegral_phase_deriv_le {a b : ℝ} {φ φ' : ℝ → ℝ}
    (hab : a ≤ b)
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x)
    (hφ' : ContinuousOn φ' (Icc a b)) :
    ‖∫ x in a..b, φ' x • (Real.fourierChar (φ x) : ℂ)‖ ≤ 1 / Real.pi := by
  have hc : ContinuousOn φ (Icc a b) := fun x hx ↦ (hφ x hx).continuousWithinAt
  have he : ContinuousOn (fun x ↦ (Real.fourierChar (φ x) : ℂ)) (Icc a b) :=
    Real.differentiable_fourierChar.continuous.comp_continuousOn hc
  have hd : ∀ x ∈ Ioo a b, HasDerivAt
      (fun x ↦ (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ x))
      (φ' x • (Real.fourierChar (φ x) : ℂ)) x := by
    intro x hx
    have hx' := (hφ x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    convert! ((Real.hasDerivAt_fourierChar (φ x)).scomp x hx').const_mul
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ using 1
    simp only [Complex.real_smul]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_const.mul he) hd ((hφ'.smul he).intervalIntegrable_of_Icc hab)]
  calc
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ b) -
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ a)‖ ≤
        ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ b)‖ +
        ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ a)‖ := norm_sub_le _ _
    _ = 1 / Real.pi := by
      simp [norm_inv, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      field_simp
      ring

/-- The sharp first derivative test: a continuous amplitude-to-phase-derivative ratio whose
absolute value is monotone gives an endpoint bound with constant `1 / π`. -/
theorem norm_intervalIntegral_smul_fourierChar_le
    {a b : ℝ} {φ φ' h : ℝ → ℝ} (hab : a ≤ b)
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x)
    (hφ' : ContinuousOn φ' (Icc a b)) (hne : ∀ x ∈ Icc a b, φ' x ≠ 0)
    (hg : ContinuousOn (fun x ↦ h x / φ' x) (Icc a b))
    (hm : MonotoneOn (fun x ↦ |h x / φ' x|) (Icc a b) ∨
      AntitoneOn (fun x ↦ |h x / φ' x|) (Icc a b)) :
    ‖∫ x in a..b, h x • (Real.fourierChar (φ x) : ℂ)‖ ≤
      max |h a / φ' a| |h b / φ' b| / Real.pi := by
  have hc : ContinuousOn φ (Icc a b) := fun x hx ↦ (hφ x hx).continuousWithinAt
  have hf : ContinuousOn (fun x ↦ φ' x • (Real.fourierChar (φ x) : ℂ)) (Icc a b) :=
    hφ'.smul (Real.differentiable_fourierChar.continuous.comp_continuousOn hc)
  have hi : IntervalIntegrable
      (fun x ↦ φ' x • (Real.fourierChar (φ x) : ℂ)) volume a b :=
    hf.intervalIntegrable_of_Icc hab
  have hbnd : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, c ≤ d →
      ‖∫ x in c..d, φ' x • (Real.fourierChar (φ x) : ℂ)‖ ≤ 1 / Real.pi := by
    intro c hc d hd hcd
    have hs : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
    exact norm_intervalIntegral_phase_deriv_le hcd
      (fun x hx ↦ (hφ x (hs hx)).mono hs) (hφ'.mono hs)
  have heq : (∫ x in a..b, h x • (Real.fourierChar (φ x) : ℂ)) =
      ∫ x in a..b, (h x / φ' x) • (φ' x • (Real.fourierChar (φ x) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    dsimp only
    rw [smul_smul, div_mul_cancel₀ _ (hne x hx)]
  rw [heq, norm_intervalIntegral_phase_deriv_eq_abs_weight hab hg hm]
  rcases hm with hm | hm
  · obtain ⟨ξ, hξ, hle⟩ :=
      exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
        (f := fun x ↦ |h x / φ' x|) hab (abs_nonneg _) hm hi
    calc
      _ ≤ |h b / φ' b| * ‖∫ x in ξ..b, φ' x • (Real.fourierChar (φ x) : ℂ)‖ := hle
      _ ≤ |h b / φ' b| * (1 / Real.pi) := mul_le_mul_of_nonneg_left
        (hbnd ξ hξ b (right_mem_Icc.mpr hab) hξ.2) (abs_nonneg _)
      _ ≤ max |h a / φ' a| |h b / φ' b| / Real.pi := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
          (le_max_right |h a / φ' a| |h b / φ' b|) (inv_nonneg.mpr Real.pi_pos.le)
  · obtain ⟨ξ, hξ, hle⟩ :=
      exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
        (f := fun x ↦ |h x / φ' x|) hab (abs_nonneg _) hm hi
    calc
      _ ≤ |h a / φ' a| * ‖∫ x in a..ξ, φ' x • (Real.fourierChar (φ x) : ℂ)‖ := hle
      _ ≤ |h a / φ' a| * (1 / Real.pi) := mul_le_mul_of_nonneg_left
        (hbnd a (left_mem_Icc.mpr hab) ξ hξ hξ.1) (abs_nonneg _)
      _ ≤ max |h a / φ' a| |h b / φ' b| / Real.pi := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
          (le_max_left |h a / φ' a| |h b / φ' b|) (inv_nonneg.mpr Real.pi_pos.le)

/-- The first derivative test with non-increasing absolute amplitude-to-derivative ratio:
only the initial endpoint is needed. -/
theorem norm_intervalIntegral_smul_fourierChar_le_of_antitoneOn_abs_div
    {a b : ℝ} {φ φ' h : ℝ → ℝ} (hab : a ≤ b)
    (hφ : ∀ x ∈ Icc a b, HasDerivWithinAt φ (φ' x) (Icc a b) x)
    (hφ' : ContinuousOn φ' (Icc a b)) (hne : ∀ x ∈ Icc a b, φ' x ≠ 0)
    (hg : ContinuousOn (fun x ↦ h x / φ' x) (Icc a b))
    (hm : AntitoneOn (fun x ↦ |h x / φ' x|) (Icc a b)) :
    ‖∫ x in a..b, h x • (Real.fourierChar (φ x) : ℂ)‖ ≤ |h a / φ' a| / Real.pi := by
  have h := norm_intervalIntegral_smul_fourierChar_le
    hab hφ hφ' hne hg (Or.inr hm)
  rwa [max_eq_left (hm (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab)] at h

end TauCeti
