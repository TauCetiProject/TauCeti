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
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Topology.Order.IntermediateValue

/-!
# The sharp first derivative test

The first derivative test bounds an oscillatory interval integral by the largest endpoint
value of `|h / φ'|`, divided by `π`, provided this absolute value is monotone. The proof uses
Mathlib's vector-valued second mean value theorem. Continuity ensures that the real ratio
has constant weak sign, so that the theorem applies to its absolute value.

## Main results

* `TauCeti.norm_intervalIntegral_deriv_smul_fourierChar_le`: the Fourier primitive bound, with
  constant `1 / π`, for either orientation and without continuity or integrability of
  the derivative.
* `TauCeti.norm_intervalIntegral_smul_fourierChar_le`: the sharp first derivative test for a
  monotone absolute amplitude-to-derivative ratio.
* `TauCeti.norm_intervalIntegral_smul_fourierChar_le_of_antitoneOn_abs_div`: the initial-endpoint
  bound for an antitone absolute ratio.

## References

* E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*,
  second edition, Lemma 4.3 (the classical first derivative test).
* J. Arias de Reyna, *On the approximation of the zeta function by Dirichlet polynomials*,
  Lemma 2, for the sharp constant used here.
-/

public section

open Set MeasureTheory

namespace TauCeti

/-- The Fourier primitive bound: the integral of a phase derivative times its Fourier
character has norm at most `1 / π`. Continuity of the phase on the closed interval and
its derivative on the open interval suffice; the derivative need not be continuous or integrable. -/
theorem norm_intervalIntegral_deriv_smul_fourierChar_le {a b : ℝ} {φ φ' : ℝ → ℝ}
    (hφ : ContinuousOn φ (uIcc a b))
    (hφ' : ∀ x ∈ uIoo a b, HasDerivAt φ (φ' x) x) :
    ‖∫ x in a..b, φ' x • (Real.fourierChar (φ x) : ℂ)‖ ≤ 1 / Real.pi := by
  by_cases hi : IntervalIntegrable
      (fun x ↦ φ' x • (Real.fourierChar (φ x) : ℂ)) volume a b
  · have he : ContinuousOn (fun x ↦ (Real.fourierChar (φ x) : ℂ)) (uIcc a b) :=
      Real.differentiable_fourierChar.continuous.comp_continuousOn hφ
    have hd : ∀ x ∈ uIoo a b, HasDerivAt
        (fun x ↦ (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ x))
        (φ' x • (Real.fourierChar (φ x) : ℂ)) x := by
      intro x hx
      convert! ((Real.hasDerivAt_fourierChar (φ x)).scomp x (hφ' x hx)).const_mul
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ using 1
      simp only [Complex.real_smul]
      field_simp
    rw [_root_.intervalIntegral.integral_eq_sub_of_hasDeriv_right
      (continuousOn_const.mul he) (fun x hx ↦ (hd x hx).hasDerivWithinAt) hi]
    calc
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ b) -
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ a)‖ ≤
          ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ b)‖ +
          ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ * Real.fourierChar (φ a)‖ := norm_sub_le _ _
      _ = 1 / Real.pi := by
        simp only [norm_mul, norm_inv, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, Circle.norm_coe, mul_one]
        field_simp
        ring
  · rw [_root_.intervalIntegral.integral_undef hi, norm_zero]
    exact one_div_nonneg.mpr Real.pi_pos.le

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
  have hφc : ContinuousOn φ (Icc a b) := fun x hx ↦ (hφ x hx).continuousWithinAt
  have hf : ContinuousOn (fun x ↦ φ' x • (Real.fourierChar (φ x) : ℂ)) (Icc a b) :=
    hφ'.smul (Real.differentiable_fourierChar.continuous.comp_continuousOn hφc)
  have hi := hf.intervalIntegrable_of_Icc (μ := volume) hab
  have hbnd : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, c ≤ d →
      ‖∫ x in c..d, φ' x • (Real.fourierChar (φ x) : ℂ)‖ ≤ 1 / Real.pi := by
    intro c hc d hd hcd
    have hs : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
    refine norm_intervalIntegral_deriv_smul_fourierChar_le ((uIcc_of_le hcd).symm ▸ hφc.mono hs) ?_
    intro x hx
    rw [uIoo_of_le hcd] at hx
    exact ((hφ x (hs (Ioo_subset_Icc_self hx))).mono hs).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)
  have heq : (∫ x in a..b, h x • (Real.fourierChar (φ x) : ℂ)) =
      ∫ x in a..b, (h x / φ' x) • (φ' x • (Real.fourierChar (φ x) : ℂ)) := by
    apply _root_.intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    dsimp only
    rw [smul_smul, div_mul_cancel₀ _ (hne x hx)]
  have hsign := hm.elim
    (hg.nonneg_or_nonpos_of_monotoneOn_abs isPreconnected_Icc)
    (hg.nonneg_or_nonpos_of_antitoneOn_abs isPreconnected_Icc)
  have hmem : ∀ᵐ x ∂volume.restrict (uIoc a b), x ∈ Icc a b :=
    ae_restrict_of_forall_mem measurableSet_uIoc
      (uIoc_subset_uIcc.trans (uIcc_of_le hab).subset)
  rw [heq, intervalIntegral.norm_integral_smul_eq_norm_integral_abs_smul _
    (hsign.imp hmem.mono hmem.mono)]
  rcases hm with hm | hm
  · obtain ⟨ξ, hξ, hle⟩ :=
      exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_monotoneOn
        (f := fun x ↦ |h x / φ' x|) hab (abs_nonneg _) hm hi
    calc
      _ ≤ |h b / φ' b| * ‖∫ x in ξ..b, φ' x • (Real.fourierChar (φ x) : ℂ)‖ := hle
      _ ≤ max |h a / φ' a| |h b / φ' b| / Real.pi := by
        rw [← mul_one_div (max |h a / φ' a| |h b / φ' b|) Real.pi]
        gcongr
        · exact le_max_right _ _
        · exact hbnd ξ hξ b (right_mem_Icc.mpr hab) hξ.2
  · obtain ⟨ξ, hξ, hle⟩ :=
      exists_le_const_mul_norm_intervalIntegral_of_nonneg_of_antitoneOn
        (f := fun x ↦ |h x / φ' x|) hab (abs_nonneg _) hm hi
    calc
      _ ≤ |h a / φ' a| * ‖∫ x in a..ξ, φ' x • (Real.fourierChar (φ x) : ℂ)‖ := hle
      _ ≤ max |h a / φ' a| |h b / φ' b| / Real.pi := by
        rw [← mul_one_div (max |h a / φ' a| |h b / φ' b|) Real.pi]
        gcongr
        · exact le_max_left _ _
        · exact hbnd a (left_mem_Icc.mpr hab) ξ hξ hξ.1

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
