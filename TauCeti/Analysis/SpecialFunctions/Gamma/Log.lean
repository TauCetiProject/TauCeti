/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.ContinuousLog.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# The normalized holomorphic logarithm of Gamma

`TauCeti.logGamma` is the holomorphic logarithm of `Complex.Gamma` on the slit plane
`ℂ ∖ (-∞, 0]`, normalized to vanish at `2`. It agrees with the real logarithm of Gamma on the
positive real axis. In particular, its value at `3` is `Real.log 2`, and its real part is
`Real.log ‖Complex.Gamma z‖`.

The branch is constructed once on the whole slit plane, using
`TauCeti.exists_differentiableOn_eqOn_exp_comp`; its restrictions to sectors therefore agree
without further choices. The sector holomorphy theorem supplies the domains used in uniform
Stirling estimates. This file makes no asymptotic assertion.
-/

public section

namespace TauCeti

open Complex Set

private theorem exists_normalized_logGamma :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L slitPlane ∧
      EqOn (Complex.exp ∘ L) Complex.Gamma slitPlane ∧ L 2 = 0 := by
  have hpole {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) : z ≠ -(n : ℂ) := by
    rintro rfl
    have hneg := (Complex.neg_ofReal_mem_slitPlane (x := (n : ℝ))).mp hz
    exact (Nat.cast_nonneg n).not_gt hneg
  have hsc : IsSimplyConnected slitPlane := by
    let : ContractibleSpace slitPlane :=
      starConvex_one_slitPlane.contractibleSpace ⟨1, one_mem_slitPlane⟩
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hL, he⟩ := exists_differentiableOn_eqOn_exp_comp hsc isOpen_slitPlane
    (fun z hz => (Complex.differentiableAt_Gamma z
      (hpole hz)).differentiableWithinAt)
    (by rintro ⟨z, hz, hzero⟩
        exact Complex.Gamma_ne_zero (hpole hz) hzero)
  have htwo : Complex.exp (L 2) = 1 := by
    simpa using (he (ofNat_mem_slitPlane 2))
  refine ⟨fun z => L z - L 2, hL.sub_const _, fun z hz => ?_, sub_self _⟩
  simpa [Complex.exp_sub, htwo] using he hz

/-- The holomorphic logarithm of Gamma on the slit plane, normalized by `logGamma 2 = 0`.
Outside the slit plane its values are unspecified. -/
noncomputable def logGamma : ℂ → ℂ := Classical.choose exists_normalized_logGamma

/-- The normalized logarithm of Gamma is holomorphic on the whole slit plane. -/
theorem differentiableOn_logGamma : DifferentiableOn ℂ logGamma slitPlane :=
  (Classical.choose_spec exists_normalized_logGamma).1

/-- Exponentiating the normalized logarithm recovers Gamma. -/
@[simp]
theorem exp_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    Complex.exp (logGamma z) = Complex.Gamma z :=
  (Classical.choose_spec exists_normalized_logGamma).2.1 hz

/-- The normalization of the logarithm of Gamma. -/
@[simp]
theorem logGamma_two : logGamma 2 = 0 :=
  (Classical.choose_spec exists_normalized_logGamma).2.2

/-- The normalized logarithm of Gamma is analytic at every point of the slit plane. -/
theorem analyticOnNhd_logGamma : AnalyticOnNhd ℂ logGamma slitPlane :=
  differentiableOn_logGamma.analyticOnNhd isOpen_slitPlane

/-- A holomorphic logarithm of Gamma on the slit plane vanishing at `2` is the chosen branch. -/
theorem eqOn_logGamma {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L slitPlane)
    (he : ∀ z ∈ slitPlane, Complex.exp (L z) = Complex.Gamma z) (h2 : L 2 = 0) :
    EqOn L logGamma slitPlane := by
  exact eqOn_of_eqOn_exp_comp isOpen_slitPlane
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    hL differentiableOn_logGamma (fun z hz => he z hz) (fun _ hz => exp_logGamma hz)
    (ofNat_mem_slitPlane 2) (h2.trans logGamma_two.symm)

/-- The real part of any value of the branch is the logarithm of the Gamma norm. -/
theorem logGamma_re {z : ℂ} (hz : z ∈ slitPlane) :
    (logGamma z).re = Real.log ‖Complex.Gamma z‖ := by
  rw [← exp_logGamma hz, Complex.norm_exp, Real.log_exp]

/-- On the positive real axis the holomorphic branch agrees with the real logarithm of Gamma. -/
@[simp]
theorem logGamma_ofReal {x : ℝ} (hx : 0 < x) :
    logGamma x = (Real.log (Real.Gamma x) : ℂ) := by
  let d : ℝ → ℂ := fun t => logGamma t - (Real.log (Real.Gamma t) : ℂ)
  have hc : ContinuousOn d (Ioi 0) := by
    exact (differentiableOn_logGamma.continuousOn.comp continuous_ofReal.continuousOn
      (fun t ht => ofReal_mem_slitPlane.mpr ht)).sub
      (continuous_ofReal.comp_continuousOn
        (Real.differentiableOn_Gamma_Ioi.continuousOn.log
          (fun t ht => (Real.Gamma_pos_of_pos ht).ne')))
  have he : ∀ t ∈ Ioi (0 : ℝ), Complex.exp (d t) = 1 := by
    intro t ht
    simp only [d, Complex.exp_sub, exp_logGamma (ofReal_mem_slitPlane.mpr ht),
      Complex.Gamma_ofReal, ← Complex.ofReal_exp,
      Real.exp_log (Real.Gamma_pos_of_pos ht), div_self (ofReal_ne_zero.mpr
        (Real.Gamma_pos_of_pos ht).ne')]
  have hd : d x = d 2 :=
    eq_of_isPreconnected_of_forall_exp_eq_one (isPreconnected_Ioi.image d hc)
      (by rintro _ ⟨t, ht, rfl⟩; exact he t ht) ⟨x, hx, rfl⟩ ⟨2, by norm_num, rfl⟩
  have hd2 : d 2 = 0 := by simp [d]
  exact sub_eq_zero.mp (hd.trans hd2)

/-- At `3` the normalized branch takes the value `log 2`. -/
@[simp]
theorem logGamma_three : logGamma 3 = (Real.log 2 : ℂ) := by
  simpa using logGamma_ofReal (x := 3) (by norm_num)

/-- The derivative of the normalized branch is the digamma function. -/
theorem deriv_logGamma {z : ℂ} (hz : z ∈ slitPlane) :
    deriv logGamma z = Complex.digamma z := by
  exact deriv_eq_logDeriv_of_eqOn_exp_comp isOpen_slitPlane differentiableOn_logGamma
    (fun _ hw => exp_logGamma hw) hz

/-- Holomorphy on every sector avoiding the negative real axis. All these sectors use the same
branch, so their restrictions agree on every overlap. -/
theorem differentiableOn_logGamma_sector {δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ logGamma {z : ℂ | |z.arg| < Real.pi - δ ∧ 1 < ‖z‖} := by
  refine differentiableOn_logGamma.mono fun z hz => mem_slitPlane_iff_arg.mpr ⟨?_, ?_⟩
  · have harg : z.arg < Real.pi := lt_of_le_of_lt (le_abs_self _) (by linarith [hz.1])
    exact ne_of_lt harg
  · rintro rfl
    norm_num at hz

end TauCeti
