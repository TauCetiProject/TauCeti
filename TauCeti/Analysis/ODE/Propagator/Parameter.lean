/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator

/-!
# Propagators of coefficients depending on a parameter

Let `P : ℂ → ℝ → E →L[ℂ] E` be a family of integrable coefficients depending on a complex
parameter `z`. This file records the parts of the holomorphic dependence of the propagator
`N_{P z}(t, s)` on `z` that only use the propagator itself.

* A domination `‖P z r‖ ≤ m r` on the interval between `s` and `t` bounds the propagator by
  `exp |∫ r in s..t, m r|`, uniformly in the parameter (`TauCeti.norm_propagator_le_of_norm_le`).
  With `m = m_K` dominating the family for `z` in a compact set `K`, this is the uniform bound of
  the holomorphic dependence theorem.
* For `P z = z • A` the propagator is `exp ((t - s) z A)`, an entire function of `z`
  (`TauCeti.differentiable_propagator_smul_const`).
* The domination hypothesis is needed: for the scalar coefficient `P z r = (z - r)⁻¹` the
  propagator from `0` is `N(t, 0) = z / (z - t)` whenever `z` avoids the real segment between `0`
  and `t` (`TauCeti.propagator_inv_sub`), which has a pole at `z = t`.

## References

* E. A. Coddington, N. Levinson, *Theory of Ordinary Differential Equations*, Chapter 1, §7.
-/

public section

open MeasureTheory Set intervalIntegral Real
open scoped Interval

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  {P : ℝ → E →L[𝕜] E} {m : ℝ → ℝ} {s t : ℝ}

/-- **The norm bound under a domination.** If `P` and `m` are integrable between `s` and `t` and
`‖P r‖ ≤ m r` for almost every `r` there, then `‖N_P(t, s)‖ ≤ exp |∫ r in s..t, m r|`. Applied
to a family of coefficients dominated by one function `m_K` for all parameters in a set `K`, the
bound is uniform in the parameter. -/
theorem norm_propagator_le_of_norm_le [CompleteSpace E] (hP : IntervalIntegrable P volume s t)
    (hm : IntervalIntegrable m volume s t) (hPm : ∀ᵐ r, r ∈ Ι s t → ‖P r‖ ≤ m r) :
    ‖propagator P t s‖ ≤ exp |∫ r in s..t, m r| := by
  have hP' : IntegrableOn P (Icc (min s t) (max s t)) :=
    Iff.mpr integrableOn_Icc_iff_integrableOn_Ioc hP.def'
  refine (norm_propagator_le hP'
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩).trans
    (exp_le_exp.2 ?_)
  have hPi : IntervalIntegrable (fun r ↦ ‖P r‖) volume s t := hP.norm
  rw [abs_integral_eq_abs_integral_uIoc, abs_integral_eq_abs_integral_uIoc,
    abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  refine (MeasureTheory.integral_mono_ae hPi.def' hm.def' ?_).trans (le_abs_self _)
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  exact hPm

/-! ### Checks -/

section Checks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Constant coefficients depending linearly on the parameter.** For `P z = z • A`,
`N_{P z}(t, s) = exp ((t - s) z A)`. -/
theorem propagator_smul_const (A : E →L[ℂ] E) (z : ℂ) (t s : ℝ) :
    propagator (fun _ ↦ z • A) t s = NormedSpace.exp ((((t - s : ℝ) : ℂ) * z) • A) := by
  rw [propagator_const, smul_smul]
  rfl

/-- For `P z = z • A` the propagator `N_{P z}(t, s)` is an entire function of `z`. -/
theorem differentiable_propagator_smul_const (A : E →L[ℂ] E) (t s : ℝ) :
    Differentiable ℂ fun z : ℂ ↦ propagator (fun _ ↦ z • A) t s := by
  simp_rw [propagator_smul_const]
  exact (differentiable_exp_smul_const ℂ A).comp
    ((differentiable_const _).mul differentiable_id)

/-- **The domination hypothesis is needed.** For the scalar coefficient `P z r = (z - r)⁻¹` on
`ℂ`, if `z` avoids the real segment between `0` and `t` then `N_{P z}(t, 0) = z / (z - t)`. As a
function of `z` this has a pole at `z = t`; the coefficients are dominated by an integrable
function uniformly on compact sets of parameters only away from the segment. -/
theorem propagator_inv_sub {z : ℂ} {t : ℝ} (hz : ∀ r ∈ uIcc 0 t, z ≠ r) :
    propagator (fun r : ℝ ↦ (z - r)⁻¹ • (1 : ℂ →L[ℂ] ℂ)) t 0 = (z / (z - t)) • 1 := by
  have hne (r : ℝ) (hr : r ∈ uIcc 0 t) : z - r ≠ 0 := sub_ne_zero.2 (hz r hr)
  have hcont : ContinuousOn (fun r : ℝ ↦ (z - r)⁻¹ • (1 : ℂ →L[ℂ] ℂ)) (uIcc 0 t) :=
    ((continuousOn_const.sub Complex.continuous_ofReal.continuousOn).inv₀ hne).smul
      continuousOn_const
  have hz0 : z ≠ 0 := by simpa using hz 0 left_mem_uIcc
  refine propagator_eq_of_hasDerivAt (X := fun r : ℝ ↦ (z / (z - r)) • (1 : ℂ →L[ℂ] ℂ))
    hcont.integrableOn_Icc left_mem_uIcc right_mem_uIcc (fun r hr ↦ ?_) (by simp [hz0])
  have hd : HasDerivAt (fun r : ℝ ↦ z / (z - r)) (z / (z - r) ^ 2) r := by
    have h := ((hasDerivAt_const r z).sub (Complex.ofRealCLM.hasDerivAt (x := r))).inv
      (hne r hr)
    convert h.const_mul z using 1
    · ext u
      simp [div_eq_mul_inv]
    · simp [div_eq_mul_inv]
  convert hd.smul_const (1 : ℂ →L[ℂ] ℂ) using 1
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    smul_smul]
  congr 1
  field_simp [hne r hr]

end Checks

end TauCeti
