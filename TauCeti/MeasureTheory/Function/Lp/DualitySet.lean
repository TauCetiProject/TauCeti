/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.Analysis.Normed.Module.DualitySet
import TauCeti.Analysis.InnerProductSpace.ExtremalRpow
import TauCeti.Analysis.Normed.Module.RCLike.Rpow
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The duality set of a real `Lᵖ` function

For `1 ≤ p < ∞` and a real function `u ∈ Lᵖ(μ)`, the functional

`v ↦ ‖u‖_p ^ (2 - p) ∫ |u| ^ (p - 2) u v dμ`

lies in the duality set `J(u) = {f | f u = ‖u‖², ‖f‖ = ‖u‖}`
(`MeasureTheory.Lp.exists_mem_dualitySet_apply_eq_integral`). Here `|u| ^ (p - 2) u` is read with
the convention `0 ^ s = 0` for `s ≠ 0` of `Real.rpow`, so it vanishes where `u` does; for `p = 1` it
is the sign of `u`, and for `p = 2` it is `u` itself. The functional is the integral pairing with
`w = |u| ^ (p - 2) u`, which lies in the conjugate space `Lᵖ'` with `‖w‖_{p'} ≤ ‖u‖_p ^ (p - 1)`
and satisfies `∫ w u = ‖u‖_p ^ p`.

This is the explicit duality map of `Lᵖ`, through which dissipativity of concrete operators on
`Lᵖ` is verified: an operator `A` is dissipative when `∫ |u| ^ (p - 2) u (A u) ≤ 0` on its domain.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Example II.3.26 (the duality set of an `Lᵖ` function).
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 7, §7.3 (the duality map of `Lᵖ` and the Laplacian).
-/

public section

noncomputable section

open scoped ENNReal

open TauCeti

namespace MeasureTheory.Lp

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The duality set of a real `Lᵖ` function.** For `1 ≤ p < ∞` and `u ∈ Lᵖ(μ)`, some element `f`
of the duality set of `u` is the functional `v ↦ ‖u‖ ^ (2 - p) ∫ |u| ^ (p - 2) u v dμ`. -/
theorem exists_mem_dualitySet_apply_eq_integral (hp : p ≠ ∞) (u : Lp ℝ p μ) :
    ∃ f ∈ dualitySet ℝ u, ∀ v : Lp ℝ p μ,
      f v = ‖u‖ ^ (2 - p.toReal) * ∫ x, |u x| ^ (p.toReal - 2) * u x * v x ∂μ := by
  have hp1 : 1 ≤ p := Fact.out
  have hr1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  -- The conjugate exponent `q`, with `1 / p + 1 / q = 1`.
  set q : ℝ≥0∞ := (1 - p⁻¹)⁻¹ with hq_def
  have : p.HolderConjugate q := by
    rw [ENNReal.holderConjugate_iff, hq_def, inv_inv]
    exact add_tsub_cancel_of_le (ENNReal.inv_le_one.2 hp1)
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  -- `w = |u| ^ (p - 2) u` lies in `L^q`, with `‖w‖_q ≤ ‖u‖_p ^ (p - 1)`.
  have hwq : eLpNorm (fun x ↦ |u x| ^ (p.toReal - 2) * u x) q μ ≤
      eLpNorm u p μ ^ (p.toReal - 1) :=
    eLpNorm_le_eLpNorm_rpow_toReal_sub_one hp
      (((continuous_abs.measurable.pow_const _).mul measurable_id).comp_aemeasurable
        (Lp.aestronglyMeasurable u).aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa using norm_ofReal_rpow_sub_two_smul_le (𝕜 := ℝ) p.toReal (u x))
  have hwmem : MemLp (fun x ↦ |u x| ^ (p.toReal - 2) * u x) q μ :=
    hwq.trans_lt (ENNReal.rpow_lt_top_of_nonneg (by linarith) (Lp.eLpNorm_ne_top u))
  -- The functional `g v = ∫ |u| ^ (p - 2) u v` has norm at most `‖u‖ ^ (p - 1)`, by Hölder.
  let g := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p hwmem.toLp
  have hg (v : Lp ℝ p μ) : g v = ∫ x, |u x| ^ (p.toReal - 2) * u x * v x ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hwmem.coeFn_toLp] with x hx
    simp [hx]
  have hgnorm : ‖g‖ ≤ ‖u‖ ^ (p.toReal - 1) := by
    refine g.opNorm_le_bound (by positivity) fun v ↦ ?_
    have h := TauCeti.enorm_integral_mul_le.trans (mul_le_mul_left hwq (eLpNorm v p μ))
    rw [hg, ← toReal_eNorm, Lp.norm_def, Lp.norm_def, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) (Lp.eLpNorm_ne_top u))
      (Lp.eLpNorm_ne_top v)) h
  refine ⟨‖u‖ ^ (2 - p.toReal) • g, mem_dualitySet_iff_norm_le.2 ⟨?_, ?_⟩, fun v ↦ ?_⟩
  · have hwu : ∫ x, |u x| ^ (p.toReal - 2) * u x * u x ∂μ = ‖u‖ ^ p.toReal := by
      rw [← Lp.integral_norm_rpow_eq_norm_rpow (zero_lt_one.trans_le hp1).ne' hp]
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      simpa [mul_comm] using inner_ofReal_rpow_sub_two_smul (𝕜 := ℝ) (by linarith) (u x)
    rw [smul_apply, hg, hwu, smul_eq_mul, ← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖u‖ ^ (2 - p.toReal) * ‖g‖ ≤ ‖u‖ ^ (2 - p.toReal) * ‖u‖ ^ (p.toReal - 1) := by gcongr
      _ = ‖u‖ := by
        rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]
        norm_num
  · rw [smul_apply, hg, smul_eq_mul]

end MeasureTheory.Lp
