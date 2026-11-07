/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, OpenAI Codex
-/
module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Liouville's theorem and affine rigidity

An entire function `f` with `f(s) = -g(1 / s) / s²` for `s ≠ 0`, where `g` is continuous at `0`,
vanishes identically (`Differentiable.eq_zero_of_eq_neg_inv_sq_smul`): it tends to `0` at
infinity, so it is zero by Liouville's theorem. This is the transformation law of the coefficient
of a one-form `f(t) dt = g(s) ds` under the change of coordinate `s = 1 / t`, and it shows that a
holomorphic one-form on the Riemann sphere vanishes.

An entire function that is little-o of `z²` is affine, with its value and derivative at zero
as coefficients (`Differentiable.eq_affine_of_isLittleO_sq`). This strict-growth form of
Liouville’s theorem identifies the exponent in an order-one Hadamard factorization.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

open Set Filter Topology

namespace Differentiable

/-- **Liouville's theorem for the transformation law of a one-form under `t ↦ 1 / t`.** If an entire
function `f` satisfies `f(s) = -g(1 / s) / s²` for `s ≠ 0`, with `g` continuous at `0`, then `f`
tends to `0` at infinity, so it vanishes. -/
theorem eq_zero_of_eq_neg_inv_sq_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f g : ℂ → F} (hf : Differentiable ℂ f) (hg : ContinuousAt g 0)
    (h : ∀ s ≠ 0, f s = -(s ^ 2)⁻¹ • g s⁻¹) (t : ℂ) : f t = 0 := by
  have hinv : Tendsto (fun s : ℂ ↦ s⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hlim : Tendsto (fun s : ℂ ↦ -(s⁻¹ ^ 2) • g s⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using (hinv.pow 2).neg.smul (hg.tendsto.comp hinv)
  refine hf.apply_eq_of_tendsto_cocompact t (hlim.congr' ?_)
  filter_upwards [(isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact] with s hs
  rw [h s (mem_compl_singleton_iff.1 hs), inv_pow]

end Differentiable

open Complex Bornology Asymptotics

/-- An entire function that is little-o of the square is affine, with its value and derivative
at zero as coefficients. -/
theorem Differentiable.eq_affine_of_isLittleO_sq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : f =o[cobounded ℂ] (fun z ↦ z ^ 2)) :
    ∀ z, f z = f 0 + _root_.deriv f 0 * z := by
  have hc : (fun _ : ℂ ↦ f 0) =o[cobounded ℂ] (fun z ↦ z ^ 2) :=
    (isBigO_const_one ℂ (f 0) _).trans_isLittleO (by
      simpa only [pow_zero] using
        isLittleO_pow_pow_cobounded_of_lt (R := ℂ) (by norm_num : (0 : ℕ) < 2))
  -- Successive divided differences lower the growth by one power.
  have h1 : _root_.dslope f 0 =o[cobounded ℂ] (fun z ↦ z) := by
    refine ((isBigO_refl (fun z : ℂ ↦ z⁻¹) _).mul_isLittleO (h.sub hc)).congr' ?_ ?_
    all_goals
      filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
      simp [dslope_of_ne f hz, slope_def_field, div_eq_mul_inv, hz, pow_two, mul_comm]
  have hc1 : (fun _ : ℂ ↦ _root_.dslope f 0 0) =o[cobounded ℂ] (fun z ↦ z) :=
    (isBigO_const_one ℂ (_root_.dslope f 0 0) _).trans_isLittleO (by
      simpa only [pow_zero, pow_one] using
        isLittleO_pow_pow_cobounded_of_lt (R := ℂ) (by norm_num : (0 : ℕ) < 1))
  have h2 : _root_.dslope (_root_.dslope f 0) 0 =o[cobounded ℂ] (1 : ℂ → ℂ) := by
    refine ((isBigO_refl (fun z : ℂ ↦ z⁻¹) _).mul_isLittleO (h1.sub hc1)).congr' ?_ ?_
    all_goals
      filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
      simp [dslope_of_ne (_root_.dslope f 0) hz, slope_def_field, div_eq_mul_inv, hz, mul_comm]
  have hg : Differentiable ℂ (_root_.dslope f 0) :=
    fun z ↦ ((hf.analyticAt z).dslope 0).differentiableAt
  have hg2 : Differentiable ℂ (_root_.dslope (_root_.dslope f 0) 0) :=
    fun z ↦ ((hg.analyticAt z).dslope 0).differentiableAt
  have ht : Tendsto (_root_.dslope (_root_.dslope f 0) 0) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact (isLittleO_one_iff ℂ).mp h2
  -- The second divided difference tends to zero and is therefore identically zero.
  have hzero (z : ℂ) := hg2.apply_eq_of_tendsto_cocompact z ht
  intro z
  have hz1 := sub_smul_dslope f 0 z
  have hz2 := sub_smul_dslope (_root_.dslope f 0) 0 z
  rw [hzero z, smul_zero] at hz2
  have hzds : _root_.dslope f 0 z = _root_.deriv f 0 := by
    rw [← dslope_same f 0]
    exact sub_eq_zero.mp hz2.symm
  simp only [sub_zero, smul_eq_mul, hzds] at hz1
  linear_combination -hz1
