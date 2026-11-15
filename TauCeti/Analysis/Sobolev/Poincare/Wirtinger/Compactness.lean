/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.MeasureTheory.Function.Lp.Const
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# The Poincaré–Wirtinger inequality from Rellich compactness

Let `Ω` be a preconnected open set of finite measure in a finite-dimensional real inner product
space, and suppose that the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator, as the
Rellich–Kondrachov theorem provides on bounded Lipschitz domains. This file proves that for every
`S ⊆ Ω` of positive measure there is a constant `C` with

`‖u - ⨍_S u‖_{Lᵖ(Ω)} ≤ C * ‖∇u‖_{Lᵖ(Ω)}` for all `u ∈ W^{1,p}(Ω)`.

The constant is not explicit; for convex domains,
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex` gives one in terms of the diameter.

The argument is the classical one by contradiction, packaged as Peetre's compact-error estimate
`ContinuousLinearMap.exists_pos_mul_norm_le_of_compact_estimate`: the Sobolev norm is at most the
`Lᵖ` norm of the gradient plus the norm of the compact value map, so the gradient is bounded below
on every closed subspace that meets its kernel only in `0`. On a preconnected domain this kernel
consists of the constants (`TauCeti.W1p.exists_value_ae_eq_const_of_gradient_eq_zero`), and the
functions with vanishing integral over `S` form such a subspace.

Connectedness cannot be dropped: on a disjoint union of two balls with `S` inside the first, the
function equal to `0` on the first ball and to `1` on the second has vanishing gradient and mean
zero over `S`, but does not vanish.

## Main declarations

* `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator`: the inequality on a
  preconnected domain of finite measure with compact value map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1, Theorem 1.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {S : Set E}

/-- On a preconnected domain, a Sobolev function with vanishing gradient and vanishing integral
over a set of positive measure is zero. -/
private theorem W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero
    (hconn : IsPreconnected (Omega : Set E)) (hS : S ⊆ (Omega : Set E)) (hS0 : mu.real S ≠ 0)
    {u : W1p mu Omega p} (hu : W1p.gradient u = 0) (hint : ∫ y in S, W1p.value u y ∂mu = 0) :
    u = 0 := by
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero hconn hu
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hS hc), setIntegral_const,
    smul_eq_mul] at hint
  have hc0 : c = 0 := (mul_eq_zero.1 hint).resolve_left hS0
  apply W1p.ext_value
  rw [← W1p.valueL_apply, ← W1p.valueL_apply, map_zero]
  apply Lp.ext
  filter_upwards [hc, Lp.coeFn_zero ℝ p (mu.restrict (Omega : Set E))] with x hx h0
  rw [W1p.valueL_apply, hx, hc0, h0, Pi.zero_apply]

/-- **The Poincaré–Wirtinger inequality from compactness.** Let `Ω` be preconnected and of finite
measure, let `S ⊆ Ω` have positive measure, and let `1 ≤ p`. If the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is compact, then the deviation of every `u ∈ W^{1,p}(Ω)` from its mean over
`S` is bounded in `Lᵖ(Ω)` by a constant, independent of `u`, times the `Lᵖ` norm of its weak
gradient. -/
theorem W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := p)))
    (hconn : IsPreconnected (Omega : Set E)) (hfin : mu Omega ≠ ∞)
    (hS : S ⊆ (Omega : Set E)) (hS0 : mu S ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p mu Omega p,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y ∂mu) p (mu.restrict Omega) ≤
        ENNReal.ofReal C * ‖W1p.gradient u‖ₑ := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) := isFiniteMeasure_restrict.2 hfin
  have hSfin : mu.restrict (Omega : Set E) S < ∞ := measure_lt_top _ S
  have hSreal : mu.real S ≠ 0 :=
    (ENNReal.toReal_pos hS0 (ne_top_of_le_ne_top hfin (measure_mono hS))).ne'
  -- The integral over `S`, as a continuous linear functional on `W^{1,p}(Ω)`.
  let ℓ : W1p mu Omega p →L[ℝ] ℝ := (setIntegralLp (𝕜 := ℝ) S hSfin).comp W1p.valueL
  have hℓ (u : W1p mu Omega p) : ℓ u = ∫ y in S, W1p.value u y ∂mu := by
    rw [ContinuousLinearMap.comp_apply, setIntegralLp_apply, W1p.valueL_apply,
      Measure.restrict_restrict_of_subset hS]
  -- Its kernel meets the constants, the kernel of the gradient, only in `0`.
  have hdisj : Disjoint (W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).ker ℓ.ker := by
    rw [Submodule.disjoint_def]
    intro u hgrad hmean
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, W1p.gradientL_apply] at hgrad
    exact W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero hconn hS hSreal hgrad
      ((hℓ u).symm.trans hmean)
  -- Peetre's estimate makes the gradient bounded below on that kernel.
  obtain ⟨c, hc, hcM⟩ :=
    (W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).exists_pos_mul_norm_le_of_compact_estimate
      (C := 1) hK (fun u ↦ by
        rw [one_mul, add_comm, W1p.gradientL_apply, W1p.valueL_apply]
        exact W1p.norm_le_norm_value_add_norm_gradient u)
      ℓ.isClosed_ker hdisj
  refine ⟨c⁻¹, inv_nonneg.2 hc.le, fun u ↦ ?_⟩
  -- Apply the bound to `u` minus its mean over `S`.
  set a := ⨍ y in S, W1p.value u y ∂mu with ha
  set w : W1p mu Omega p := u - W1p.const a with hw
  have hw0 : ℓ w = 0 := by
    have hconst : ℓ (W1p.const a) = mu.real S * a := by
      rw [hℓ, W1p.value_const, ← smul_eq_mul, ← setIntegral_const]
      exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hS (Lp.coeFn_const p _ a))
    rw [hw, map_sub, hconst, hℓ, ha, setAverage_eq, smul_eq_mul, mul_inv_cancel_left₀ hSreal,
      sub_self]
  have hvw : W1p.value w = W1p.value u - Lp.const p (mu.restrict (Omega : Set E)) a := by
    have h := map_sub (W1p.valueL (mu := mu) (Omega := Omega) (p := p)) u (W1p.const a)
    rwa [W1p.valueL_apply, W1p.valueL_apply, W1p.valueL_apply, W1p.value_const, ← hw] at h
  have hgw : W1p.gradient w = W1p.gradient u := by
    rw [hw, W1p.gradient_sub, W1p.gradient_const, sub_zero]
  have hbound : ‖W1p.value w‖ ≤ c⁻¹ * ‖W1p.gradient u‖ := by
    rw [le_inv_mul_iff₀ hc, ← hgw, ← W1p.gradientL_apply]
    exact (mul_le_mul_of_nonneg_left (W1p.norm_value_le w) hc.le).trans
      (hcM w (LinearMap.mem_ker.2 hw0))
  rw [eLpNorm_sub_const_eq_enorm, ← hvw, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
  exact ENNReal.ofReal_le_ofReal hbound

end TauCeti

end
