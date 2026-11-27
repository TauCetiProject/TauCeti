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

* `TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_isCompactOperator`: with compact value
  map, `‖u‖_{Lᵖ(Ω)} ≤ C ‖∇u‖_{Lᵖ(Ω)}` on every closed subspace meeting the kernel of the gradient
  only in `0`.
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

/-- **A Poincaré inequality on a closed subspace, from compactness.** If the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is compact and `V` is a closed subspace of `W^{1,p}(Ω)` whose only element
with vanishing gradient is `0`, then there is a constant `C` with
`‖u‖_{Lᵖ(Ω)} ≤ C * ‖∇u‖_{Lᵖ(Ω)}` for every `u ∈ V`. This is Peetre's compact-error estimate,
since the Sobolev norm is at most the norm of the gradient plus the norm of the value. -/
theorem W1p.exists_norm_value_le_mul_norm_gradient_of_isCompactOperator
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := p)))
    {V : Submodule ℝ (W1p mu Omega p)} (hV : IsClosed (V : Set (W1p mu Omega p)))
    (hdisj : Disjoint (W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).ker V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ V, ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
  obtain ⟨c, hc, hcM⟩ :=
    (W1p.gradientL (mu := mu) (Omega := Omega) (p := p)).exists_pos_mul_norm_le_of_compact_estimate
      (C := 1) hK (fun u ↦ by
        rw [one_mul, add_comm, W1p.gradientL_apply, W1p.valueL_apply]
        exact W1p.norm_le_norm_value_add_norm_gradient u)
      hV hdisj
  refine ⟨c⁻¹, inv_nonneg.2 hc.le, fun u hu ↦ ?_⟩
  rw [le_inv_mul_iff₀ hc, ← W1p.gradientL_apply]
  exact (mul_le_mul_of_nonneg_left (W1p.norm_value_le u) hc.le).trans (hcM u hu)

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
  -- Compactness makes the gradient bounded below on that kernel.
  obtain ⟨C, hC, hCV⟩ :=
    W1p.exists_norm_value_le_mul_norm_gradient_of_isCompactOperator hK ℓ.isClosed_ker hdisj
  refine ⟨C, hC, fun u ↦ ?_⟩
  -- Apply the bound to `u` minus its mean over `S`.
  set a := ⨍ y in S, W1p.value u y ∂mu with ha
  set w : W1p mu Omega p := u - W1p.const a with hw
  have hw0 : ℓ w = 0 := by
    have hconst : ℓ (W1p.const a) = mu.real S * a := by
      rw [hℓ, ← smul_eq_mul, ← setIntegral_const]
      exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hS (W1p.value_const_ae a))
    rw [hw, map_sub, hconst, hℓ, ha, setAverage_eq, smul_eq_mul, mul_inv_cancel_left₀ hSreal,
      sub_self]
  have hvw : W1p.value w = W1p.value u - Lp.const p (mu.restrict (Omega : Set E)) a := by
    have h := map_sub (W1p.valueL (mu := mu) (Omega := Omega) (p := p)) u (W1p.const a)
    rwa [W1p.valueL_apply, W1p.valueL_apply, W1p.valueL_apply, W1p.value_const, ← hw] at h
  have hgw : W1p.gradient w = W1p.gradient u := by
    rw [hw, W1p.gradient_sub, W1p.gradient_const, sub_zero]
  have hbound : ‖W1p.value w‖ ≤ C * ‖W1p.gradient u‖ :=
    hgw ▸ hCV w (LinearMap.mem_ker.2 hw0)
  rw [eLpNorm_sub_const_eq_enorm, ← hvw, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal hbound

end TauCeti

end
