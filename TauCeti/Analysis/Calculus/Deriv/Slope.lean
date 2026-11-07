/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of slopes in topological modules

For a function with a derivative along a filter at a fixed base point, its slopes converge to
that derivative after removing the base point from the filter. This applies to topological
modules, including seminormed spaces where distinct points can have zero distance, and supplies
the difference-quotient limit used to identify metric speed with the norm of a derivative.

Sampling these slopes along `x + t / n` gives the sequential form: if `f` has derivative `f'` at
`x`, then `n • (f (x + t / n) - f x)` tends to `t • f'`. The scalar field has characteristic
zero and continuous nonnegative-rational scalar multiplication, so that `t / n` tends to zero;
both real and complex scalars qualify. This limit feeds the exponential power limit behind the
Trotter product formula.

## Main results

* `HasDerivAtFilter.tendsto_slope`: slopes converge to the derivative away from the base point.
* `HasDerivAt.tendsto_nsmul_sub_add_div`: `n • (f (x + t / n) - f x)` tends to `t • f'`.
* `HasDerivAt.eventually_pos_nhdsGT_and_eventually_neg_nhdsLT`: a real function with positive
  derivative at a zero is positive just to the right of it and negative just to its left.
-/

public section

open Filter Set Topology

/-- The slopes of a function with a derivative along a filter converge to that derivative away
from the base point. -/
theorem HasDerivAtFilter.tendsto_slope {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [SeparatelyContinuousAdd E]
    [ContinuousSMul 𝕜 E]
    {γ : 𝕜 → E} {v : E} {t : 𝕜} {L : Filter 𝕜}
    (h : HasDerivAtFilter γ v (L ×ˢ pure t)) :
    Tendsto (slope γ t) (L ⊓ 𝓟 {t}ᶜ) (𝓝 v) := by
  have hlim := (h.hasFDerivAtFilter.isLittleOTVS.comp_tendsto
    (tendsto_id.prodMk (Filter.tendsto_const_pure (b := t)))).tendsto_inv_smul
  have hlim' := (hlim.mono_left (inf_le_left (a := L) (b := 𝓟 {t}ᶜ))).add_const v
  simp only [zero_add] at hlim'
  refine hlim'.congr' <| eventually_inf_principal.2 <| Eventually.of_forall fun s hs ↦ ?_
  simp [slope_def_module, smul_sub, inv_smul_smul₀ (sub_ne_zero.2 hs)]

/-- If `f` has derivative `f'` at `x`, then the rescaled increments `n • (f (x + t / n) - f x)`
tend to `t • f'` as `n → ∞`. -/
theorem HasDerivAt.tendsto_nsmul_sub_add_div {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [SeparatelyContinuousAdd E]
    [ContinuousSMul 𝕜 E] {f : 𝕜 → E} {f' : E} {x : 𝕜} (hf : HasDerivAt f f' x) (t : 𝕜) :
    Tendsto (fun n : ℕ ↦ n • (f (x + t / n) - f x)) atTop (𝓝 (t • f')) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using tendsto_const_nhds
  have hlim : Tendsto (fun n : ℕ ↦ x + t / n) atTop (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, (eventually_ne_atTop 0).mono fun n hn ↦ ?_⟩
    · simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat t)
    · simp [ht, hn]
  -- `HasDerivAt` and `𝓝[≠] x` are by definition the filter forms used by `tendsto_slope`.
  refine (((HasDerivAtFilter.tendsto_slope hf).comp hlim).const_smul t).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp [slope_def_module, smul_smul, mul_div_cancel₀ _ ht, Nat.cast_smul_eq_nsmul]

/-- **Sign of a function with positive derivative at a zero.** If `χ θ₀ = 0` and `χ` has positive
derivative `d` at `θ₀`, then `χ` is positive just to the right of `θ₀` and negative just to its
left. -/
theorem HasDerivAt.eventually_pos_nhdsGT_and_eventually_neg_nhdsLT {χ : ℝ → ℝ} {θ₀ d : ℝ}
    (hχ : HasDerivAt χ d θ₀) (hd : 0 < d) (hχ0 : χ θ₀ = 0) :
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < χ (θ₀ + t)) ∧ ∀ᶠ t in 𝓝[<] (0 : ℝ), χ (θ₀ + t) < 0 := by
  have hg : HasDerivAt (fun t => χ (θ₀ + t)) d 0 := by
    exact HasDerivAt.comp_const_add θ₀ 0 (by rwa [add_zero])
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos (f := fun t => χ (θ₀ + t))
    (x₀ := 0) (by rw [hg.deriv]; exact hd) (by simpa using hχ0)
  constructor
  · filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht
      (ht0 : 0 < t)
    rwa [sub_zero, sign_pos ht0, sign_eq_one_iff] at ht
  · filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht
      (ht0 : t < 0)
    rwa [sub_zero, sign_neg ht0, sign_eq_neg_one_iff] at ht
