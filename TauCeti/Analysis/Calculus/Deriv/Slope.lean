/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered

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

For a real function, a positive one-sided derivative at `a` fixes the sign of `f x - f a` for
`x` near `a` on that side: if the right derivative at `a` is positive, then `f a < f x` for every
`x > a` close to `a`, and if the left derivative at `a` is positive, then `f x < f a` for every
`x < a` close to `a`.

Comparing the slopes of two curves leaving a common point with the same right derivative shows
that they do not separate linearly: their distance is `o(s - t)` at parameter `s`.

A negative right derivative at `x` forces nearby values to the right to lie strictly below `f x`.

## Main results

* `HasDerivAtFilter.tendsto_slope`: slopes converge to the derivative away from the base point.
* `HasDerivAt.tendsto_nsmul_sub_add_div`: `n • (f (x + t / n) - f x)` tends to `t • f'`.
* `HasDerivWithinAt.eventually_nhdsGT_lt_of_pos`,
  `HasDerivWithinAt.eventually_nhdsLT_lt_of_pos`: a positive right (left) derivative at `a`
  makes `f` larger (smaller) than `f a` just to the right (left) of `a`.
* `HasDerivWithinAt.nonpos_of_mul_le_norm_sub`: two curves with the same right derivative at a
  common point do not separate linearly.
* `HasDerivWithinAt.eventually_lt_of_neg`: `f t < f x` eventually for `t` to the right of `x`.
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
  filter_upwards with n
  simp [slope_def_module, smul_smul, mul_div_cancel₀ _ ht, Nat.cast_smul_eq_nsmul]

/-- If `f : ℝ → ℝ` has positive right derivative at `a`, then `f a < f x` for every `x > a`
close to `a`. -/
theorem HasDerivWithinAt.eventually_nhdsGT_lt_of_pos {f : ℝ → ℝ} {f' a : ℝ}
    (hf : HasDerivWithinAt f f' (Ioi a) a) (hf' : 0 < f') : ∀ᶠ x in 𝓝[>] a, f a < f x := by
  filter_upwards [((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf).eventually
    (lt_mem_nhds hf'), self_mem_nhdsWithin] with x hx hax
  exact (slope_pos_iff hax).mp hx

/-- If `f : ℝ → ℝ` has positive left derivative at `a`, then `f x < f a` for every `x < a`
close to `a`. -/
theorem HasDerivWithinAt.eventually_nhdsLT_lt_of_pos {f : ℝ → ℝ} {f' a : ℝ}
    (hf : HasDerivWithinAt f f' (Iio a) a) (hf' : 0 < f') : ∀ᶠ x in 𝓝[<] a, f x < f a := by
  filter_upwards [((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf).eventually
    (lt_mem_nhds hf'), self_mem_nhdsWithin] with x hx hxa
  exact (slope_pos_iff_gt hxa).mp hx

/-- Two curves leaving a common point with the same right derivative do not separate linearly:
if `(s - t) * a ≤ ‖γ₁ s - γ₂ s‖` for all `s > t` close to `t`, then `a ≤ 0`. -/
theorem HasDerivWithinAt.nonpos_of_mul_le_norm_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {γ₁ γ₂ : ℝ → E} {u : E} {t a : ℝ}
    (h₁ : HasDerivWithinAt γ₁ u (Ioi t) t) (h₂ : HasDerivWithinAt γ₂ u (Ioi t) t)
    (h0 : γ₁ t = γ₂ t) (hle : ∀ᶠ s in 𝓝[>] t, (s - t) * a ≤ ‖γ₁ s - γ₂ s‖) : a ≤ 0 := by
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp (h₁.sub h₂)
  rw [sub_self] at hslope
  refine ge_of_tendsto (by simpa using hslope.norm) ?_
  filter_upwards [hle, self_mem_nhdsWithin] with s hs (hst : t < s)
  simpa [slope_def_module, h0, norm_smul, abs_of_pos (sub_pos.2 hst),
    le_inv_mul_iff₀ (sub_pos.2 hst)] using hs

/-- A negative right derivative at `x` forces `f t < f x` for all `t > x` sufficiently close
to `x`. -/
theorem HasDerivWithinAt.eventually_lt_of_neg {f : ℝ → ℝ} {a x : ℝ}
    (hf : HasDerivWithinAt f a (Ioi x) x) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] x, f t < f x := by
  filter_upwards [hf.limsup_slope_le' (lt_irrefl x) ha, self_mem_nhdsWithin]
    with t ht hxt
  rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hxt), zero_mul] at ht
  exact sub_neg.mp ht
