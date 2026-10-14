/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The first-order condition for strong convexity

A function `f` on a real normed space that is `m`-strongly convex on a set `s`, in Mathlib's sense
`StrongConvexOn s m f`, lies above each of its tangent paraboloids: if `f` has derivative `f'`
within `s` at `x ∈ s`, then for every `y ∈ s`

`f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.

For `m = 0` this is the familiar statement that a differentiable convex function lies above its
tangent hyperplanes. The parameter `m` may be negative, in which case the paraboloid opens
downwards. In an inner product space, with `f'` given by the gradient, this is the inequality that
makes the gradient of a strongly convex potential a subgradient of its potential energy on the
Wasserstein space.

## Main results

* `StrongConvexOn.add_add_le_of_hasFDerivWithinAt`: the first-order condition for strong convexity.
-/

public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m : ℝ} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x y : E}

/-- **The first-order condition for strong convexity.** If `f` is `m`-strongly convex on `s` and
has derivative `f'` within `s` at a point `x ∈ s`, then `f` lies above its tangent paraboloid at `x`
on `s`: `f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for every `y ∈ s`. -/
theorem StrongConvexOn.add_add_le_of_hasFDerivWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasFDerivWithinAt f f' s x) :
    f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  -- Restrict `f` to the segment from `x` to `y`, which lies in `s`:
  -- `g t = f ((1 - t) • x + t • y)`.
  set g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hg : HasDerivWithinAt g (f' (y - x)) (Icc 0 1) 0 := by
    have hd' : HasFDerivWithinAt f f' s (AffineMap.lineMap x y (0 : ℝ)) := by
      rwa [AffineMap.lineMap_apply_zero]
    exact hd'.comp_hasDerivWithinAt 0 AffineMap.hasDerivAt_lineMap.hasDerivWithinAt
      fun t ht ↦ hf.1.lineMap_mem hx hy ht
  have hgs : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 (f' (y - x))) := by
    have := hasDerivWithinAt_iff_tendsto_slope.1 (hg.mono Ioo_subset_Icc_self)
    rwa [sdiff_singleton_eq_self (by simp : (0 : ℝ) ∉ Ioo 0 1),
      nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] at this
  -- On `(0, 1)`, strong convexity bounds the slopes of `g` at `0`.
  have hslope : ∀ t ∈ Ioo (0 : ℝ) 1, slope g 0 t ≤
      f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2) := by
    intro t ht
    have hconv := hf.2 hx hy (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    simp only [smul_eq_mul, norm_sub_rev x y] at hconv
    simp only [slope_def_field, g, AffineMap.lineMap_apply_module, sub_zero, one_smul, zero_smul,
      add_zero]
    rw [div_le_iff₀ ht.1]
    nlinarith
  have hlim : Tendsto (fun t : ℝ ↦ f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f y - f x - (1 - 0) * (m / 2 * ‖y - x‖ ^ 2))) :=
    ((continuous_const.sub ((continuous_const.sub continuous_id).mul
      continuous_const)).tendsto 0).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto hgs hlim
    (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) hslope)
  simp only [sub_zero, one_mul] at this
  linarith
