/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The first-order condition for strong convexity

A function `f` on a real normed space that is `m`-strongly convex on a set `s`, in Mathlib's sense
`StrongConvexOn s m f`, lies above each of its tangent paraboloids: if `f` has derivative `f'`
within `s` at `x ∈ s`, then for every `y ∈ s`

`f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y`.

Only the derivative of `f` at `x` along the direction `y - x` enters, so the inequality is proved
for a line derivative first and the Fréchet version is deduced from it.

For `m = 0` this is the familiar statement that a differentiable convex function lies above its
tangent hyperplanes. The parameter `m` may be negative, in which case the paraboloid opens
downwards. In an inner product space, with `f'` given by the gradient, this is the inequality that
makes the gradient of a strongly convex potential a subgradient of its potential energy on the
Wasserstein space.

## Main results

* `StrongConvexOn.add_add_le_of_hasLineDerivWithinAt`: the first-order condition for strong
  convexity, for a line derivative.
* `StrongConvexOn.add_add_le_of_hasFDerivWithinAt`: the first-order condition for strong convexity,
  for a Fréchet derivative.
-/

public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {m d : ℝ} {f : E → ℝ}
  {f' : E →L[ℝ] ℝ} {x y : E}

/-- **The first-order condition for strong convexity**, for a line derivative. If `f` is
`m`-strongly convex on `s` and has line derivative `d` within `s` at a point `x ∈ s` in the
direction `y - x` of a point `y ∈ s`, then `f x + d + m / 2 * ‖y - x‖ ^ 2 ≤ f y`. -/
theorem StrongConvexOn.add_add_le_of_hasLineDerivWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasLineDerivWithinAt ℝ f d s x (y - x)) :
    f x + d + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  -- Restrict `f` to the line through `x` and `y`; the segment between them lies in `s`.
  set g : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
  have hg : HasDerivWithinAt g d (Ioi 0) 0 :=
    HasDerivWithinAt.mono_of_mem_nhdsWithin hd <| mem_of_superset (Ioo_mem_nhdsGT zero_lt_one)
      fun _ ht ↦ hf.1.add_smul_sub_mem hx hy (Ioo_subset_Icc_self ht)
  have hgs : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 d) :=
    (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hg
  -- On `(0, 1)`, strong convexity bounds the slopes of `g` at `0`.
  have hslope : ∀ t ∈ Ioo (0 : ℝ) 1, slope g 0 t ≤
      f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2) := by
    intro t ht
    have hconv := hf.2 hx hy (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    have hxy : (1 - t) • x + t • y = x + t • (y - x) := by module
    simp only [hxy, smul_eq_mul, norm_sub_rev x y] at hconv
    simp only [slope_def_field, g, sub_zero, zero_smul, add_zero]
    rw [div_le_iff₀ ht.1]
    nlinarith
  have hlim : Tendsto (fun t : ℝ ↦ f y - f x - (1 - t) * (m / 2 * ‖y - x‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f y - f x - (1 - 0) * (m / 2 * ‖y - x‖ ^ 2))) :=
    (by fun_prop : Continuous _).continuousWithinAt
  have := le_of_tendsto_of_tendsto hgs hlim (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) hslope)
  linarith

/-- **The first-order condition for strong convexity.** If `f` is `m`-strongly convex on `s` and
has derivative `f'` within `s` at a point `x ∈ s`, then `f` lies above its tangent paraboloid at `x`
on `s`: `f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y` for every `y ∈ s`. -/
theorem StrongConvexOn.add_add_le_of_hasFDerivWithinAt (hf : StrongConvexOn s m f) (hx : x ∈ s)
    (hy : y ∈ s) (hd : HasFDerivWithinAt f f' s x) :
    f x + f' (y - x) + m / 2 * ‖y - x‖ ^ 2 ≤ f y :=
  hf.add_add_le_of_hasLineDerivWithinAt hx hy (hd.hasLineDerivWithinAt _)
