/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Abel

/-!
# Directional derivatives

For a function `f : 𝕜 → F` of one variable, the directional derivative in the direction `1` is
the ordinary derivative. This identifies the weak directional derivatives of
`TauCeti.HasWeakLineDerivOn` on the real line with one-variable derivatives.

Outside the topological support of a function on a topological vector space, its directional
derivatives vanish. This is the directional counterpart of Mathlib's `fderiv_of_notMem_tsupport`.
Both results require no differentiability hypothesis, which matters for Lipschitz functions.

A differentiable map that is affine near `0` along a line `s ↦ w + s • d` has the slope of that
line as its derivative at `w` in the direction `d` (`DifferentiableAt.fderiv_apply_eq_of_add_smul`).
The derivative of the restriction of any function to a line is its directional derivative along
the line (`TauCeti.deriv_comp_add_smul_eq_lineDeriv`), and a function whose restriction to a line
is a translate of a differentiable function of one variable has the derivative of that function as
its directional derivative (`HasDerivAt.hasLineDerivAt_of_add_smul`); for a function
differentiable at the base point, this computes its derivative in the direction of the line
(`DifferentiableAt.fderiv_apply_eq_of_hasDerivAt_add_smul`).

For a continuous function `g` with values in a real Banach space, the integral
`y ↦ ∫ₐᵇ g (y - t h) dt` of its translates has directional derivative `g (y - a h) - g (y - b h)` in
the direction `h`, by the fundamental theorem of calculus. On `[0, 1]` this is the segment average
`y ↦ ∫₀¹ g (y - t h) dt`, with directional derivative `g y - g (y - h)`.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The directional derivative of a function of one variable in the direction `1` is its
derivative. No differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_one {f : 𝕜 → F} {x : 𝕜} : lineDeriv 𝕜 f x 1 = deriv f x := by
  simp [lineDeriv, deriv_comp_const_add]

/-- Outside the topological support of `f`, every directional derivative of `f` vanishes. No
differentiability hypothesis is needed. -/
@[simp]
theorem lineDeriv_of_notMem_tsupport {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
    {f : E → F} {x : E} (h : x ∉ tsupport f) (v : E) : lineDeriv 𝕜 f x v = 0 := by
  -- Near `t = 0`, the point `x + t • v` lies outside `tsupport f`, where `f` vanishes.
  have hzero : (fun t : 𝕜 => f (x + t • v)) =ᶠ[𝓝 0] fun _ => 0 :=
    (notMem_tsupport_iff_eventuallyEq.1 h).comp_tendsto
      (Continuous.tendsto' (by fun_prop) 0 x (by simp))
  rw [lineDeriv, hzero.deriv_eq, deriv_const]

/-- If `f (x + t • v) = g (c + t)` for every scalar `t` near `0` and `g` has derivative `g'` at `c`,
then `f` has derivative `g'` at `x` in the direction `v`. -/
theorem _root_.HasDerivAt.hasLineDerivAt_of_add_smul {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {f : E → F} {x v : E} {g : 𝕜 → F} {g' : F} {c : 𝕜} (hg : HasDerivAt g g' c)
    (hf : ∀ᶠ t in 𝓝 (0 : 𝕜), f (x + t • v) = g (c + t)) : HasLineDerivAt 𝕜 f g' x v := by
  unfold HasLineDerivAt
  rw [← add_zero c] at hg
  exact (hg.comp_const_add c 0).congr_of_eventuallyEq hf

/-- If `f` is differentiable at `x`, `f (x + t • v) = g (c + t)` for every scalar `t` near `0` and
`g` has derivative `g'` at `c`, then the derivative of `f` at `x` sends `v` to `g'`. -/
theorem _root_.DifferentiableAt.fderiv_apply_eq_of_hasDerivAt_add_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → F} {x v : E} {g : 𝕜 → F} {g' : F} {c : 𝕜}
    (hf : DifferentiableAt 𝕜 f x) (hg : HasDerivAt g g' c)
    (h : ∀ᶠ t in 𝓝 (0 : 𝕜), f (x + t • v) = g (c + t)) : fderiv 𝕜 f x v = g' :=
  (hf.hasFDerivAt.hasLineDerivAt v).unique (hg.hasLineDerivAt_of_add_smul h)

/-- **A map that is affine along a line has the slope of that line as its derivative there.** If
`g` is differentiable at `w` and `g (w + s • d) = g w + s • y` for every scalar `s` near `0`, then
the derivative of `g` at `w` sends `d` to `y`. -/
theorem _root_.DifferentiableAt.fderiv_apply_eq_of_add_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] {g : F → G} {w d : F} {y : G} (hg : DifferentiableAt 𝕜 g w)
    (h : ∀ᶠ s in 𝓝 (0 : 𝕜), g (w + s • d) = g w + s • y) : fderiv 𝕜 g w d = y :=
  hg.fderiv_apply_eq_of_hasDerivAt_add_smul (g := fun s ↦ g w + s • y) (c := 0)
    (by simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const y).const_add (g w)) (by simpa using h)

/-- The function `y ↦ ∫ₐᵇ g (y - t h) dt` of a continuous `g` has directional derivative
`g (y - a h) - g (y - b h)` in the direction `h`. -/
theorem _root_.Continuous.hasLineDerivAt_intervalIntegral_comp_sub {E G : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSub E] [ContinuousSMul ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {h : E} {g : E → G}
    (hg : Continuous g) (a b : ℝ) (y : E) :
    HasLineDerivAt ℝ (fun y => ∫ t in a..b, g (y - t • h)) (g (y - a • h) - g (y - b • h))
      y h := by
  -- `s ↦ Φ (y + s h)` differentiates by the fundamental theorem of calculus, as
  -- `Φ (y + s h) = ∫_{a-s}^{b-s} g (y - t h) dt`.
  set f : ℝ → G := fun t => g (y - t • h)
  have hf : Continuous f := hg.comp (by fun_prop)
  have hline : (fun s : ℝ => ∫ t in a..b, g (y + s • h - t • h)) =
      fun s => (∫ t in (0 : ℝ)..b - s, f t) - ∫ t in (0 : ℝ)..a - s, f t := by
    funext s
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), ← intervalIntegral.integral_comp_sub_right]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [f, sub_smul]
    congr 1
    abel
  -- `HasLineDerivAt` is by definition the derivative at `0` of `s ↦ Φ (y + s • h)`.
  unfold HasLineDerivAt
  rw [hline]
  have h1 := (hf.integral_hasStrictDerivAt 0 (b - 0)).hasDerivAt.scomp 0
    ((hasDerivAt_id (0 : ℝ)).const_sub b)
  have h2 := (hf.integral_hasStrictDerivAt 0 (a - 0)).hasDerivAt.scomp 0
    ((hasDerivAt_id (0 : ℝ)).const_sub a)
  exact (h1.sub h2).congr_deriv (by simp [f, neg_add_eq_sub])

/-- The derivative at `t` of the restriction `s ↦ f (x + s • v)` of a function to a line is the
directional derivative of `f` at `x + t • v` along `v`. No differentiability hypothesis is needed:
both sides are `0` where `f` is not differentiable along the line. -/
theorem deriv_comp_add_smul_eq_lineDeriv {E : Type*} [AddCommGroup E] [Module 𝕜 E] (f : E → F)
    (x v : E) (t : 𝕜) :
    deriv (fun s : 𝕜 ↦ f (x + s • v)) t = lineDeriv 𝕜 f (x + t • v) v := by
  have h : (fun s : 𝕜 ↦ f (x + s • v)) =
      fun s ↦ (fun u : 𝕜 ↦ f ((x + t • v) + u • v)) (s - t) := by
    funext s
    simp [sub_smul]
  rw [h, deriv_comp_sub_const (f := fun u : 𝕜 ↦ f ((x + t • v) + u • v)), sub_self, lineDeriv]

end TauCeti
