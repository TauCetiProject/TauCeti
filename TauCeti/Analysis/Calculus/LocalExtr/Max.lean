/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import TauCeti.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

/-!
# Local minima of the maximum of two functions

At a right local minimum of the maximum of two right-differentiable real-valued functions,
the right derivatives cannot both be negative. Consequently, equal-length gradients for a positive
definite symmetric bilinear form must be opposite. The maximum need not be differentiable,
and no finite-dimensionality assumption is needed for the bilinear-form result.

## Main results

* `IsLocalMin.max_hasLineDerivAt_nonneg`: directional derivatives cannot both be negative.
* `IsLocalMin.max_hasFDerivAt_nonneg`: the corresponding Fréchet derivative consequence.
* `IsLocalMin.eq_neg_of_max_hasFDerivAt_bilin`: equal-length bilinear gradients are opposite.
* `IsLocalMin.eq_neg_of_max_hasGradientAt`: the inner-product gradient formulation.

Applied to two inverse exponential radius branches at a first minimal collision, the bilinear
result would give the opposite terminal velocities used in Klingenberg's lemma. Constructing
those branches is a separate geometric step.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Theorem 1.36.
* Related public formalizations:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology

/-- At a right local minimum of the maximum, the two right derivatives cannot both be
negative. -/
theorem IsMinFilter.not_both_deriv_neg_max {f g : ℝ → ℝ} {a b x : ℝ}
    (hmin : IsMinFilter (fun t ↦ Max.max (f t) (g t)) (𝓝[>] x) x)
    (hf : HasDerivWithinAt f a (Ioi x) x) (hg : HasDerivWithinAt g b (Ioi x) x) :
    ¬ (a < 0 ∧ b < 0) := by
  rintro ⟨ha, hb⟩
  have hm : ∀ᶠ t in 𝓝[>] x, Max.max (f x) (g x) ≤ Max.max (f t) (g t) :=
    hmin
  have hfalse : ∀ᶠ _ in 𝓝[>] x, False := by
    filter_upwards [hf.eventually_lt_of_neg ha, hg.eventually_lt_of_neg hb, hm]
      with t hft hgt hmt
    exact (not_lt_of_ge hmt) (max_lt
      (hft.trans_le (le_max_left _ _)) (hgt.trans_le (le_max_right _ _)))
  exact hfalse.exists.choose_spec

/-- At a local minimum of a maximum, two line derivatives in the same direction cannot both
be negative. -/
theorem IsLocalMin.max_hasLineDerivAt_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {a b : ℝ} {x y : E}
    (hmin : IsLocalMin (fun z ↦ Max.max (f z) (g z)) x)
    (hf : HasLineDerivAt ℝ f a x y) (hg : HasLineDerivAt ℝ g b x y) :
    0 ≤ Max.max a b := by
  by_contra hneg
  have hm : IsLocalMin (fun t : ℝ ↦ Max.max (f (x + t • y)) (g (x + t • y))) 0 := by
    have hmin0 : IsLocalMin (fun z ↦ Max.max (f z) (g z)) (x + (0 : ℝ) • y) := by
      simpa using hmin
    exact hmin0.comp_continuous (g := fun t : ℝ ↦ x + t • y) (by fun_prop :
      ContinuousAt (fun t : ℝ ↦ x + t • y) 0)
  exact (hm.filter_mono nhdsWithin_le_nhds).not_both_deriv_neg_max
    hf.hasDerivWithinAt hg.hasDerivWithinAt (max_lt_iff.mp (lt_of_not_ge hneg))

/-- At a local minimum of a maximum, the maximum of the directional derivatives is
nonnegative in every direction. -/
theorem IsLocalMin.max_hasFDerivAt_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hmin : IsLocalMin (fun z ↦ Max.max (f z) (g z)) x)
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (y : E) :
    0 ≤ Max.max (f' y) (g' y) :=
  hmin.max_hasLineDerivAt_nonneg (hf.hasLineDerivAt y) (hg.hasLineDerivAt y)

/-- Equal-length gradients for a positive definite symmetric bilinear form are opposite at a
local minimum of the maximum. Only the second slot of the form needs to be continuous. -/
theorem IsLocalMin.eq_neg_of_max_hasFDerivAt_bilin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x u v : E}
    (hmin : IsLocalMin (fun y ↦ Max.max (f y) (g y)) x)
    (B : E →ₗ[ℝ] E →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBpos : ∀ u, u ≠ 0 → 0 < B u u)
    (hf : HasFDerivAt f (B u) x) (hg : HasFDerivAt g (B v) x)
    (hnorm : B u u = B v v) : u = -v := by
  by_contra hne
  have huv : u + v ≠ 0 := fun h ↦ hne (eq_neg_of_add_eq_zero_left h)
  have hpos := hBpos (u + v) huv
  simp only [map_add, add_apply] at hpos
  rw [hBsymm v u, hnorm] at hpos
  have hu : B u (-(u + v)) < 0 := by
    rw [map_neg, map_add, hnorm]
    linarith
  have hv : B v (-(u + v)) < 0 := by
    rw [map_neg, map_add, hBsymm v u]
    linarith
  exact (not_lt_of_ge (hmin.max_hasFDerivAt_nonneg hf hg (-(u + v))))
    (max_lt hu hv)

/-- Equal-norm inner-product gradients are opposite at a local minimum of the maximum. -/
theorem IsLocalMin.eq_neg_of_max_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f g : E → ℝ} {x u v : E}
    (hmin : IsLocalMin (fun y ↦ Max.max (f y) (g y)) x)
    (hf : HasGradientAt f u x) (hg : HasGradientAt g v x)
    (hnorm : ‖u‖ = ‖v‖) : u = -v := by
  exact hmin.eq_neg_of_max_hasFDerivAt_bilin (innerSL ℝ).toLinearMap
    (fun a b ↦ real_inner_comm b a) (fun a ha ↦ real_inner_self_pos.mpr ha)
    hf.hasFDerivAt hg.hasFDerivAt (by
      simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        real_inner_self_eq_norm_sq, hnorm])
