/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Levi form of `-log (1 - ‖g‖²)`

For a smooth map `g` into a real inner product space, the function `y ↦ -log (1 - ‖g y‖²)` is
smooth where `‖g‖ < 1`. For a holomorphic map `g` from a complex normed space into a complex
inner product space, writing this function as `h ∘ ‖g‖²` with
`h t = -log (1 - t)` convex and increasing, its Levi diagonal at `v` is at least
`h'(‖g‖²) ‖Dg(v)‖² ≥ ‖Dg(v)‖²`, since the Levi diagonal of `‖g‖²` is exactly `‖Dg(v)‖²`
(`TauCeti.re_leviForm_norm_sq_sub_comp_apply_self`). Such functions are the building blocks of
plurisubharmonic exhaustions of domains cut out by inequalities `‖g‖ < 1`.

## Main declarations

* `TauCeti.contDiffAt_neg_log_one_sub_norm_sq`: `-log (1 - ‖g‖²)` is as smooth as `g` where
  `‖g‖ < 1`.
* `TauCeti.norm_fderiv_apply_sq_le_re_leviForm_neg_log_one_sub_norm_sq`: the Levi form of
  `-log (1 - ‖g‖²)` dominates `‖Dg(·)‖²` for holomorphic `g` with `‖g‖ < 1`.

## References

* L. Hörmander, *An introduction to complex analysis in several variables*, 3rd ed.,
  North-Holland, 1990, §2.6.
-/

public section

namespace TauCeti

/-- `y ↦ -log (1 - ‖g y‖²)` is as smooth as the map `g` into a real inner product space where
`‖g‖ < 1`. -/
theorem contDiffAt_neg_log_one_sub_norm_sq {G F : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {g : G → F} {x : G}
    {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n g x) (hx : ‖g x‖ < 1) :
    ContDiffAt ℝ n (fun y ↦ -Real.log (1 - ‖g y‖ ^ 2)) x := by
  have hpos : 0 < 1 - ‖g x‖ ^ 2 := by nlinarith [norm_nonneg (g x)]
  exact ((contDiffAt_const.sub (hg.norm_sq ℝ)).log hpos.ne').neg

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {g : V → E} {x : V}

/-- **The Levi form of `-log (1 - ‖g‖²)`.** For a holomorphic map `g` into a complex inner product
space with `‖g x‖ < 1`, the Levi diagonal of `y ↦ -log (1 - ‖g y‖²)` at `x` in the direction `v`
is at least `‖Dg(x) v‖²`. In particular its Levi form at `x` is positive semidefinite, and
positive definite (the function is strictly plurisubharmonic at `x`) when `Dg(x)` is injective. -/
theorem norm_fderiv_apply_sq_le_re_leviForm_neg_log_one_sub_norm_sq (hg : ContDiffAt ℂ 2 g x)
    (hx : ‖g x‖ < 1) (v : V) :
    ‖fderiv ℂ g x v‖ ^ 2 ≤ (leviForm (fun y ↦ -Real.log (1 - ‖g y‖ ^ 2)) x v v).re := by
  set t := ‖g x‖ ^ 2
  have ht : 0 < 1 - t := by nlinarith [norm_nonneg (g x)]
  -- Write the function as `h ∘ f` with `f = ‖g‖²` and `h t = -log (1 - t)`.
  set h : ℝ → ℝ := fun t ↦ -Real.log (1 - t)
  have hderiv {u : ℝ} (hu : u < 1) : HasDerivAt h (1 - u)⁻¹ u := by
    simpa [h, Pi.neg_def, div_eq_inv_mul] using
      (((hasDerivAt_id u).const_sub 1).log (sub_pos.2 hu).ne').neg
  have hderiv₂ : HasDerivAt (deriv h) (((1 - t) ^ 2)⁻¹) t := by
    have heq : deriv h =ᶠ[nhds t] fun u ↦ (1 - u)⁻¹ :=
      (eventually_lt_nhds (sub_pos.1 ht)).mono fun u hu ↦ (hderiv hu).deriv
    refine HasDerivAt.congr_of_eventuallyEq ?_ heq
    simpa [Pi.inv_def] using ((hasDerivAt_id t).const_sub 1).inv ht.ne'
  have hh : ContDiffAt ℝ 2 h t := ((contDiffAt_const.sub contDiffAt_id).log ht.ne').neg
  have hf : ContDiffAt ℝ 2 (fun y ↦ ‖g y‖ ^ 2) x := (hg.restrict_scalars ℝ).norm_sq ℂ
  have hh₂ : 0 ≤ iteratedDeriv 2 h t := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv₂.deriv]
    positivity
  have key := le_re_leviForm_scalar_comp_apply_self (f := fun y ↦ ‖g y‖ ^ 2) hh hf hh₂ v
  have hLf : (leviForm (fun y ↦ ‖g y‖ ^ 2) x v v).re = ‖fderiv ℂ g x v‖ ^ 2 := by
    simpa using re_leviForm_norm_sq_sub_comp_apply_self (a := 0) hg v
  rw [(hderiv (sub_pos.1 ht)).deriv, hLf] at key
  refine le_trans ?_ key
  rw [← div_eq_inv_mul]
  exact le_div_self (sq_nonneg _) ht (by linarith [sq_nonneg ‖g x‖])

end TauCeti
