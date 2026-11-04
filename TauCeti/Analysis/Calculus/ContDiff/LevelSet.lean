/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.Gradient

/-!
# A normalized defining function for a regular superlevel set

Let `u` be a smooth compactly supported real function on a real inner product space and let
`t > 0` be a regular value of `u`. Then `w = (u - t) / √(‖∇u‖² + (u - t)²)` is a smooth defining
function of the superlevel set `{u > t}`: it is positive exactly on `{u > t}`, equal to `-1` off
the support of `u` (so `{w ≥ -1/2}` is compact), and its derivative has norm one on its zero level
`{u = t}` (`ContDiff.exists_contDiff_setOf_pos_eq_setOf_lt`).

Such a normalization lets estimates near the boundary of `{u > t}` be stated uniformly in terms of
`‖Dw‖`, which is close to one in a neighbourhood of the zero level.
-/

public section

open Set InnerProductSpace TauCeti
open scoped ContDiff Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **A normalized defining function for a regular superlevel set.** Let `u` be smooth and
compactly supported, and let `t > 0` be a regular value of `u`. Then
`w = (u - t) / √(‖∇u‖² + (u - t)²)` is smooth, positive exactly on `{u > t}`, equal to `-1` off
the support of `u`, and its derivative has norm one on its zero level `{u = t}`. -/
theorem ContDiff.exists_contDiff_setOf_pos_eq_setOf_lt {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t) (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) :
    ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ IsCompact {x | -(1 / 2 : ℝ) ≤ w x} ∧
      (∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1) ∧ {x | 0 < w x} = {x | t < u x} := by
  -- `G` is the gradient of `u` and `g = √(‖∇u‖² + (u - t)²)` is a smooth positive normalizer.
  let G : E → E := ∇ u
  have hG : ContDiff ℝ ∞ G := hu.gradient_right le_rfl
  have hGnorm (x : E) : ‖G x‖ = ‖fderiv ℝ u x‖ := norm_gradient_eq_norm_fderiv u x
  let q : E → ℝ := fun x => ‖G x‖ ^ 2 + (u x - t) ^ 2
  have hq (x : E) : 0 < q x := by
    by_cases hx : u x = t
    · have hGx : 0 < ‖G x‖ := by rw [hGnorm, norm_pos_iff]; exact hreg x hx
      simp only [q, hx, sub_self]
      positivity
    · have := sq_pos_of_ne_zero (sub_ne_zero.2 hx)
      positivity
  let g : E → ℝ := fun x => √(q x)
  have hg : ContDiff ℝ ∞ g :=
    (((contDiff_norm_sq ℝ).comp hG).add ((hu.sub contDiff_const).pow 2)).sqrt fun x => (hq x).ne'
  have hgpos (x : E) : 0 < g x := Real.sqrt_pos.2 (hq x)
  let w : E → ℝ := fun x => (u x - t) / g x
  have hw : ContDiff ℝ ∞ w := (hu.sub contDiff_const).div hg fun x => (hgpos x).ne'
  have hset : {x | 0 < w x} = {x | t < u x} := by
    ext x
    exact (div_pos_iff_of_pos_right (hgpos x)).trans sub_pos
  -- Off the support of `u`, `w = -1`, so `{w ≥ -1/2}` is compact.
  have hK : IsCompact {x | -(1 / 2 : ℝ) ≤ w x} := by
    refine huc.isCompact.of_isClosed_subset (isClosed_le continuous_const hw.continuous)
      fun x hx => ?_
    by_contra hxs
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hxs
    have hgx : g x = t := by
      simp [g, q, G, gradient_of_notMem_tsupport hxs, hu0, Real.sqrt_sq ht.le]
    have hx : -(1 / 2 : ℝ) ≤ (u x - t) / g x := hx
    rw [hgx, hu0, zero_sub, neg_div, div_self ht.ne'] at hx
    linarith
  -- On the level `{u = t}` the derivative of `w` is `Du / ‖Du‖`.
  have hnorm (x : E) (hx : w x = 0) : ‖fderiv ℝ w x‖ = 1 := by
    have hux : u x = t := sub_eq_zero.1 ((div_eq_zero_iff.1 hx).resolve_right (hgpos x).ne')
    have h1 : HasFDerivAt (fun y => u y - t) (fderiv ℝ u x) x :=
      ((hu.differentiable (by simp)) x).hasFDerivAt.sub_const t
    have h2 := (((hg.differentiable (by simp)) x).inv (hgpos x).ne').hasFDerivAt
    have hd : HasFDerivAt w ((g x)⁻¹ • fderiv ℝ u x) x := by
      have := h1.mul h2
      simp only [hux, sub_self, zero_smul, zero_add] at this
      exact this.congr_of_eventuallyEq (.of_forall fun y => div_eq_mul_inv _ _)
    have hgx : g x = ‖fderiv ℝ u x‖ := by
      simp only [g, q, hux, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero, Real.sqrt_sq (norm_nonneg _), hGnorm]
    rw [hd.fderiv, norm_smul, norm_inv, Real.norm_of_nonneg (hgpos x).le, hgx,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hreg x hux))]
  exact ⟨w, hw, hK, hnorm, hset⟩
