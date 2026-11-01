/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.OrderClosed

/-!
# Boundaries of regular scalar superlevel sets

A continuous real-valued function whose derivative does not vanish on a level has that level
as the frontier of its strict superlevel set. This identifies the boundary of domains selected
by regular values without requiring a choice of normal vector field.

At a regular point the gradient is normal to the level in the metric sense: if `y` is a point of
the sublevel set `{z | v z ≤ v y}` nearest to `x`, and the gradient of `v` at `y` is nonzero, then
`x - y` is a nonnegative multiple of that gradient
(`DifferentiableAt.sub_eq_smul_gradient_of_forall_dist_le`).
-/

public section

open Filter Set
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : E → ℝ} {t : ℝ}

/-- The frontier of a strict superlevel set is its level set if the derivative is nonzero
everywhere on that level. -/
theorem Continuous.frontier_setOf_lt_eq_of_fderiv_ne_zero (hu : Continuous u)
    (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) :
    frontier {x | t < u x} = {x | u x = t} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact (frontier_lt_subset_eq continuous_const hu hx).symm
  · intro x (hx : u x = t)
    rw [frontier_eq_closure_inter_closure]
    refine ⟨?_, subset_closure (not_lt.mpr hx.le)⟩
    by_contra h
    rw [mem_closure_iff_frequently, not_frequently] at h
    have hmax : IsLocalMax u x := h.mono fun y hy ↦ by simpa [hx] using not_lt.1 hy
    exact hreg x hx hmax.fderiv_eq_zero

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {v : F → ℝ} {x y : F}

/-- **Nearest points on a regular sublevel set.** If `y` is a point of the sublevel set
`{z | v z ≤ v y}` nearest to `x`, and `v` is differentiable at `y` with nonzero gradient, then
`x - y` is the nonnegative multiple `(‖x - y‖ / ‖∇v(y)‖) • ∇v(y)` of the gradient. -/
theorem DifferentiableAt.sub_eq_smul_gradient_of_forall_dist_le (hd : DifferentiableAt ℝ v y)
    (hg : gradient v y ≠ 0) (hmin : ∀ z, v z ≤ v y → dist x y ≤ dist x z) :
    x - y = (‖x - y‖ / ‖gradient v y‖) • gradient v y := by
  set w := x - y
  set g := gradient v y
  have hg0 : 0 < ‖g‖ := norm_pos_iff.2 hg
  -- Directions along which `v` decreases stay in the sublevel set, so they do not approach `x`.
  have key (e : F) (he : ⟪g, e⟫ < 0) : ⟪w, e⟫ ≤ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => y + h • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
    have hderiv : HasDerivAt (fun h : ℝ => v (y + h • e)) ⟪g, e⟫ 0 := by
      have h2 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
      rwa [show fderiv ℝ v y e = ⟪g, e⟫ by simp [g, gradient]] at h2
    have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), y + h • e ∈ {z | v z ≤ v y} := by
      filter_upwards [hderiv.tendsto_slope_zero_right.eventually (gt_mem_nhds he),
        self_mem_nhdsWithin] with h hh (hpos : 0 < h)
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hh
      exact (sub_neg.1 (neg_of_mul_neg_right hh (inv_pos.2 hpos).le)).le
    have hloc : IsLocalMinOn (fun z => ‖z - x‖ ^ 2) {z | v z ≤ v y} y :=
      IsMinOn.isLocalMinOn fun z hz => by
        have := hmin z hz
        rw [dist_comm x y, dist_comm x z, dist_eq_norm, dist_eq_norm] at this
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have := hloc.hasFDerivWithinAt_nonneg ((hasFDerivAt_id y).sub_const x).norm_sq.hasFDerivWithinAt
      (mem_posTangentConeAt_of_frequently_mem hev.frequently)
    have h2 : ⟪x, e⟫ ≤ ⟪y, e⟫ := by simpa using this
    rw [inner_sub_left]
    linarith
  -- Testing `key` along `w - ((‖w‖ + η) / ‖g‖) • g` for `η > 0` gives `‖w‖ ‖g‖ ≤ ⟪w, g⟫`.
  have hη (η : ℝ) (hη : 0 < η) : ‖w‖ ^ 2 * ‖g‖ ≤ (‖w‖ + η) * ⟪w, g⟫ := by
    have he : ⟪g, w - ((‖w‖ + η) / ‖g‖) • g⟫ < 0 := by
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
      have := real_inner_le_norm w g
      have : (‖w‖ + η) / ‖g‖ * ‖g‖ ^ 2 = (‖w‖ + η) * ‖g‖ := by field_simp
      nlinarith
    have := key _ he
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at this
    have h2 : ‖w‖ ^ 2 ≤ (‖w‖ + η) / ‖g‖ * ⟪w, g⟫ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hg0] at h2
    linarith
  have hlim : Tendsto (fun η : ℝ => (‖w‖ + η) * ⟪w, g⟫) (𝓝[>] 0) (𝓝 (‖w‖ * ⟪w, g⟫)) := by
    have : Continuous (fun η : ℝ => (‖w‖ + η) * ⟪w, g⟫) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hη)
  have hge : ‖w‖ * ‖g‖ ≤ ⟪w, g⟫ := by
    rcases (norm_nonneg w).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, norm_eq_zero.1 h0.symm, inner_zero_left]
    · exact le_of_mul_le_mul_left (by nlinarith) h0
  have := inner_eq_norm_mul_iff_real.1 (le_antisymm (real_inner_le_norm w g) hge)
  rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hg0.ne', one_smul]

end InnerProduct
