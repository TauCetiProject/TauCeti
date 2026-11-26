/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ACL.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UnitInterval

/-!
# An `ACL` map into `C([0, 1], ℝ)` with no derivative

A Lipschitz, hence `ACL^p`, map into the infinite-dimensional space `C([0, 1], ℝ)` that is
differentiable at no point of `[0, 1]`. On the line `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, the map
`u(t)(s) = |t - s|` into `C([0, 1], ℝ)` with the supremum norm satisfies `‖u(t) - u(r)‖ = |t - r|`
for `t ∈ [0, 1]` (`TauCeti.ACLContinuousMapCheck.norm_u_sub_u`), so it is `1`-Lipschitz
(`TauCeti.ACLContinuousMapCheck.lipschitzWith_u`) and `ACL^p` for every `p`
(`TauCeti.ACLContinuousMapCheck.isACLpOn_u`). At every `t ∈ [0, 1]` it has no derivative, not even
along the line (`TauCeti.ACLContinuousMapCheck.not_lineDifferentiableAt_u`): evaluation at
`s = t` would make `r ↦ |r|` differentiable at `0`. So almost-everywhere differentiation of
`ACL` maps can fail for infinite-dimensional targets such as `C([0, 1], ℝ)`. For the scalar map
`t ↦ |t - s₀|` the derivative is `-1` for `t < s₀` and `+1` for `t > s₀`
(`TauCeti.ACLContinuousMapCheck.hasDerivAt_abs_sub`), and fails to exist only at `s₀`
(`TauCeti.ACLContinuousMapCheck.not_differentiableAt_abs_sub`).
-/

public section

open Set unitInterval
open scoped ENNReal

noncomputable section

namespace TauCeti.ACLContinuousMapCheck

local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- The map `u(t)(s) = |t - s|` from the line into `C([0, 1], ℝ)`. -/
def u (x : ℝ¹) : C(I, ℝ) :=
  ⟨fun s ↦ |x 0 - s|, by fun_prop⟩

/-- The values of `u`. -/
@[simp]
theorem u_apply (x : ℝ¹) (s : I) : u x s = |x 0 - s| := (rfl)

/-- `u` moves at most at unit speed: `‖u(t) - u(r)‖ ≤ |t - r|`. -/
theorem norm_u_sub_u_le (x y : ℝ¹) : ‖u x - u y‖ ≤ |x 0 - y 0| :=
  (ContinuousMap.norm_le _ (abs_nonneg _)).2 fun s ↦ by
    simpa [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub (x 0 - s) (y 0 - s)

/-- **`u` is an isometric curve on `[0, 1]`**: `‖u(t) - u(r)‖ = |t - r|` for `t ∈ [0, 1]`. -/
theorem norm_u_sub_u {x : ℝ¹} (hx : x 0 ∈ I) (y : ℝ¹) : ‖u x - u y‖ = |x 0 - y 0| := by
  refine le_antisymm (norm_u_sub_u_le x y) ?_
  have := (u x - u y).norm_coe_le_norm ⟨x 0, hx⟩
  simpa [Real.norm_eq_abs, abs_sub_comm (y 0)] using this

/-- `u` is `1`-Lipschitz. -/
theorem lipschitzWith_u : LipschitzWith 1 u :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [dist_eq_norm, NNReal.coe_one, one_mul]
    refine (norm_u_sub_u_le x y).trans ?_
    simpa [Real.dist_eq] using PiLp.dist_apply_le x y 0

/-- `u` is `ACL^p` on every set, for every exponent `p`. -/
theorem isACLpOn_u (p : ℝ≥0∞) (Ω : Set ℝ¹) : IsACLpOn u p Ω :=
  lipschitzWith_u.locallyLipschitz.isACLpOn Ω p

/-- **`u` has no derivative along the line** at any `t ∈ [0, 1]`. -/
theorem not_lineDifferentiableAt_u {x : ℝ¹} (hx : x 0 ∈ I) :
    ¬ LineDifferentiableAt ℝ u x (EuclideanSpace.single 0 1) := by
  intro h
  have hev := ((ContinuousMap.evalCLM ℝ (⟨x 0, hx⟩ : I)).differentiableAt).comp (0 : ℝ) h
  refine not_differentiableAt_abs_zero (hev.congr_of_eventuallyEq ?_)
  refine Filter.Eventually.of_forall fun r ↦ ?_
  simp [Function.comp_apply]

/-- `u` is differentiable at no `t ∈ [0, 1]`. -/
theorem not_differentiableAt_u {x : ℝ¹} (hx : x 0 ∈ I) : ¬ DifferentiableAt ℝ u x :=
  fun h ↦ not_lineDifferentiableAt_u hx h.lineDifferentiableAt

/-- For the scalar map `t ↦ |t - s₀|`, the derivative at `t ≠ s₀` is the sign of `t - s₀`:
`-1` for `t < s₀` and `+1` for `t > s₀`. -/
theorem hasDerivAt_abs_sub {s₀ t : ℝ} (ht : t ≠ s₀) :
    HasDerivAt (fun r ↦ |r - s₀|) (SignType.sign (t - s₀) : ℝ) t :=
  HasDerivAt.comp_sub_const t s₀ (hasDerivAt_abs (sub_ne_zero.mpr ht))

/-- The scalar map `t ↦ |t - s₀|` is not differentiable at `s₀`. -/
theorem not_differentiableAt_abs_sub (s₀ : ℝ) : ¬ DifferentiableAt ℝ (fun r ↦ |r - s₀|) s₀ := by
  rw [differentiableAt_comp_sub_const, sub_self]
  exact not_differentiableAt_abs_zero

end TauCeti.ACLContinuousMapCheck
