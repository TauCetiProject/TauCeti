/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Rays leaving the closed unit ball

Let `x` and `y` be distinct points of a real inner product space `E`, with `x` in the closed unit
ball. The ray `t ↦ x + t • (x - y)`, `t ≥ 0`, starts at `x` and points away from `y`; it meets the
unit sphere at the time `TauCeti.unitSphereRayTime y x`, the larger root of the quadratic equation
`‖x + t • (x - y)‖ ^ 2 = 1`, which is nonnegative. That root is given by an explicit formula, so it
depends continuously on `x` and `y`, and it vanishes when `x` already lies on the unit sphere and
`y` lies in the closed ball.

For a self-map `f` of the closed unit ball without fixed points, following the ray from `f x`
through `x` therefore gives a retraction of the ball onto its boundary sphere
(`ContinuousMap.closedBallRayRetraction`). This is the geometric half of the classical deduction
of Brouwer's fixed-point theorem from the no-retraction theorem.

## Main definitions

* `TauCeti.unitSphereRayTime y x`: the time at which the ray from `y` through `x` meets the unit
  sphere, beyond `x`.
* `ContinuousMap.closedBallRayRetraction f hf`: the retraction of the closed unit ball onto the
  unit sphere along the rays from `f x` through `x`.

## Main results

* `TauCeti.norm_add_unitSphereRayTime_smul_sub`: `x + unitSphereRayTime y x • (x - y)` lies on
  the unit sphere when `‖x‖ ≤ 1` and `x ≠ y`.
* `TauCeti.unitSphereRayTime_eq_zero`: the time vanishes when `x` lies on the unit sphere and
  `‖y‖ ≤ 1`.
* `ContinuousMap.closedBallRayRetraction_apply_of_mem_sphere`: the retraction fixes the unit
  sphere.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.15.
-/

public section

noncomputable section

open Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace TauCeti

/-- The time `t ≥ 0` at which the ray `t ↦ x + t • (x - y)` from `x`, pointing away from `y`,
meets the unit sphere: the larger root of `‖x + t • (x - y)‖ ^ 2 = 1`, a root when `‖x‖ ≤ 1` and
`x ≠ y` (`TauCeti.norm_add_unitSphereRayTime_smul_sub`). -/
def unitSphereRayTime (y x : E) : ℝ :=
  (√(⟪x, x - y⟫ ^ 2 + ‖x - y‖ ^ 2 * (1 - ‖x‖ ^ 2)) - ⟪x, x - y⟫) / ‖x - y‖ ^ 2

/-- The quadratic formula for the time at which the ray from `y` through `x` meets the unit
sphere. -/
theorem unitSphereRayTime_def (y x : E) :
    unitSphereRayTime y x =
      (√(⟪x, x - y⟫ ^ 2 + ‖x - y‖ ^ 2 * (1 - ‖x‖ ^ 2)) - ⟪x, x - y⟫) / ‖x - y‖ ^ 2 :=
  (rfl)

/-- The time at which a ray from a point of the closed unit ball meets the unit sphere is
nonnegative. -/
theorem unitSphereRayTime_nonneg (y : E) {x : E} (hx : ‖x‖ ≤ 1) : 0 ≤ unitSphereRayTime y x := by
  have h1 : 0 ≤ 1 - ‖x‖ ^ 2 := sub_nonneg.2 (pow_le_one₀ (norm_nonneg x) hx)
  rw [unitSphereRayTime_def]
  refine div_nonneg (sub_nonneg.2 ?_) (sq_nonneg _)
  calc ⟪x, x - y⟫ ≤ |⟪x, x - y⟫| := le_abs_self _
    _ = √(⟪x, x - y⟫ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) h1))

/-- **The ray from `y` through a point `x ≠ y` of the closed unit ball meets the unit sphere at
time `TauCeti.unitSphereRayTime y x`.** -/
@[simp]
theorem norm_add_unitSphereRayTime_smul_sub {x y : E} (hxy : x ≠ y) (hx : ‖x‖ ≤ 1) :
    ‖x + unitSphereRayTime y x • (x - y)‖ = 1 := by
  have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  have hc : 0 < ‖x - y‖ ^ 2 := by positivity
  have hD : 0 ≤ ⟪x, x - y⟫ ^ 2 + ‖x - y‖ ^ 2 * (1 - ‖x‖ ^ 2) :=
    add_nonneg (sq_nonneg _) (mul_nonneg hc.le (sub_nonneg.2 (pow_le_one₀ (norm_nonneg x) hx)))
  have hs := Real.sq_sqrt hD
  -- The time is a root of the quadratic `‖x‖ ^ 2 + 2 t ⟪x, x - y⟫ + t ^ 2 ‖x - y‖ ^ 2 = 1`.
  have hsq : ‖x + unitSphereRayTime y x • (x - y)‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      unitSphereRayTime_def]
    field_simp
    linear_combination hs
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

/-- **A ray from a point `x` of the unit sphere pointing away from a point `y` of the closed unit
ball leaves the ball at once**: when `‖x‖ = 1` and `‖y‖ ≤ 1`, the time
`TauCeti.unitSphereRayTime y x` vanishes. -/
@[simp]
theorem unitSphereRayTime_eq_zero {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) :
    unitSphereRayTime y x = 0 := by
  have ha : 0 ≤ ⟪x, x - y⟫ := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hx]
    nlinarith [real_inner_le_norm x y]
  rw [unitSphereRayTime_def, hx, one_pow, sub_self, mul_zero, add_zero, Real.sqrt_sq ha, sub_self,
    zero_div]

end TauCeti

/-- The formula `TauCeti.unitSphereRayTime (f z) (g z)` depends continuously on `z` when `f` and
`g` are continuous and `g z ≠ f z` everywhere. Where moreover `‖g z‖ ≤ 1`, it is the time at which
the ray from `f z` through `g z` meets the unit sphere. -/
theorem Continuous.unitSphereRayTime {X : Type*} [TopologicalSpace X] {f g : X → E}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ z, g z ≠ f z) :
    Continuous fun z ↦ TauCeti.unitSphereRayTime (f z) (g z) := by
  simp only [TauCeti.unitSphereRayTime_def]
  exact Continuous.div (by fun_prop) (by fun_prop) fun z ↦
    pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 (h z)))

namespace ContinuousMap

variable (f : C(closedBall (0 : E) 1, closedBall (0 : E) 1)) (hf : ∀ x, f x ≠ x)

/-- **The ray retraction of the closed unit ball onto the unit sphere** determined by a self-map
`f` of the ball without fixed points: a point `x` goes to the point where the ray from `f x`
through `x` meets the unit sphere. It fixes the unit sphere
(`ContinuousMap.closedBallRayRetraction_apply_of_mem_sphere`). -/
def closedBallRayRetraction : C(closedBall (0 : E) 1, sphere (0 : E) 1) where
  toFun x := ⟨x + TauCeti.unitSphereRayTime (f x : E) x • ((x : E) - f x),
    mem_sphere_zero_iff_norm.2 <| TauCeti.norm_add_unitSphereRayTime_smul_sub
      (fun h ↦ hf x (Subtype.ext h.symm)) (mem_closedBall_zero_iff.1 x.2)⟩
  continuous_toFun := by
    have := (continuous_subtype_val.comp f.continuous).unitSphereRayTime continuous_subtype_val
      fun x h ↦ hf x (Subtype.ext h.symm)
    fun_prop

/-- The ray retraction sends `x` to `x + t • (x - f x)`, with `t` the time at which the ray from
`f x` through `x` meets the unit sphere. -/
@[simp]
lemma coe_closedBallRayRetraction_apply (x : closedBall (0 : E) 1) :
    (closedBallRayRetraction f hf x : E) =
      x + TauCeti.unitSphereRayTime (f x : E) x • ((x : E) - f x) :=
  (rfl)

/-- The ray retraction of the closed unit ball fixes the points of the unit sphere. -/
theorem closedBallRayRetraction_apply_of_mem_sphere {x : closedBall (0 : E) 1}
    (hx : (x : E) ∈ sphere (0 : E) 1) : (closedBallRayRetraction f hf x : E) = x := by
  rw [coe_closedBallRayRetraction_apply,
    TauCeti.unitSphereRayTime_eq_zero (mem_sphere_zero_iff_norm.1 hx)
      (mem_closedBall_zero_iff.1 (f x).2), zero_smul, add_zero]

end ContinuousMap
