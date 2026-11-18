/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval
public import TauCeti.Geometry.Sphere.Circle
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# The standard parametrization of the circle

The loop `t ↦ (cos 2πt, sin 2πt)` parametrizes the unit circle `S¹ ⊆ ℝ²` once, counterclockwise,
starting at `(1, 0)`. As a map from the interval `I¹`, it collapses the boundary of the interval to
the point `(1, 0)` and is injective elsewhere, so it is a quotient map of `I¹` onto `S¹`.

## Main declarations

* `TauCeti.circleLoop`: the standard loop `I¹ → S¹`.
* `TauCeti.circleLoop_eq_east_iff`, `TauCeti.circleLoop_surjective` and
  `TauCeti.eq_or_of_circleLoop_eq`: it collapses exactly the boundary to `(1, 0)`, is surjective,
  and is injective elsewhere.
* `TauCeti.circleGenLoop`: the standard loop as a generalized loop at `(1, 0)`.
* `TauCeti.sphereHomeomorphCircle_circleLoop`: identified with the complex unit circle, it is
  `t ↦ exp(2πit)`.
* `TauCeti.diskBoundaryTwoLoop`: the same counterclockwise parametrization as a loop of the
  boundary circle `∂D²`, based at `(1, 0)`.
* `TauCeti.diskBoundaryTwoReflect`: the reflection `(w₀, w₁) ↦ (-w₀, w₁)` of `∂D²`.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval Topology.Homotopy

namespace TauCeti

/-- The standard loop `I¹ → S¹`, `t ↦ (cos 2πt, sin 2πt)`. -/
def circleLoop : C(Fin 1 → I, Sphere1) where
  toFun t :=
    ⟨!₂[cos (2 * π * t 0), sin (2 * π * t 0)], by
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact cos_sq_add_sin_sq _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta]
      fun_prop
    · simp only [Fin.mk_one]
      fun_prop

/-- The first coordinate of the standard loop at `t` is `cos 2πt`. -/
@[simp]
theorem circleLoop_apply_zero (t : Fin 1 → I) :
    (circleLoop t : EuclideanSpace ℝ (Fin 2)) 0 = cos (2 * π * t 0) := by
  rw [circleLoop]
  -- unfolding the bundled map leaves exactly this coordinate formula
  rfl

/-- The second coordinate of the standard loop at `t` is `sin 2πt`. -/
@[simp]
theorem circleLoop_apply_one (t : Fin 1 → I) :
    (circleLoop t : EuclideanSpace ℝ (Fin 2)) 1 = sin (2 * π * t 0) := by
  rw [circleLoop]
  -- unfolding the bundled map leaves exactly this coordinate formula
  rfl

/-- The standard loop sends a point of the interval to `(1, 0)` exactly when it is an end point. -/
@[simp]
theorem circleLoop_eq_east_iff (t : Fin 1 → I) :
    circleLoop t = Sphere1.east ↔ t ∈ Cube.boundary (Fin 1) := by
  rw [Cube.boundary_fin_one_iff]
  constructor
  · intro h
    have h0 := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
    simp only [circleLoop_apply_zero, Sphere1.coe_east, PiLp.single_apply,
      ite_true] at h0
    exact eq_zero_or_eq_one_of_cos_two_pi_mul_eq_one h0
  · rintro (h | h)
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.coe_east, h]
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.coe_east, h]

/-- The standard loop `t ↦ (cos 2πt, sin 2πt)` as a generalized loop `I¹ → S¹` at `(1, 0)`. -/
def circleGenLoop : Ω^ (Fin 1) Sphere1 Sphere1.east :=
  ⟨circleLoop, fun t ht => (circleLoop_eq_east_iff t).2 ht⟩

@[simp]
theorem circleGenLoop_apply (t : Fin 1 → I) : circleGenLoop t = circleLoop t :=
  (rfl)

/-- Two points of the interval with the same image under the standard loop are equal, or both
end points. -/
theorem eq_or_of_circleLoop_eq {t t' : Fin 1 → I} (h : circleLoop t = circleLoop t') :
    t = t' ∨ (t ∈ Cube.boundary (Fin 1) ∧ t' ∈ Cube.boundary (Fin 1)) := by
  have hc := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
  have hs := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 1) h
  simp only [circleLoop_apply_zero, circleLoop_apply_one] at hc hs
  rw [Cube.boundary_fin_one_iff, Cube.boundary_fin_one_iff]
  rcases eq_or_of_cos_sin_two_pi_mul_eq hc hs with h | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · left
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h
  · exact Or.inr ⟨Or.inl h0, Or.inr h1⟩
  · exact Or.inr ⟨Or.inr h1, Or.inl h0⟩

/-- The standard loop is surjective. -/
theorem circleLoop_surjective : Function.Surjective circleLoop := by
  rintro ⟨v, hv⟩
  have hn : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
    simpa [Fin.sum_univ_two] using hv
  obtain ⟨t, hc, hs⟩ := exists_cos_sin_two_pi_mul_eq hn
  refine ⟨fun _ => t, Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, circleLoop_apply_zero, hc]
  · simp only [Fin.mk_one, circleLoop_apply_one, hs]

/-- Under the identification of `S¹ ⊆ ℝ²` with the complex unit circle, the standard loop is
`t ↦ exp(2πit)`. -/
@[simp]
theorem sphereHomeomorphCircle_circleLoop (t : Fin 1 → I) :
    EuclideanSpace.sphereHomeomorphCircle (circleLoop t) = Circle.exp (2 * π * t 0) := by
  rw [← Homeomorph.eq_symm_apply]
  refine Subtype.ext ?_
  rw [EuclideanSpace.coe_sphereHomeomorphCircle_symm_exp]
  ext j
  fin_cases j <;> simp

/-! ### The counterclockwise loop of `∂D²` -/

/-- The point `(1, 0)` of the boundary circle `∂D²`. -/
def diskBoundaryTwoBase : TopCat.diskBoundary.{0} 2 :=
  ⟨EuclideanSpace.sphereHomeomorphCircle.symm 1⟩

/-- The point `TauCeti.diskBoundaryTwoBase` is the point `1` of `Circle`. -/
theorem diskBoundaryTwoBase_down :
    diskBoundaryTwoBase.down = EuclideanSpace.sphereHomeomorphCircle.symm 1 :=
  (rfl)

/-- The first coordinate of `TauCeti.diskBoundaryTwoBase` is `1`. -/
@[simp]
theorem diskBoundaryTwoBase_apply_zero :
    (diskBoundaryTwoBase.down : EuclideanSpace ℝ (Fin 2)) 0 = 1 := by
  rw [diskBoundaryTwoBase_down, EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply,
    Circle.coe_one, Complex.orthonormalBasisOneI_repr_apply]
  exact Complex.one_re

/-- The second coordinate of `TauCeti.diskBoundaryTwoBase` is `0`. -/
@[simp]
theorem diskBoundaryTwoBase_apply_one :
    (diskBoundaryTwoBase.down : EuclideanSpace ℝ (Fin 2)) 1 = 0 := by
  rw [diskBoundaryTwoBase_down, EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply,
    Circle.coe_one, Complex.orthonormalBasisOneI_repr_apply]
  exact Complex.one_im

/-- The counterclockwise loop `t ↦ (cos 2πt, sin 2πt)` of the boundary circle `∂D²`, based at
`(1, 0)`: the loop `t ↦ exp(2πit)` of `Circle` carried to `∂D²` by
`TauCeti.EuclideanSpace.sphereHomeomorphCircle`. -/
def diskBoundaryTwoLoop : Path diskBoundaryTwoBase diskBoundaryTwoBase where
  toFun t := ⟨EuclideanSpace.sphereHomeomorphCircle.symm (Circle.exp (2 * π * t))⟩
  continuous_toFun := continuous_uliftUp.comp
    (EuclideanSpace.sphereHomeomorphCircle.symm.continuous.comp (by fun_prop))
  source' := by
    rw [Set.Icc.coe_zero, mul_zero, Circle.exp_zero]
    rfl
  target' := by
    rw [Set.Icc.coe_one, mul_one, Circle.exp_two_pi]
    rfl

/-- The loop `TauCeti.diskBoundaryTwoLoop` at time `t` is the point of `∂D²` corresponding to
`exp(2πit)`. -/
theorem diskBoundaryTwoLoop_down_apply (t : I) :
    (diskBoundaryTwoLoop t).down =
      EuclideanSpace.sphereHomeomorphCircle.symm (Circle.exp (2 * π * t)) :=
  (rfl)

/-- The first coordinate of `TauCeti.diskBoundaryTwoLoop` at time `t` is `cos 2πt`. -/
@[simp]
theorem diskBoundaryTwoLoop_apply_zero (t : I) :
    ((diskBoundaryTwoLoop t).down : EuclideanSpace ℝ (Fin 2)) 0 = cos (2 * π * t) := by
  rw [diskBoundaryTwoLoop_down_apply, EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply,
    Circle.coe_exp, Complex.orthonormalBasisOneI_repr_apply]
  exact Complex.exp_ofReal_mul_I_re _

/-- The second coordinate of `TauCeti.diskBoundaryTwoLoop` at time `t` is `sin 2πt`. -/
@[simp]
theorem diskBoundaryTwoLoop_apply_one (t : I) :
    ((diskBoundaryTwoLoop t).down : EuclideanSpace ℝ (Fin 2)) 1 = sin (2 * π * t) := by
  rw [diskBoundaryTwoLoop_down_apply, EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply,
    Circle.coe_exp, Complex.orthonormalBasisOneI_repr_apply]
  exact Complex.exp_ofReal_mul_I_im _

/-! ### The reflection of `∂D²` -/

/-- The reflection `(w₀, w₁) ↦ (-w₀, w₁)` of the boundary circle `∂D²`. -/
private def diskBoundaryTwoReflectFun (w : TopCat.diskBoundary.{0} 2) :
    TopCat.diskBoundary.{0} 2 :=
  ⟨⟨!₂[-(w.down : EuclideanSpace ℝ (Fin 2)) 0, (w.down : EuclideanSpace ℝ (Fin 2)) 1], by
    have h := mem_sphere_zero_iff_norm.1 w.down.2
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two] at *
    simpa using h⟩⟩

private theorem continuous_diskBoundaryTwoReflectFun : Continuous diskBoundaryTwoReflectFun :=
  continuous_uliftUp.comp (Continuous.subtype_mk (by fun_prop) _)

private theorem diskBoundaryTwoReflectFun_involutive :
    Function.Involutive diskBoundaryTwoReflectFun := fun w ↦
  ULift.ext (Subtype.ext (PiLp.ext (Fin.forall_fin_two.2 ⟨by simp [diskBoundaryTwoReflectFun],
    by simp [diskBoundaryTwoReflectFun]⟩)))

/-- The reflection `(w₀, w₁) ↦ (-w₀, w₁)` of the boundary circle `∂D²`, as an isomorphism of
topological spaces. It is its own inverse. -/
def diskBoundaryTwoReflect : TopCat.diskBoundary.{0} 2 ≅ TopCat.diskBoundary.{0} 2 :=
  TopCat.isoOfHomeo
    { toFun := diskBoundaryTwoReflectFun
      invFun := diskBoundaryTwoReflectFun
      left_inv := diskBoundaryTwoReflectFun_involutive
      right_inv := diskBoundaryTwoReflectFun_involutive
      continuous_toFun := continuous_diskBoundaryTwoReflectFun
      continuous_invFun := continuous_diskBoundaryTwoReflectFun }

/-- The reflection of `∂D²` is its own inverse. -/
@[simp]
theorem diskBoundaryTwoReflect_inv : diskBoundaryTwoReflect.inv = diskBoundaryTwoReflect.hom := by
  rfl

/-- The reflection of `∂D²` negates the first coordinate. -/
@[simp]
theorem diskBoundaryTwoReflect_hom_apply_zero (w : TopCat.diskBoundary.{0} 2) :
    ((diskBoundaryTwoReflect.hom w).down : EuclideanSpace ℝ (Fin 2)) 0 =
      -(w.down : EuclideanSpace ℝ (Fin 2)) 0 := by
  rfl

/-- The reflection of `∂D²` fixes the second coordinate. -/
@[simp]
theorem diskBoundaryTwoReflect_hom_apply_one (w : TopCat.diskBoundary.{0} 2) :
    ((diskBoundaryTwoReflect.hom w).down : EuclideanSpace ℝ (Fin 2)) 1 =
      (w.down : EuclideanSpace ℝ (Fin 2)) 1 := by
  rfl

end TauCeti
