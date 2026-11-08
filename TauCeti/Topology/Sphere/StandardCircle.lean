/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Angle
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
* `TauCeti.diskBoundaryTwoLoop`: the same counterclockwise parametrization as a loop of the
  boundary circle `∂D²`, based at `(1, 0)`.
* `TauCeti.diskBoundaryTwoReflect`: the reflection `(w₀, w₁) ↦ (-w₀, w₁)` of `∂D²`.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval

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
    obtain ⟨n, hn⟩ := Real.cos_eq_one_iff _ |>.1 h0
    have hpi : (2 * π) ≠ 0 := by positivity
    have hnt : (n : ℝ) = t 0 := mul_right_cancel₀ hpi (by linarith)
    have h1 : (0 : ℝ) ≤ n := hnt ▸ (t 0).2.1
    have h2 : (n : ℝ) ≤ 1 := hnt ▸ (t 0).2.2
    have : n = 0 ∨ n = 1 := by
      have h1' : 0 ≤ n := by exact_mod_cast h1
      have h2' : n ≤ 1 := by exact_mod_cast h2
      omega
    rcases this with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa using hnt.symm))
    · exact Or.inr (Subtype.ext (by simpa using hnt.symm))
  · rintro (h | h)
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.coe_east, h]
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.coe_east, h]

/-- Two points of the interval with the same image under the standard loop are equal, or both
end points. -/
theorem eq_or_of_circleLoop_eq {t t' : Fin 1 → I} (h : circleLoop t = circleLoop t') :
    t = t' ∨ (t ∈ Cube.boundary (Fin 1) ∧ t' ∈ Cube.boundary (Fin 1)) := by
  have hc := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
  have hs := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 1) h
  simp only [circleLoop_apply_zero, circleLoop_apply_one] at hc hs
  obtain ⟨n, hn⟩ := Real.exists_int_eq_add_of_cos_sin_eq hc hs
  have ha := (t 0).2
  have hb := (t' 0).2
  have h1 : (-1 : ℝ) ≤ n := by linarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (n : ℝ) ≤ 1 := by linarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : -1 ≤ n := by exact_mod_cast h1
  have h2' : n ≤ 1 := by exact_mod_cast h2
  rw [Cube.boundary_fin_one_iff, Cube.boundary_fin_one_iff]
  have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · right
    push_cast at hn
    refine ⟨Or.inl (Subtype.ext ?_), Or.inr (Subtype.ext ?_)⟩ <;>
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one] <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · left
    push_cast at hn
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact Subtype.ext (by linarith)
  · right
    push_cast at hn
    refine ⟨Or.inr (Subtype.ext ?_), Or.inl (Subtype.ext ?_)⟩ <;>
      simp only [Set.Icc.coe_zero, Set.Icc.coe_one] <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The standard loop is surjective. -/
theorem circleLoop_surjective : Function.Surjective circleLoop := by
  rintro ⟨v, hv⟩
  have hn : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
    simpa [Fin.sum_univ_two] using hv
  let z : ℂ := ⟨v 0, v 1⟩
  have hzn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
    nlinarith
  have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
  have hcos : cos (Complex.arg z) = v 0 := by
    rw [Complex.cos_arg hz0, hzn, div_one]
  have hsin : sin (Complex.arg z) = v 1 := by
    rw [Complex.sin_arg, hzn, div_one]
  set θ := Complex.arg z with hθ
  have hp : (0 : ℝ) < 2 * π := by positivity
  set r := toIcoMod hp 0 θ with hr
  have hrmem : r ∈ Set.Ico 0 (2 * π) := toIcoMod_mem_Ico' hp θ
  have hrθ : r = θ - (toIcoDiv hp 0 θ : ℝ) * (2 * π) := by
    rw [hr, toIcoMod, zsmul_eq_mul]
  have hrc : cos r = v 0 := by rw [hrθ, cos_sub_int_mul_two_pi, hcos]
  have hrs : sin r = v 1 := by rw [hrθ, sin_sub_int_mul_two_pi, hsin]
  have hs0 : 0 ≤ r / (2 * π) := div_nonneg hrmem.1 hp.le
  have hs1 : r / (2 * π) ≤ 1 := (div_le_one hp).2 hrmem.2.le
  refine ⟨fun _ => ⟨r / (2 * π), hs0, hs1⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, circleLoop_apply_zero]
    rw [mul_div_cancel₀ _ hp.ne', hrc]
  · simp only [Fin.mk_one, circleLoop_apply_one]
    rw [mul_div_cancel₀ _ hp.ne', hrs]

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
