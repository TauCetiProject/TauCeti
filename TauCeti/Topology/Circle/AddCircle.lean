/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The additive circle and the complex unit circle

For a nonzero real period `T`, Mathlib's `AddCircle.homeomorphCircle` identifies `AddCircle T`
with the complex unit circle `Circle`. This file records where that identification sends the
distinguished points: `0 : AddCircle T` is the point `1 : Circle`, so the inverse homeomorphism
carries `1` back to `0`; more generally it carries `exp (2πix / T)` back to the class of `x`.
In the other direction, `AddCircle.toCircle` sends the class of `t` to
`cos (2πt / T) + i sin (2πt / T)`, and the only points it sends to the real points `±1` of `Circle`
are `0` and the half period `T / 2`.
Applied to both factors, it identifies the torus `S¹ × S¹` with the standard torus
`UnitAddTorus (Fin 2) = ℝ² / ℤ²`. Applied coordinatewise, it identifies the standard torus
`UnitAddTorus ι` with the product of circles `ι → Circle` as topological groups.

## Main definitions

* `TauCeti.circleProdHomeomorphUnitAddTorus` — the homeomorphism `S¹ × S¹ ≃ₜ ℝ² / ℤ²`.
* `TauCeti.unitAddTorusEquivPiCircle` — the isomorphism of topological groups
  `UnitAddTorus ι ≃ₜ+ Additive (ι → Circle)`.

## Main results

* `AddCircle.homeomorphCircle_symm_one` — the inverse circle homeomorphism sends `1` to `0` for
  every nonzero real period.
* `AddCircle.homeomorphCircle_symm_exp` — it sends `exp (2πix / T)` to the class of `x`.
* `AddCircle.re_toCircle_coe`, `AddCircle.im_toCircle_coe` — the real and imaginary parts of
  `AddCircle.toCircle` at the class of `t` are `cos (2πt / T)` and `sin (2πt / T)`.
* `AddCircle.toCircle_half_period`, `AddCircle.coe_half_period_ne_zero` — the half period is sent
  to `-1`, so it is not `0`.
* `AddCircle.im_toCircle_eq_zero_iff` — `0` and the half period are the only points at which
  `AddCircle.toCircle` is real.
* `TauCeti.circleProdHomeomorphUnitAddTorus_apply`,
  `TauCeti.circleProdHomeomorphUnitAddTorus_symm_apply` — the torus homeomorphism and its inverse
  act factorwise through `AddCircle.homeomorphCircle`.
* `TauCeti.circleProdHomeomorphUnitAddTorus_exp` — the torus homeomorphism sends
  `(exp (2πia), exp (2πib))` to the class of `(a, b)`.
* `TauCeti.toMul_unitAddTorusEquivPiCircle_apply`,
  `TauCeti.unitAddTorusEquivPiCircle_symm_apply` — the torus isomorphism and its inverse act
  coordinatewise through `AddCircle.homeomorphCircle`.
-/

public section

namespace AddCircle

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `1 : Circle` to `0`. -/
@[simp]
theorem homeomorphCircle_symm_one {T : ℝ} (hT : T ≠ 0) :
    (AddCircle.homeomorphCircle hT).symm 1 = 0 := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `exp (2πix / T)` to the
class of `x`. -/
@[simp]
theorem homeomorphCircle_symm_exp {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    (AddCircle.homeomorphCircle hT).symm (Circle.exp (2 * Real.pi / T * x)) = x := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]

/-- The real part of `AddCircle.toCircle` at the class of `t` is `cos (2πt / T)`. -/
@[simp]
theorem re_toCircle_coe (T t : ℝ) :
    (toCircle (t : AddCircle T) : ℂ).re = Real.cos (2 * Real.pi / T * t) := by
  rw [toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]

/-- The imaginary part of `AddCircle.toCircle` at the class of `t` is `sin (2πt / T)`. -/
@[simp]
theorem im_toCircle_coe (T t : ℝ) :
    (toCircle (t : AddCircle T) : ℂ).im = Real.sin (2 * Real.pi / T * t) := by
  rw [toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

/-- The half period `T / 2` of `AddCircle T` is sent to `-1` by `AddCircle.toCircle`. -/
@[simp]
theorem toCircle_half_period {T : ℝ} (hT : T ≠ 0) : toCircle ((T / 2 : ℝ) : AddCircle T) = -1 := by
  have hangle : 2 * Real.pi / T * (T / 2) = Real.pi := by field_simp
  ext1
  rw [toCircle_apply_mk, Circle.coe_exp, Circle.coe_neg, Circle.coe_one, hangle]
  exact Complex.exp_pi_mul_I

/-- For a nonzero period `T`, the half period `T / 2` is a nonzero point of `AddCircle T`. -/
theorem coe_half_period_ne_zero {T : ℝ} (hT : T ≠ 0) : ((T / 2 : ℝ) : AddCircle T) ≠ 0 :=
  fun h ↦ by
    have := congrArg (fun x ↦ (toCircle x : ℂ).re) h
    norm_num [hT] at this

/-- **The real points of the circle.** For a nonzero period `T`, the value of `AddCircle.toCircle`
at `x` is real exactly when `x` is `0` or the half period `T / 2`; these are sent to `1` and `-1`.
-/
theorem im_toCircle_eq_zero_iff {T : ℝ} (hT : T ≠ 0) {x : AddCircle T} :
    (toCircle x : ℂ).im = 0 ↔ x = 0 ∨ x = ((T / 2 : ℝ) : AddCircle T) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- A unit complex number with vanishing imaginary part is `1` or `-1`.
    have hsq : ((toCircle x : ℂ).re - 1) * ((toCircle x : ℂ).re + 1) = 0 := by
      have := Circle.normSq_coe (toCircle x)
      rw [Complex.normSq_apply, h] at this
      linear_combination this
    -- Such a point of the circle is determined by its real part.
    have heq (w : Circle) (hw : (w : ℂ).im = 0) (hre : (toCircle x : ℂ).re = (w : ℂ).re) :
        toCircle x = w :=
      Circle.ext (Complex.ext hre (h.trans hw.symm))
    rcases mul_eq_zero.1 hsq with hre | hre
    · left
      refine injective_toCircle hT ?_
      rw [toCircle_zero]
      exact heq 1 (by simp) (by simp [sub_eq_zero.1 hre])
    · right
      refine injective_toCircle hT ?_
      rw [toCircle_half_period hT]
      exact heq (-1) (by simp) (by simp [eq_neg_of_add_eq_zero_left hre])
  · rintro (rfl | rfl) <;> simp [hT]

end AddCircle

namespace TauCeti

/-- The torus `S¹ × S¹` is homeomorphic to the standard torus `UnitAddTorus (Fin 2) = ℝ² / ℤ²`,
each circle factor being identified with `ℝ / ℤ` by `AddCircle.homeomorphCircle`. -/
noncomputable def circleProdHomeomorphUnitAddTorus : Circle × Circle ≃ₜ UnitAddTorus (Fin 2) :=
  ((AddCircle.homeomorphCircle one_ne_zero).symm.prodCongr
    (AddCircle.homeomorphCircle one_ne_zero).symm).trans Homeomorph.finTwoArrow.symm

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` reads each circle factor through
`AddCircle.homeomorphCircle.symm`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_apply (z : Circle × Circle) :
    circleProdHomeomorphUnitAddTorus z =
      ![(AddCircle.homeomorphCircle one_ne_zero).symm z.1,
        (AddCircle.homeomorphCircle one_ne_zero).symm z.2] := by
  ext i
  fin_cases i <;> rfl

/-- The inverse identification of `ℝ² / ℤ²` with `S¹ × S¹` sends the coordinates of a point to the
circle by `AddCircle.toCircle`. -/
@[simp]
theorem circleProdHomeomorphUnitAddTorus_symm_apply (x : UnitAddTorus (Fin 2)) :
    circleProdHomeomorphUnitAddTorus.symm x =
      (AddCircle.toCircle (x 0), AddCircle.toCircle (x 1)) := by
  simp [circleProdHomeomorphUnitAddTorus, AddCircle.homeomorphCircle_apply]

/-- The identification of `S¹ × S¹` with `ℝ² / ℤ²` sends `(exp (2πia), exp (2πib))` to the class
of `(a, b)`. -/
theorem circleProdHomeomorphUnitAddTorus_exp (a b : ℝ) :
    circleProdHomeomorphUnitAddTorus
        (Circle.exp (2 * Real.pi * a), Circle.exp (2 * Real.pi * b)) =
      ![(a : UnitAddCircle), (b : UnitAddCircle)] := by
  have h (x : ℝ) : (AddCircle.homeomorphCircle one_ne_zero).symm (Circle.exp (2 * Real.pi * x)) =
      (x : UnitAddCircle) := by
    simpa using AddCircle.homeomorphCircle_symm_exp one_ne_zero x
  ext i
  fin_cases i <;> simp [circleProdHomeomorphUnitAddTorus, h]

/-- The standard torus `UnitAddTorus ι = (ℝ / ℤ)^ι` is isomorphic as a topological group to the
product `ι → Circle` of unit circles, each coordinate being identified with `Circle` by
`AddCircle.homeomorphCircle`. The group `ι → Circle` is multiplicative, so it appears as
`Additive (ι → Circle)`. -/
noncomputable def unitAddTorusEquivPiCircle {ι : Type*} : UnitAddTorus ι ≃ₜ+ Additive (ι → Circle)
    where
  toEquiv := (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).toEquiv.trans Additive.ofMul
  map_add' x y := by
    ext i
    simp [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add]
  continuous_toFun := continuous_ofMul.comp (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous
  continuous_invFun := (Homeomorph.piCongrRight fun _ : ι ↦
    AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).symm.continuous.comp continuous_toMul

/-- The torus isomorphism `TauCeti.unitAddTorusEquivPiCircle` sends each coordinate to the circle
by `AddCircle.toCircle`. -/
@[simp]
theorem toMul_unitAddTorusEquivPiCircle_apply {ι : Type*} (x : UnitAddTorus ι) (i : ι) :
    (unitAddTorusEquivPiCircle x).toMul i = AddCircle.toCircle (x i) := by
  simp [unitAddTorusEquivPiCircle, AddCircle.homeomorphCircle_apply]

/-- The inverse of the torus isomorphism `TauCeti.unitAddTorusEquivPiCircle` reads each coordinate
through `AddCircle.homeomorphCircle.symm`. -/
@[simp]
theorem unitAddTorusEquivPiCircle_symm_apply {ι : Type*} (z : ι → Circle) (i : ι) :
    unitAddTorusEquivPiCircle.symm (Additive.ofMul z) i =
      (AddCircle.homeomorphCircle one_ne_zero).symm (z i) := by
  rw [Homeomorph.eq_symm_apply, AddCircle.homeomorphCircle_apply,
    ← toMul_unitAddTorusEquivPiCircle_apply, ContinuousAddEquiv.apply_symm_apply, toMul_ofMul]

end TauCeti
