/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The linear reflection in a side direction

The plane is `ℂ`, and a direction is a unit complex number, an element of `Circle`. For a side of
a polygonal billiard table with unit direction `d`, the linear reflection in the line spanned by
`d` is `σ_d(v) = d² · conj v`. It fixes `d`, negates `i · d`, depends on `d` only up to sign, is an
involution, and commutes with `v ↦ -v`. The composite of two such reflections is the rotation
through twice the angle between their lines: `σ_d ∘ σ_e` is multiplication by `(d · e⁻¹)²`.

On directions, the reflection is the involution `v ↦ d² · v⁻¹` of `Circle`. It preserves the
arclength measure `dθ` of `Circle`, the image of the Haar measure `volume` of `AddCircle (2π)`
under `AddCircle.homeomorphCircle'`.

## Main definitions

* `TauCeti.Billiard.sideReflection d`: the linear isometry `z ↦ d² · conj z` of `ℂ`.
* `TauCeti.Billiard.directionReflection d`: the same reflection on directions, as an involutive
  permutation of `Circle`.
* `TauCeti.Billiard.arcLength`: the arclength measure `dθ` on `Circle`.

## Main results

* `TauCeti.Billiard.sideReflection_eq_reflection`: `σ_d` is Mathlib's `reflection (ℝ ∙ d)`.
* `TauCeti.Billiard.sideReflection_neg`: `σ_{-d} = σ_d`.
* `TauCeti.Billiard.sideReflection_sideReflection`: `σ_d` is an involution.
* `TauCeti.Billiard.sideReflection_trans_sideReflection`: `σ_d ∘ σ_e = rotation ((d · e⁻¹)²)`.
* `TauCeti.Billiard.measurePreserving_directionReflection`: `σ_d` preserves `dθ`.

## References

* S. Tabachnikov, *Geometry and Billiards*, Chapter 7.
* N. Chernov and R. Markarian, *Chaotic Billiards*, Chapter 2.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory

namespace TauCeti.Billiard

/-- **The linear reflection in a side direction.** For a unit direction `d`, the real linear
isometry `z ↦ d² · conj z` of `ℂ`, the reflection in the line `ℝ · d`. -/
def sideReflection (d : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  conjLIE.trans (rotation (d ^ 2))

@[simp]
theorem sideReflection_apply (d : Circle) (z : ℂ) :
    sideReflection d z = (d : ℂ) ^ 2 * conj z := by
  rw [sideReflection, LinearIsometryEquiv.trans_apply, rotation_apply, conjLIE_apply,
    Circle.coe_pow]

/-- `σ_d` is Mathlib's reflection `reflection (ℝ ∙ d)` of `ℂ` in the real line spanned by `d`. -/
theorem sideReflection_eq_reflection (d : Circle) :
    sideReflection d = (ℝ ∙ (d : ℂ)).reflection := by
  have h : (d : ℂ) * conj (d : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  ext z
  rw [Submodule.reflection_singleton_apply, Complex.inner, sideReflection_apply, Circle.norm_coe]
  rw [real_smul, two_smul]
  push_cast
  rw [re_eq_add_conj]
  simp only [map_mul, Complex.conj_conj]
  linear_combination (-z) * h

/-- The reflection fixes its own direction. -/
theorem sideReflection_self (d : Circle) : sideReflection d d = d := by
  rw [sideReflection_apply, ← Circle.coe_inv_eq_conj, pow_two, mul_assoc, ← Circle.coe_mul,
    mul_inv_cancel, Circle.coe_one, mul_one]

/-- The reflection negates the normal direction `i · d`. -/
theorem sideReflection_I_mul (d : Circle) : sideReflection d (I * d) = -(I * d) := by
  rw [sideReflection_apply, map_mul, conj_I, ← Circle.coe_inv_eq_conj, pow_two]
  have : (d : ℂ) * (d⁻¹ : Circle) = 1 := by rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  linear_combination (-I * d) * this

/-- The reflection depends on the direction only up to sign. -/
@[simp]
theorem sideReflection_neg (d : Circle) : sideReflection (-d) = sideReflection d := by
  ext z
  simp

/-- The reflection is an involution. -/
theorem sideReflection_sideReflection (d : Circle) (z : ℂ) :
    sideReflection d (sideReflection d z) = z := by
  have h : (d : ℂ) * conj (d : ℂ) = 1 := by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  simp only [sideReflection_apply, map_mul, map_pow, Complex.conj_conj]
  linear_combination ((d : ℂ) * conj (d : ℂ) + 1) * z * h

theorem sideReflection_involutive (d : Circle) : Function.Involutive (sideReflection d) :=
  sideReflection_sideReflection d

@[simp]
theorem sideReflection_symm (d : Circle) : (sideReflection d).symm = sideReflection d := by
  ext z
  rw [LinearIsometryEquiv.symm_apply_eq, sideReflection_sideReflection]

/-- **Composite of two reflections.** Reflecting in `ℝ · e` and then in `ℝ · d` is the rotation
by `(d · e⁻¹)²`, through twice the angle from `e` to `d`. -/
theorem sideReflection_trans_sideReflection (d e : Circle) :
    (sideReflection e).trans (sideReflection d) = rotation ((d * e⁻¹) ^ 2) := by
  ext z
  rw [LinearIsometryEquiv.trans_apply, sideReflection_apply, sideReflection_apply, rotation_apply,
    Circle.coe_pow, Circle.coe_mul, Circle.coe_inv_eq_conj]
  simp only [map_mul, map_pow, Complex.conj_conj]
  ring

/-- Conjugating a reflection by a rotation reflects in the rotated direction. -/
theorem rotation_trans_sideReflection_trans_rotation (a d : Circle) :
    ((rotation a⁻¹).trans (sideReflection d)).trans (rotation a) = sideReflection (a * d) := by
  ext z
  rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, rotation_apply,
    sideReflection_apply, sideReflection_apply, rotation_apply, Circle.coe_inv_eq_conj,
    Circle.coe_mul]
  simp only [map_mul, Complex.conj_conj]
  ring

/-- Reflections commute with time reversal `v ↦ -v`. -/
theorem sideReflection_neg_apply (d : Circle) (z : ℂ) :
    sideReflection d (-z) = -sideReflection d z :=
  map_neg _ z

/-! #### Checks -/

/-- A horizontal side reflects by complex conjugation. -/
theorem sideReflection_one (z : ℂ) : sideReflection 1 z = conj z := by
  simp

/-- A vertical side, with direction `i`, reflects by `v ↦ -conj v`. -/
theorem sideReflection_exp_pi_div_two (z : ℂ) :
    sideReflection (Circle.exp (Real.pi / 2)) z = -conj z := by
  rw [sideReflection_apply, Circle.coe_exp]
  push_cast
  rw [exp_pi_div_two_mul_I, I_sq, neg_one_mul]

/-- A vertical side sends `exp(iπ/4)` to `exp(3iπ/4)`. -/
theorem sideReflection_exp_pi_div_two_exp_pi_div_four :
    sideReflection (Circle.exp (Real.pi / 2)) (exp (Real.pi / 4 * I)) =
      exp (3 * Real.pi / 4 * I) := by
  rw [sideReflection_exp_pi_div_two, ← Complex.exp_conj]
  simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_ofNat]
  rw [← neg_one_mul, ← exp_pi_mul_I, ← Complex.exp_add]
  congr 1
  ring

/-- A side at angle `π/4` sends `1` to `i`. -/
theorem sideReflection_exp_pi_div_four_one : sideReflection (Circle.exp (Real.pi / 4)) 1 = I := by
  rw [sideReflection_apply, map_one, mul_one, Circle.coe_exp, ← Complex.exp_natCast_mul]
  conv_rhs => rw [← exp_pi_div_two_mul_I]
  congr 1
  push_cast
  ring

/-- **The reflection on directions.** The involution `v ↦ d² · v⁻¹` of `Circle`, which is
`v ↦ d² · conj v` on unit complex numbers. -/
def directionReflection (d : Circle) : Equiv.Perm Circle where
  toFun v := d ^ 2 * v⁻¹
  invFun v := d ^ 2 * v⁻¹
  left_inv v := by dsimp only; rw [mul_inv, inv_inv, mul_inv_cancel_left]
  right_inv v := by dsimp only; rw [mul_inv, inv_inv, mul_inv_cancel_left]

@[simp]
theorem directionReflection_apply (d : Circle) (v : Circle) :
    directionReflection d v = d ^ 2 * v⁻¹ :=
  (rfl)

theorem coe_directionReflection (d v : Circle) :
    (directionReflection d v : ℂ) = sideReflection d v := by
  rw [directionReflection_apply, Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_pow,
    sideReflection_apply]

theorem directionReflection_involutive (d : Circle) :
    Function.Involutive (directionReflection d) := fun v ↦ by
  rw [directionReflection_apply, directionReflection_apply, mul_inv, inv_inv, mul_inv_cancel_left]

theorem continuous_directionReflection (d : Circle) : Continuous (directionReflection d) := by
  rw [show ⇑(directionReflection d) = fun v ↦ d ^ 2 * v⁻¹ from funext (directionReflection_apply d)]
  fun_prop

@[simp]
theorem directionReflection_neg (d : Circle) :
    directionReflection (-d) = directionReflection d := by
  ext v
  simp

/-- Reflections of directions commute with `v ↦ -v`. -/
theorem directionReflection_neg_apply (d v : Circle) :
    directionReflection d (-v) = -directionReflection d v := by
  ext
  simp

/-- `2π` is positive, so that `AddCircle (2π)` carries its Haar measure. -/
local instance instFactZeroLtTwoPi : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- **The arclength measure on `Circle`.** The image of the Haar measure `volume` of
`AddCircle (2π)`, of total mass `2π`, under the homeomorphism `θ ↦ exp(iθ)`. -/
def arcLength : Measure Circle :=
  Measure.map AddCircle.homeomorphCircle' volume

/-- On angles, the reflection in the direction `exp(iβ)` is `θ ↦ 2β - θ`. -/
theorem directionReflection_homeomorphCircle' (β : ℝ) (θ : AddCircle (2 * Real.pi)) :
    directionReflection (Circle.exp β) (AddCircle.homeomorphCircle' θ) =
      AddCircle.homeomorphCircle' ((2 * β : ℝ) - θ) := by
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [← AddCircle.coe_sub, AddCircle.homeomorphCircle'_apply_mk,
      AddCircle.homeomorphCircle'_apply_mk, directionReflection_apply, Circle.exp_sub,
      div_eq_mul_inv, ← Circle.exp_natCast_mul]
    norm_num

/-- **The reflection preserves arclength.** Each `σ_d` preserves the measure `dθ` on `Circle`. -/
theorem measurePreserving_directionReflection (d : Circle) :
    MeasurePreserving (directionReflection d) arcLength arcLength := by
  obtain ⟨β, rfl⟩ : ∃ β : ℝ, Circle.exp β = d := ⟨_, Circle.exp_arg d⟩
  have hh : Measurable AddCircle.homeomorphCircle' :=
    AddCircle.homeomorphCircle'.continuous.measurable
  have hsub : MeasurePreserving (fun θ : AddCircle (2 * Real.pi) ↦ ((2 * β : ℝ) - θ))
      volume volume := Measure.measurePreserving_sub_left volume _
  have hcomp : directionReflection (Circle.exp β) ∘ AddCircle.homeomorphCircle' =
      AddCircle.homeomorphCircle' ∘ fun θ ↦ ((2 * β : ℝ) - θ) := by
    funext θ
    exact directionReflection_homeomorphCircle' β θ
  have hσ := (continuous_directionReflection (Circle.exp β)).measurable
  refine ⟨hσ, ?_⟩
  rw [arcLength, Measure.map_map hσ hh, hcomp, ← Measure.map_map hh hsub.measurable, hsub.map_eq]

end TauCeti.Billiard
