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
public import TauCeti.MeasureTheory.Group.Circle
public import TauCeti.Analysis.Complex.LinearIsometryGroup
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# The linear reflection in a side direction

The plane is `ℂ`, and a direction is a unit complex number, an element of `Circle`. For a side of
a polygonal billiard table with unit direction `d`, the linear reflection in the line spanned by
`d` is `σ_d(v) = d² · conj v`, the reflection `TauCeti.Complex.conjReflection (d²)`. It fixes
`d`, negates `i · d`, depends on `d` only up to sign, is an involution, and commutes with
`v ↦ -v`. The composite of two such reflections is the rotation
through twice the angle between their lines: `σ_d ∘ σ_e` is multiplication by `(d · e⁻¹)²`.

On directions, the reflection is the involution `v ↦ d² / v` of `Circle`, Mathlib's
`Equiv.divLeft (d ^ 2)`. It preserves the arclength measure `TauCeti.circleArcLength` of `Circle`,
the image of the Haar measure `volume` of `AddCircle (2π)` under `AddCircle.homeomorphCircle'`.

## Main definitions

* `TauCeti.Billiard.sideReflection d`: the linear isometry `z ↦ d² · conj z` of `ℂ`.
* `TauCeti.Billiard.directionReflection d`: the same reflection on directions, as an involutive
  permutation of `Circle`.

## Main results

* `TauCeti.Billiard.sideReflection_eq_conjReflection_sq`: `σ_d` is the reflection
  `TauCeti.Complex.conjReflection (d²)`, so the general facts about rotations and reflections
  apply to it.
* `TauCeti.Billiard.sideReflection_eq_reflection`: `σ_d` is Mathlib's `reflection (ℝ ∙ d)`.
* `TauCeti.Billiard.sideReflection_neg`: `σ_{-d} = σ_d`.
* `TauCeti.Billiard.sideReflection_sideReflection`: `σ_d` is an involution.
* `TauCeti.Billiard.sideReflection_trans_sideReflection`: `σ_d ∘ σ_e = rotation ((d · e⁻¹)²)`.
* `TauCeti.Billiard.measurePreserving_directionReflection`: `σ_d` preserves the arclength
  measure `TauCeti.circleArcLength`.

## References

* S. Tabachnikov, *Geometry and Billiards*, Chapter 7.
* N. Chernov and R. Markarian, *Chaotic Billiards*, Chapter 2.
-/

public section

noncomputable section

open Complex ComplexConjugate MeasureTheory TauCeti.Complex

namespace TauCeti.Billiard

/-- **The linear reflection in a side direction.** For a unit direction `d`, the real linear
isometry `z ↦ d² · conj z` of `ℂ`, the reflection in the line `ℝ · d`. -/
def sideReflection (d : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  conjReflection (d ^ 2)

/-- The side reflection `σ_d` is the reflection `v ↦ d² conj v`. -/
theorem sideReflection_eq_conjReflection_sq (d : Circle) :
    sideReflection d = conjReflection (d ^ 2) :=
  (rfl)

@[simp]
theorem sideReflection_apply (d : Circle) (z : ℂ) :
    sideReflection d z = (d : ℂ) ^ 2 * conj z := by
  rw [sideReflection_eq_conjReflection_sq, conjReflection_apply, Circle.coe_pow]

/-- `σ_d` is Mathlib's reflection `reflection (ℝ ∙ d)` of `ℂ` in the real line spanned by `d`. -/
theorem sideReflection_eq_reflection (d : Circle) :
    sideReflection d = (ℝ ∙ (d : ℂ)).reflection := by
  ext z
  rw [Submodule.reflection_singleton_apply, Complex.inner, sideReflection_apply, Circle.norm_coe]
  rw [real_smul, two_smul]
  push_cast
  rw [re_eq_add_conj]
  simp only [map_mul, Complex.conj_conj]
  linear_combination (-z) * d.coe_mul_conj_self

/-- The reflection fixes its own direction. -/
theorem sideReflection_self (d : Circle) : sideReflection d d = d := by
  rw [sideReflection_eq_reflection]
  exact Submodule.reflection_mem_subspace_eq_self (Submodule.mem_span_singleton_self _)

/-- The reflection negates the normal direction `i · d`. -/
theorem sideReflection_I_mul (d : Circle) : sideReflection d (I * d) = -(I * d) := by
  rw [sideReflection_apply, map_mul, conj_I]
  linear_combination (-I * d) * d.coe_mul_conj_self

/-- The reflection depends on the direction only up to sign. -/
@[simp]
theorem sideReflection_neg (d : Circle) : sideReflection (-d) = sideReflection d := by
  ext z
  simp

/-- The reflection is an involution. -/
theorem sideReflection_sideReflection (d : Circle) (z : ℂ) :
    sideReflection d (sideReflection d z) = z := by
  rw [sideReflection_eq_reflection]
  exact Submodule.reflection_reflection _ z

theorem sideReflection_involutive (d : Circle) : Function.Involutive (sideReflection d) :=
  sideReflection_sideReflection d

@[simp]
theorem sideReflection_symm (d : Circle) : (sideReflection d).symm = sideReflection d :=
  conjReflection_symm _

/-- **Composite of two reflections.** Reflecting in `ℝ · e` and then in `ℝ · d` is the rotation
by `(d · e⁻¹)²`, through twice the angle from `e` to `d`. -/
theorem sideReflection_trans_sideReflection (d e : Circle) :
    (sideReflection e).trans (sideReflection d) = rotation ((d * e⁻¹) ^ 2) := by
  rw [← LinearIsometryEquiv.mul_def, sideReflection_eq_conjReflection_sq,
    sideReflection_eq_conjReflection_sq, conjReflection_mul_conjReflection, mul_pow, inv_pow]

/-- Conjugating a reflection by a rotation reflects in the rotated direction. -/
theorem rotation_trans_sideReflection_trans_rotation (a d : Circle) :
    ((rotation a⁻¹).trans (sideReflection d)).trans (rotation a) = sideReflection (a * d) := by
  simp only [← LinearIsometryEquiv.mul_def, sideReflection_eq_conjReflection_sq,
    conjReflection_mul_rotation, rotation_mul_conjReflection, conjReflection_inj, inv_inv]
  simp [sq, mul_comm, mul_left_comm]

/-- Reflections commute with time reversal `v ↦ -v`. -/
theorem sideReflection_apply_neg (d : Circle) (z : ℂ) :
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

/-- **The reflection on directions.** The involution `v ↦ d² / v` of `Circle`, which is
`v ↦ d² · conj v` on unit complex numbers. -/
def directionReflection (d : Circle) : Equiv.Perm Circle :=
  Equiv.divLeft (d ^ 2)

@[simp]
theorem directionReflection_apply (d : Circle) (v : Circle) :
    directionReflection d v = d ^ 2 / v :=
  (rfl)

theorem coe_directionReflection (d v : Circle) :
    (directionReflection d v : ℂ) = sideReflection d v := by
  rw [directionReflection_apply, div_eq_mul_inv, Circle.coe_mul, Circle.coe_inv_eq_conj,
    Circle.coe_pow, sideReflection_apply]

theorem directionReflection_involutive (d : Circle) :
    Function.Involutive (directionReflection d) :=
  Equiv.divLeft_involutive _

theorem directionReflection_directionReflection (d v : Circle) :
    directionReflection d (directionReflection d v) = v :=
  directionReflection_involutive d v

@[simp]
theorem directionReflection_symm (d : Circle) :
    (directionReflection d).symm = directionReflection d :=
  Equiv.symm_divLeft _

theorem continuous_directionReflection (d : Circle) : Continuous (directionReflection d) :=
  continuous_const.div' continuous_id

@[simp]
theorem directionReflection_neg (d : Circle) :
    directionReflection (-d) = directionReflection d := by
  ext v
  simp

/-- Reflections of directions commute with `v ↦ -v`. -/
theorem directionReflection_apply_neg (d v : Circle) :
    directionReflection d (-v) = -directionReflection d v := by
  ext
  simp [div_neg]

/-- On angles, the reflection in the direction `exp(iβ)` is `θ ↦ 2β - θ`. -/
theorem directionReflection_homeomorphCircle' (β : ℝ) (θ : AddCircle (2 * Real.pi)) :
    directionReflection (Circle.exp β) (AddCircle.homeomorphCircle' θ) =
      AddCircle.homeomorphCircle' ((2 * β : ℝ) - θ) := by
  induction θ using QuotientAddGroup.induction_on with
  | H x =>
    rw [← AddCircle.coe_sub, AddCircle.homeomorphCircle'_apply_mk,
      AddCircle.homeomorphCircle'_apply_mk, directionReflection_apply, Circle.exp_sub,
      ← Circle.exp_natCast_mul]
    norm_num

/-- **The reflection preserves arclength.** Each `σ_d` preserves the arclength measure
`TauCeti.circleArcLength` on `Circle`. -/
theorem measurePreserving_directionReflection (d : Circle) :
    MeasurePreserving (directionReflection d) circleArcLength circleArcLength := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
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
  rw [circleArcLength_def, Measure.map_map hσ hh, hcomp, ← Measure.map_map hh hsub.measurable,
    hsub.map_eq]

end TauCeti.Billiard
