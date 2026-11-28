/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.RingTheory.DedekindDomain.Circle

import Mathlib.RingTheory.Complex
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.RotationLoop
import TauCeti.Topology.Circle.CoordinateRing

/-!
# Nontriviality of `SK₁` for the algebraic circle

For a field `k` with `2 ≠ 0`, the coordinate ring `CircleRing k = k[x, y] ⧸ (x² + y² - 1)` of the
algebraic circle is a Dedekind domain (`TauCeti.CircleRing.instIsDedekindDomain`). Over any
commutative ring `k` admitting a ring homomorphism `k →+* ℝ` (for instance `k = ℤ`, `ℚ`, or `ℝ`),
its special Whitehead group `SK₁(CircleRing k)` does not vanish. For any commutative ring `k`, the
determinant-one rotation matrix

  `circleRotation k = !![x, -y; y, x] ∈ SL₂(CircleRing k)`

defines a class in `SK₁(CircleRing k)`. Over `ℝ`, evaluating entries along
`CircleRing.evalGL : GL (Fin N) (CircleRing ℝ) →* C(Circle, GL (Fin N) ℝ)` sends any stabilized
elementary matrix to a based nullhomotopic loop
(`CircleRing.evalGL_homotopicRel_one_of_mem_elementarySubgroup`),
whereas the stabilized rotation matrix evaluates to the rotation loop
`TauCeti.circleRotationLoop`, which is not based nullhomotopic
(`TauCeti.not_homotopicRel_circleRotationLoop_const`). Base change along `k →+* ℝ` then
propagates nonvanishing from `ℝ` to `k`.

## Main definitions

* `TauCeti.circleRotation`: the determinant-one rotation matrix `!![x, -y; y, x]` over
  `CircleRing k`.

## Main results

* `TauCeti.circleRotation_mul_transpose`: `circleRotation k` is algebraically orthogonal.
* `TauCeti.map_circleRotation`: base change on `CircleRing` preserves `circleRotation`.
* `TauCeti.circleRotation_notMem_elementarySubgroup`: no stabilization of `circleRotation k` is
  elementary when `k` admits `k →+* ℝ`.
* `TauCeti.circle_rotation_not_stably_elementary`: the class of `circleRotation k` in
  `TauCeti.AlgebraicK1 (CircleRing k)` is nontrivial when `k` admits `k →+* ℝ`.
* `TauCeti.specialAlgebraicK1_circleRing_ne_bot`: `SK₁(CircleRing k) ≠ ⊥` when `k` admits `k →+* ℝ`.
* `TauCeti.not_det_circleRing_injective`: the determinant
  `K₁(CircleRing k) →* (CircleRing k)ˣ` is not injective when `k` admits `k →+* ℝ`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Example 1.5.4 (p. 185).
-/

public section

open Matrix

namespace TauCeti

noncomputable section

/-! ## The circle rotation matrix -/

section CircleRotation

variable (k : Type*) [CommRing k]

/-- The determinant-one rotation matrix `!![x, -y; y, x]` over the coordinate ring of the
algebraic circle over `k`. -/
def circleRotation : Matrix.SpecialLinearGroup (Fin 2) (CircleRing k) :=
  ⟨!![CircleRing.x, -CircleRing.y; CircleRing.y, CircleRing.x], by
    rw [Matrix.det_fin_two_of]
    linear_combination CircleRing.x_sq_add_y_sq (k := k)⟩

variable {k}

/-- Entry `(0, 0)` of `circleRotation k` is `x`. -/
@[simp]
theorem circleRotation_apply_zero_zero :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 0 0 = CircleRing.x :=
  (rfl)

/-- Entry `(0, 1)` of `circleRotation k` is `-y`. -/
@[simp]
theorem circleRotation_apply_zero_one :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 0 1 = -CircleRing.y :=
  (rfl)

/-- Entry `(1, 0)` of `circleRotation k` is `y`. -/
@[simp]
theorem circleRotation_apply_one_zero :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 1 0 = CircleRing.y :=
  (rfl)

/-- Entry `(1, 1)` of `circleRotation k` is `x`. -/
@[simp]
theorem circleRotation_apply_one_one :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) 1 1 = CircleRing.x :=
  (rfl)

/-- `circleRotation k` is algebraically orthogonal over `CircleRing k`. -/
theorem circleRotation_mul_transpose :
    (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) *
      (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k))ᵀ = 1 := by
  have hT : (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k))ᵀ =
      adjugate (circleRotation k : Matrix (Fin 2) (Fin 2) (CircleRing k)) := by
    change !![CircleRing.x, -CircleRing.y; CircleRing.y, CircleRing.x]ᵀ =
      adjugate !![CircleRing.x, -CircleRing.y; CircleRing.y, CircleRing.x]
    rw [Matrix.adjugate_fin_two_of, neg_neg]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hT, Matrix.mul_adjugate, (circleRotation k).prop, one_smul]

end CircleRotation

/-! ## Nonvanishing in algebraic `K₁` and `SK₁` -/

private theorem evalGL_stabilizeGL_circleRotation (N : ℕ) (hN : 2 ≤ N) :
    CircleRing.evalGL (stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ))) =
      circleRotationLoop hN := by
  ext1 z
  let φ : CircleRing ℝ →+* ℝ :=
    ((ContinuousMap.evalAlgHom ℝ ℝ z).comp CircleRing.evalCircle).toRingHom
  have heval : CircleRing.evalGL
        (stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ))) z =
      Units.map φ.mapMatrix.toMonoidHom
        (stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ))) := by
    ext i j
    simp [φ]
  rw [heval, ← stabilizeGL_map, circleRotationLoop_apply]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [φ, coe_unitsLeftMulMatrix, Algebra.leftMulMatrix_complex]

private theorem circleRotation_notMem_elementarySubgroup_real (N : ℕ) (hN : 2 ≤ N) :
    stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ)) ∉
      elementarySubgroup (Fin N) (CircleRing ℝ) := by
  intro hg
  have h1 : CircleRing.evalGL
      (stabilizeGL (CircleRing ℝ) hN (SpecialLinearGroup.toGL (circleRotation ℝ))) 1 = 1 := by
    rw [evalGL_stabilizeGL_circleRotation, circleRotationLoop_one]
  have hnull := CircleRing.evalGL_homotopicRel_one_of_mem_elementarySubgroup hg h1
  rw [evalGL_stabilizeGL_circleRotation] at hnull
  exact not_homotopicRel_circleRotationLoop_const hN hnull

private theorem circle_rotation_not_stably_elementary_real :
    AlgebraicK1.mk (CircleRing ℝ) 2 (SpecialLinearGroup.toGL (circleRotation ℝ)) ≠ 1 := by
  rw [ne_eq, AlgebraicK1.mk_eq_one_iff]
  rintro ⟨N, hN, hmem⟩
  exact circleRotation_notMem_elementarySubgroup_real N hN hmem

/-- Base change along `f : k →+* S` carries `circleRotation k` to `circleRotation S`. -/
@[simp]
theorem map_circleRotation {k S : Type*} [CommRing k] [CommRing S] (f : k →+* S) :
    SpecialLinearGroup.map (CircleRing.map f) (circleRotation k) = circleRotation S := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The circle rotation has nontrivial class in algebraic `K₁`**: for any commutative ring
`k` admitting a ring homomorphism `k →+* ℝ` (such as `ℤ`, `ℚ`, or `ℝ`), `circleRotation k`
represents a nontrivial class in `SK₁(CircleRing k)`. -/
theorem circle_rotation_not_stably_elementary {k : Type*} [CommRing k] (f : k →+* ℝ) :
    AlgebraicK1.mk (CircleRing k) 2 (SpecialLinearGroup.toGL (circleRotation k)) ≠ 1 := by
  intro h
  apply circle_rotation_not_stably_elementary_real
  have hmap := congrArg (AlgebraicK1.map (CircleRing.map f)) h
  rw [AlgebraicK1.map_mk, map_one] at hmap
  change AlgebraicK1.mk (CircleRing ℝ) 2
      (GeneralLinearGroup.map (CircleRing.map f) (SpecialLinearGroup.toGL (circleRotation k))) = 1
    at hmap
  rwa [← SpecialLinearGroup.toGL_map, map_circleRotation f] at hmap

/-- **No identity stabilization of `circleRotation k` is elementary** when `k` admits a ring
homomorphism `k →+* ℝ`. -/
theorem circleRotation_notMem_elementarySubgroup {k : Type*} [CommRing k] (f : k →+* ℝ)
    (N : ℕ) (hN : 2 ≤ N) :
    stabilizeGL (CircleRing k) hN (SpecialLinearGroup.toGL (circleRotation k)) ∉
      elementarySubgroup (Fin N) (CircleRing k) := by
  intro hmem
  exact circle_rotation_not_stably_elementary f (AlgebraicK1.mk_eq_one_iff.2 ⟨N, hN, hmem⟩)

/-- `SK₁(CircleRing k)` is nontrivial whenever `k` admits a ring homomorphism `k →+* ℝ`: even
for a Dedekind domain such as `CircleRing ℚ` or `CircleRing ℝ`, `SK₁` need not vanish. -/
theorem specialAlgebraicK1_circleRing_ne_bot {k : Type*} [CommRing k] (f : k →+* ℝ) :
    specialAlgebraicK1 (CircleRing k) ≠ ⊥ := by
  intro hbot
  have hmem : AlgebraicK1.mk (CircleRing k) 2 (SpecialLinearGroup.toGL (circleRotation k)) ∈
      specialAlgebraicK1 (CircleRing k) :=
    AlgebraicK1.mk_mem_specialAlgebraicK1_iff.2 (SpecialLinearGroup.coeToGL_det _)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact circle_rotation_not_stably_elementary f hmem

/-- The determinant homomorphism `K₁(CircleRing k) →* (CircleRing k)ˣ` is not injective
whenever `k` admits a ring homomorphism `k →+* ℝ`. -/
theorem not_det_circleRing_injective {k : Type*} [CommRing k] (f : k →+* ℝ) :
    ¬ Function.Injective (AlgebraicK1.det (CircleRing k)) := fun h ↦
  specialAlgebraicK1_circleRing_ne_bot f <|
    (Subgroup.eq_bot_iff_forall _).2 fun x hx ↦
      h (by rw [mem_specialAlgebraicK1_iff.1 hx, map_one])

end

end TauCeti
