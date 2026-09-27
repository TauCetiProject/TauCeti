/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.DetSquareClass
public import Mathlib.Basic.Real.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.SpecialOrthogonal
import TauCeti.FieldTheory.SquareClassGroup.Real

/-!
# The spinor norm of a real quadratic form

Over `ℝ` the square-class group `ℝˣ/(ℝˣ)²` has exactly two elements, by
`TauCeti.eq_one_or_eq_squareClassHom_neg_one`, so on `O(Q)` the image of the spinor norm is read
off the sign of a single reflection. A reflection is never an element of `SO(Q)`, since it has
determinant `-1`, so on `SO(Q)` the nontrivial class is instead witnessed by the product of a
reflection in a vector of negative value with a reflection in a vector of positive value, which has
determinant one.

For a positive definite form every invertible value is a positive real number, hence a square, so
`orthogonalSpinorNorm_eq_one_of_posDef` makes the orthogonal spinor norm trivial and
`spinorNorm_eq_one_of_posDef` restricts it to `SO(Q)`. A negative definite form takes negative
values on every nonzero vector, so a reflection contributes the square class of `-1`, which is
also the determinant square class of a reflection: the two maps agree, and the spinor norm on
`SO(Q)` is trivial since every isometry of `SO(Q)` has determinant one.

As soon as the form takes a negative value the spinor norm on `O(Q)` is surjective, and an
indefinite form, which takes values of both signs, has surjective spinor norm on `SO(Q)` as well.

## Main results

* `CliffordAlgebra.spinorNorm_eq_one_of_posDef`: the positive definite case on `SO(Q)`.
* `CliffordAlgebra.orthogonalSpinorNorm_eq_orthogonalDetSquareClass_of_negDef` and
  `CliffordAlgebra.spinorNorm_eq_one_of_negDef`: the negative definite case, the determinant square
  class on `O(Q)` and the trivial map on `SO(Q)`.
* `CliffordAlgebra.orthogonalSpinorNorm_surjective_of_negValue` and
  `CliffordAlgebra.spinorNorm_surjective_of_indefinite`: surjectivity on `O(Q)` as soon as the form
  takes a negative value, and on `SO(Q)` for an indefinite form.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.

Together the results describe the real square-class image of both spinor norms: on `O(Q)` it is
trivial for a positive definite form, the determinant square class for a negative definite form,
and everything as soon as the form takes a negative value, while on `SO(Q)` it is trivial for a
definite form and everything for an indefinite form. The split by signature is the point: on
`SO(Q)` the image of a definite form of positive dimension is not all square classes, whereas on
`O(Q)` a negative definite form of positive dimension already has full image, because it takes a
negative value.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe v

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- A negative definite form takes strictly negative values on every invertible value. -/
private theorem lt_neg_of_negPosDef_invertible {Q : QuadraticForm ℝ V} (hneg : (-Q).PosDef)
    {v : V} [Invertible (Q v)] : Q v < 0 := by
  have hne : Q v ≠ 0 := isUnit_iff_ne_zero.mp (isUnit_of_invertible (Q v))
  have hv0 : v ≠ 0 := fun hv => hne (by simp [hv])
  have h : 0 < -(Q v) := by simpa only [neg_apply] using hneg v hv0
  linarith

omit [FiniteDimensional ℝ V] in
/-- The square class of the unit of a negative real value is the class of `-1`. -/
private theorem squareClass_eq_neg_one_of_lt_zero {Q : QuadraticForm ℝ V} {v : V}
    [Invertible (Q v)] (hv : Q v < 0) :
    squareClass (unitOfInvertible (Q v) : ℝˣ) = squareClass (-1 : ℝˣ) :=
  (_root_.Units.squareClass_eq_squareClass_neg_one_iff_neg _).mpr (by simpa using hv)

private theorem orthogonalSpinorNorm_reflection_eq_neg_one (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) {v : V} [Invertible (Q v)] (hv : Q v < 0) :
    orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v)
      = squareClassHom (-1 : ℝˣ) := by
  rw [orthogonalSpinorNorm_reflectionOrthogonal, squareClassHom_apply, squareClassHom_apply,
    squareClass_eq_neg_one_of_lt_zero hv]

private theorem orthogonalSpinorNorm_reflection_eq_one_of_pos (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) {v : V} [Invertible (Q v)] (hv : 0 < Q v) :
    orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v) = 1 := by
  rw [orthogonalSpinorNorm_reflectionOrthogonal, squareClassHom_apply,
    (_root_.Units.squareClass_eq_zero_iff_pos (unitOfInvertible (Q v))).mpr (by simpa using hv)]
  rfl

/-- The spinor norm of a positive definite real quadratic form is trivial on its special
orthogonal group. -/
@[simp]
theorem spinorNorm_eq_one_of_posDef (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    spinorNorm Q hQ.anisotropic.nondegenerate = 1 := by
  refine MonoidHom.ext fun g ↦ ?_
  rw [spinorNorm_apply, orthogonalSpinorNorm_eq_one_of_posDef Q hQ]
  simp only [MonoidHom.one_apply]

/-- For a negative definite real quadratic form the spinor norm on `O(Q)` is the square class of
the determinant, which is trivial on the isometries of determinant one. -/
@[simp]
theorem orthogonalSpinorNorm_eq_orthogonalDetSquareClass_of_negDef (Q : QuadraticForm ℝ V)
    (hneg : (-Q).PosDef) :
    orthogonalSpinorNorm Q ((QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate)
      = QuadraticMap.orthogonalDetSquareClass Q := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hQ : Q.Nondegenerate :=
    (QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate
  refine QuadraticMap.orthogonalGroup_hom_ext Q hQ fun v _ ↦ ?_
  rw [orthogonalSpinorNorm_reflectionOrthogonal, QuadraticMap.orthogonalDetSquareClass_apply,
    squareClassHom_apply, QuadraticMap.coe_reflectionOrthogonal, QuadraticMap.det_reflection,
    squareClassHom_apply, squareClass_eq_neg_one_of_lt_zero (lt_neg_of_negPosDef_invertible hneg)]

/-- The spinor norm of a negative definite real quadratic form is trivial on `SO(Q)`, where every
isometry has determinant one. -/
@[simp]
theorem spinorNorm_eq_one_of_negDef (Q : QuadraticForm ℝ V) (hneg : (-Q).PosDef) :
    spinorNorm Q ((QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate) = 1 := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  refine MonoidHom.ext fun g ↦ ?_
  rw [spinorNorm_apply, orthogonalSpinorNorm_eq_orthogonalDetSquareClass_of_negDef Q hneg,
    QuadraticMap.orthogonalDetSquareClass_apply, coe_specialOrthogonalToOrthogonal,
    (QuadraticMap.mem_specialOrthogonalGroup_iff.mp g.2).2, map_one]
  simp only [MonoidHom.one_apply]

/-- The spinor norm of a real quadratic form taking a negative value is surjective on `O(Q)`.
This holds in particular for a negative definite form of positive dimension and for an indefinite
form. -/
theorem orthogonalSpinorNorm_surjective_of_negValue (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
    (hneg : ∃ v, Q v < 0) : Function.Surjective (orthogonalSpinorNorm Q hQ) := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := hneg
  let _ : Invertible (Q v) := (isUnit_iff_ne_zero.mpr (ne_of_lt hv)).invertible
  have hval : orthogonalSpinorNorm Q hQ (QuadraticMap.reflectionOrthogonal Q v)
      = squareClassHom (-1 : ℝˣ) := orthogonalSpinorNorm_reflection_eq_neg_one Q hQ hv
  intro x
  rcases eq_one_or_eq_squareClassHom_neg_one x with h | h
  · exact ⟨1, by rw [h, map_one]⟩
  · exact ⟨QuadraticMap.reflectionOrthogonal Q v, by rw [h, hval]⟩

/-- The spinor norm of an indefinite real quadratic form is surjective on `SO(Q)`, so every square
class is the spinor norm of a determinant-one isometry. -/
theorem spinorNorm_surjective_of_indefinite (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
    (hpos : ∃ v, 0 < Q v) (hneg : ∃ v, Q v < 0) : Function.Surjective (spinorNorm Q hQ) := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := hneg
  obtain ⟨w, hw⟩ := hpos
  let _ : Invertible (Q v) := (isUnit_iff_ne_zero.mpr (ne_of_lt hv)).invertible
  let _ : Invertible (Q w) := (isUnit_iff_ne_zero.mpr (ne_of_gt hw)).invertible
  have hval : orthogonalSpinorNorm Q hQ
      (QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w)
      = squareClassHom (-1 : ℝˣ) := by
    rw [map_mul, orthogonalSpinorNorm_reflection_eq_neg_one Q hQ hv,
      orthogonalSpinorNorm_reflection_eq_one_of_pos Q hQ hw]
    exact mul_one (squareClassHom (-1 : ℝˣ))
  intro x
  rcases eq_one_or_eq_squareClassHom_neg_one x with h | h
  · refine ⟨1, ?_⟩
    rw [h]
    exact MonoidHom.map_one (spinorNorm Q hQ)
  · have hso : ((QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w :
        QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ℝ] V) ∈ QuadraticMap.specialOrthogonalGroup Q := by
      rw [QuadraticMap.mem_specialOrthogonalGroup_iff]
      refine ⟨(QuadraticMap.orthogonalGroup Q).mul_mem
        (by simpa only [QuadraticMap.coe_reflectionOrthogonal] using
          QuadraticMap.reflection_mem_orthogonalGroup Q v)
        (by simpa only [QuadraticMap.coe_reflectionOrthogonal] using
          QuadraticMap.reflection_mem_orthogonalGroup Q w), by simp⟩
    -- `specialOrthogonalToOrthogonal` is the identity on the ambient linear isomorphism, so this
    -- witness is the product of the two reflections.
    have hkey : specialOrthogonalToOrthogonal Q
        ⟨(QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w :
          V ≃ₗ[ℝ] V), hso⟩ = QuadraticMap.reflectionOrthogonal Q v
            * QuadraticMap.reflectionOrthogonal Q w := by
      refine Subtype.ext ?_
      rw [coe_specialOrthogonalToOrthogonal]
      rfl
    refine ⟨⟨(QuadraticMap.reflectionOrthogonal Q v * QuadraticMap.reflectionOrthogonal Q w :
      V ≃ₗ[ℝ] V), hso⟩, ?_⟩
    rw [spinorNorm_apply, hkey, h, hval]

end CliffordAlgebra
