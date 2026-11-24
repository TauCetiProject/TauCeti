/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.Quaternion.ComplexMatrix` supplies `Quaternion.toComplexMatrix` and the
-- identification `Quaternion.unitaryEquivSpecialUnitaryGroup` of the unit quaternions with `SU(2)`.
public import TauCeti.Algebra.Quaternion.ComplexMatrix
-- `TauCeti.Analysis.Matrix.UnitaryGroup.Basic` supplies the decomposition `U(n) = Circle · SU(n)`
-- (`Matrix.exists_circle_smul_mem_specialUnitaryGroup`) and `Circle.coe_mem_unitary`.
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# `U(2)` from unit quaternions and the circle

Through the embedding `Quaternion.toComplexMatrix : ℍ[ℝ] →⋆ₐ[ℝ] M₂(ℂ)`, the unit quaternions are
`SU(2)` (`Quaternion.unitaryEquivSpecialUnitaryGroup`). Multiplying by scalars of modulus one then
presents the whole unitary group: the homomorphism
`Quaternion.unitaryProdCircleToUnitaryGroup : Sp(1) × U(1) → U(2)`, `(q, w) ↦ w • q`, is onto
(`U(2) = Circle · SU(2)`) with kernel `{(1, 1), (-1, -1)}`, so
`U(2) ≅ (Sp(1) × U(1)) / {±1}`.

This is the quaternionic form, for `n = 2`, of the cover `S¹ × SU(n) → U(n)` of
`TauCeti/Analysis/Matrix/UnitaryGroup/CircleCover.lean`, with `SU(2)` replaced by the unit
quaternions.

## Main definitions

* `Quaternion.circleToUnitary`: the circle as the unit quaternions of the complex line.
* `Quaternion.unitaryProdCircleToUnitaryGroup`: the homomorphism `Sp(1) × U(1) → U(2)`,
  `(q, w) ↦ w • q`.

## Main results

* `Quaternion.unitaryProdCircleToUnitaryGroup_surjective` and
  `Quaternion.mem_ker_unitaryProdCircleToUnitaryGroup_iff`: `Sp(1) × U(1) → U(2)` is onto with
  kernel `{1, -1}`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
-/

public section

open scoped Matrix Quaternion

namespace Quaternion

/-- The circle as the unit quaternions of the complex line `ℝ ⊕ ℝ i`. -/
noncomputable def circleToUnitary : Circle →* unitary ℍ[ℝ] where
  toFun w := ⟨((w : ℂ) : ℍ[ℝ]), by
    rw [mem_unitary_iff_normSq_eq_one, normSq_def']
    simpa [sq] using Circle.re_sq_add_im_sq w⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)

/-- The unit quaternion `circleToUnitary w` is the complex number `w`. -/
@[simp]
theorem coe_circleToUnitary (w : Circle) :
    (circleToUnitary w : ℍ[ℝ]) = ((w : ℂ) : ℍ[ℝ]) :=
  (rfl)

/-! ### `U(2)` as a quotient of `Sp(1) × U(1)` -/

/-- **`U(2)` from unit quaternions and the circle.** The homomorphism `Sp(1) × U(1) → U(2)`,
`(q, w) ↦ w • toComplexMatrix q`. It is onto (`unitaryProdCircleToUnitaryGroup_surjective`) with
kernel `{1, -1}` (`mem_ker_unitaryProdCircleToUnitaryGroup_iff`). -/
noncomputable def unitaryProdCircleToUnitaryGroup :
    unitary ℍ[ℝ] × Circle →* Matrix.unitaryGroup (Fin 2) ℂ where
  toFun p := ⟨(p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ]),
    Unitary.smul_mem_of_mem p.2.coe_mem_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup
        (mem_specialUnitaryGroup_toComplexMatrix p.1.property))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' p q := Subtype.ext (by
    simp only [Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, Circle.coe_mul, map_mul]
    rw [smul_mul_smul_comm])

/-- The matrix of `unitaryProdCircleToUnitaryGroup (q, w)` is `w • toComplexMatrix q`. -/
@[simp]
theorem coe_unitaryProdCircleToUnitaryGroup_apply (p : unitary ℍ[ℝ] × Circle) :
    (unitaryProdCircleToUnitaryGroup p : Matrix (Fin 2) (Fin 2) ℂ) =
      (p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ]) :=
  (rfl)

/-- **`U(2) = U(1) · Sp(1)`.** Every unitary matrix of degree two is a scalar of modulus one times
the matrix of a unit quaternion. -/
theorem unitaryProdCircleToUnitaryGroup_surjective :
    Function.Surjective unitaryProdCircleToUnitaryGroup := by
  intro g
  obtain ⟨c, hc⟩ := Matrix.exists_circle_smul_mem_specialUnitaryGroup g
  refine ⟨(unitaryEquivSpecialUnitaryGroup.symm ⟨_, hc⟩, c⁻¹), Subtype.ext ?_⟩
  rw [coe_unitaryProdCircleToUnitaryGroup_apply, coe_unitaryEquivSpecialUnitaryGroup_symm_apply,
    smul_smul, Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_smul]

/-- **The kernel of `Sp(1) × U(1) → U(2)` is `{1, -1}`**: `w • q = 1` forces `q = w⁻¹` to be a real
unit quaternion. -/
theorem mem_ker_unitaryProdCircleToUnitaryGroup_iff {p : unitary ℍ[ℝ] × Circle} :
    p ∈ unitaryProdCircleToUnitaryGroup.ker ↔ p = 1 ∨ p = -1 := by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨⟨a, ha⟩, w⟩ := p
    have hm : (w : ℂ) • toComplexMatrix a = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
    -- Taking determinants gives `w ^ 2 = 1`; then `toComplexMatrix a = w • 1` forces `a = w`.
    have hw : (w : ℂ) ^ 2 = 1 := by
      simpa [Matrix.det_smul, (mem_unitary_iff_normSq_eq_one a).mp ha] using
        congrArg Matrix.det hm
    rcases sq_eq_one_iff.mp hw with h | h
    · refine Or.inl (Prod.ext (Subtype.ext (toComplexMatrix_injective ?_)) (Circle.ext h))
      simpa [h] using hm
    · refine Or.inr (Prod.ext (Subtype.ext (toComplexMatrix_injective ?_)) (Circle.ext ?_))
      · simpa [h, Unitary.coe_neg, neg_eq_iff_eq_neg] using hm
      · simpa using h
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
      simp [Unitary.coe_neg]

end Quaternion

end
