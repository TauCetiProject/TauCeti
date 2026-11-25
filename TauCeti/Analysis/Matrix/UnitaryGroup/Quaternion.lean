/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.Quaternion.ComplexMatrix` supplies `Quaternion.toComplexMatrix` and the
-- identification `Quaternion.unitaryEquivSpecialUnitaryGroup` of the unit quaternions with `SU(2)`.
public import TauCeti.Algebra.Quaternion.ComplexMatrix
-- `TauCeti.Analysis.Matrix.UnitaryGroup.CircleCover` supplies the cover
-- `TauCeti.circleProdSpecialUnitary : S¹ × SU(n) →* U(n)`, its surjectivity and its kernel.
public import TauCeti.Analysis.Matrix.UnitaryGroup.CircleCover

/-!
# `U(2)` from unit quaternions and the circle

Through the embedding `Quaternion.toComplexMatrix : ℍ[ℝ] →⋆ₐ[ℝ] M₂(ℂ)`, the unit quaternions are
`SU(2)` (`Quaternion.unitaryEquivSpecialUnitaryGroup`). Multiplying by scalars of modulus one then
presents the whole unitary group: the homomorphism
`Quaternion.unitaryProdCircleToUnitaryGroup : Sp(1) × U(1) → U(2)`, `(q, w) ↦ w • q`, is onto
(`U(2) = Circle · SU(2)`) with kernel `{(1, 1), (-1, -1)}`, so
`U(2) ≅ (Sp(1) × U(1)) / {±1}`.

This is the quaternionic form, for `n = 2`, of the cover `TauCeti.circleProdSpecialUnitary :
S¹ × SU(n) → U(n)` of `TauCeti/Analysis/Matrix/UnitaryGroup/CircleCover.lean`, with `SU(2)`
replaced by the unit quaternions: the homomorphism is defined as that cover precomposed with
`Quaternion.unitaryEquivSpecialUnitaryGroup`, and its surjectivity and kernel are read off from the
cover's.

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
    unitary ℍ[ℝ] × Circle →* Matrix.unitaryGroup (Fin 2) ℂ :=
  TauCeti.circleProdSpecialUnitary.comp
    ((MonoidHom.snd _ _).prod
      (unitaryEquivSpecialUnitaryGroup.toMonoidHom.comp (MonoidHom.fst _ _)))

/-- The matrix of `unitaryProdCircleToUnitaryGroup (q, w)` is `w • toComplexMatrix q`. -/
@[simp]
theorem coe_unitaryProdCircleToUnitaryGroup_apply (p : unitary ℍ[ℝ] × Circle) :
    (unitaryProdCircleToUnitaryGroup p : Matrix (Fin 2) (Fin 2) ℂ) =
      (p.2 : ℂ) • toComplexMatrix (p.1 : ℍ[ℝ]) :=
  (TauCeti.coe_circleProdSpecialUnitary_apply _).trans
    (congrArg _ (coe_unitaryEquivSpecialUnitaryGroup_apply p.1))

/-- **`U(2) = U(1) · Sp(1)`.** Every unitary matrix of degree two is a scalar of modulus one times
the matrix of a unit quaternion. -/
theorem unitaryProdCircleToUnitaryGroup_surjective :
    Function.Surjective unitaryProdCircleToUnitaryGroup :=
  TauCeti.circleProdSpecialUnitary_surjective.comp fun p =>
    ⟨(unitaryEquivSpecialUnitaryGroup.symm p.2, p.1),
      Prod.ext rfl (unitaryEquivSpecialUnitaryGroup.apply_symm_apply p.2)⟩

/-- **The kernel of `Sp(1) × U(1) → U(2)` is `{1, -1}`**: `w • q = 1` forces `q = w⁻¹` to be a real
unit quaternion. -/
theorem mem_ker_unitaryProdCircleToUnitaryGroup_iff {p : unitary ℍ[ℝ] × Circle} :
    p ∈ unitaryProdCircleToUnitaryGroup.ker ↔ p = 1 ∨ p = -1 := by
  refine ⟨fun hp => ?_, ?_⟩
  · obtain ⟨q, w⟩ := p
    -- In the cover `S¹ × SU(2) → U(2)` the point `(w, q)` of the kernel has `q = w⁻¹` and
    -- `w ^ 2 = 1`, so `w = ±1` and `q = w`.
    have hp' : (w, unitaryEquivSpecialUnitaryGroup q) ∈ TauCeti.circleProdSpecialUnitary.ker := hp
    have hm : toComplexMatrix (q : ℍ[ℝ]) = ((w⁻¹ : Circle) : ℂ) • 1 :=
      (coe_unitaryEquivSpecialUnitaryGroup_apply q).symm.trans
        ((TauCeti.mem_ker_circleProdSpecialUnitary_iff _).1 hp')
    have hw : (w : ℂ) ^ 2 = 1 := by
      simpa using congrArg ((↑) : Circle → ℂ)
        (TauCeti.pow_card_eq_one_of_mem_ker_circleProdSpecialUnitary hp')
    rcases sq_eq_one_iff.mp hw with h | h
    · refine Or.inl (Prod.ext (Subtype.ext (toComplexMatrix_injective ?_)) (Circle.ext h))
      simpa [h] using hm
    · refine Or.inr (Prod.ext (Subtype.ext (toComplexMatrix_injective ?_)) (Circle.ext ?_))
      · simpa [h, Unitary.coe_neg] using hm
      · simpa using h
  · rintro (rfl | rfl)
    · exact one_mem _
    · refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
      simp [Unitary.coe_neg]

end Quaternion

end
