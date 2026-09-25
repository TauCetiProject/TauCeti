/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

/-!
# The compact three-dimensional even Clifford algebra

The even Clifford algebra of the positive-definite real form in dimension three is the Hamilton
quaternion algebra. Under this identification, Clifford reversal is quaternion conjugation, so
the reverse norm is the quaternion norm-square.

The construction follows the standard reductions
`Cl⁺(3,0) ≃ Cl⁺(0,3) ≃ Cl(0,2) ≃ ℍ`: first negate the form, then split off one negative line,
apply the even-algebra dimension reduction, and finally use the explicit `(0,2)` quaternion
model.

## Main definitions and results

* `TauCeti.realCliffordThreeZeroEvenEquivQuaternion` identifies `Cl⁺(3,0)` with `ℍ[ℝ]`.
* `TauCeti.realCliffordThreeZeroEvenEquivQuaternion_reverseEven` identifies reversal with
  quaternion conjugation.
* The three `..._bivector_*` theorems identify the coordinate bivectors with the imaginary
  quaternion basis.
* `TauCeti.realCliffordThreeZeroEvenEquivQuaternion_reverseEven_mul_self` identifies the reverse
  norm with the quaternion norm-square.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §4; see in particular
  the reversal convention and the low-dimensional real Clifford-algebra table.
-/

public section

open QuadraticMap
open scoped Quaternion

namespace TauCeti

private noncomputable def realCliffordZeroThreeAugmentedIsometry :
    (realCliffordForm 0 3).IsometryEquiv
      (CliffordAlgebra.EquivEven.Q' (realCliffordForm 0 2)) :=
  (realCliffordSplitIsometry 0 0 2 1).trans
    ((QuadraticMap.IsometryEquiv.refl (realCliffordForm 0 2)).prod
      realCliffordZeroOneIsometry)

@[simp]
private theorem realCliffordFormNegIsometry_three_zero_basis (i : Fin 3) :
    realCliffordFormNegIsometry 3 0 (Pi.single i 1) = Pi.single i 1 := by
  funext j
  simpa using realCliffordFormNegIsometry_neg_of_pos 3 0 (Pi.single i 1) j

@[simp]
private theorem realCliffordZeroThreeAugmentedIsometry_basis_zero :
    realCliffordZeroThreeAugmentedIsometry (Pi.single 0 1) =
      (Pi.single 0 1, 0) := by
  classical
  apply Prod.ext
  · funext i
    change (realCliffordSplitIsometry 0 0 2 1 (Pi.single 0 1)).1 i = _
    convert realCliffordSplitIsometry_fst_neg 0 0 2 1 (Pi.single 0 1) i using 1
    all_goals fin_cases i <;> simp
  · change realCliffordZeroOneIsometry
        (realCliffordSplitIsometry 0 0 2 1 (Pi.single 0 1)).2 = 0
    rw [realCliffordZeroOneIsometry_apply]
    convert realCliffordSplitIsometry_snd_neg 0 0 2 1 (Pi.single 0 1) (0 : Fin 1)
      using 1 <;> simp

@[simp]
private theorem realCliffordZeroThreeAugmentedIsometry_basis_one :
    realCliffordZeroThreeAugmentedIsometry (Pi.single 1 1) =
      (Pi.single 1 1, 0) := by
  classical
  apply Prod.ext
  · funext i
    change (realCliffordSplitIsometry 0 0 2 1 (Pi.single 1 1)).1 i = _
    convert realCliffordSplitIsometry_fst_neg 0 0 2 1 (Pi.single 1 1) i using 1
    all_goals fin_cases i <;> simp
  · change realCliffordZeroOneIsometry
        (realCliffordSplitIsometry 0 0 2 1 (Pi.single 1 1)).2 = 0
    rw [realCliffordZeroOneIsometry_apply]
    convert realCliffordSplitIsometry_snd_neg 0 0 2 1 (Pi.single 1 1) (0 : Fin 1)
      using 1 <;> simp

@[simp]
private theorem realCliffordZeroThreeAugmentedIsometry_basis_two :
    realCliffordZeroThreeAugmentedIsometry (Pi.single 2 1) =
      (0, 1) := by
  classical
  apply Prod.ext
  · funext i
    change (realCliffordSplitIsometry 0 0 2 1 (Pi.single 2 1)).1 i = 0
    convert realCliffordSplitIsometry_fst_neg 0 0 2 1 (Pi.single 2 1) i using 1
    all_goals fin_cases i <;> simp
  · change realCliffordZeroOneIsometry
        (realCliffordSplitIsometry 0 0 2 1 (Pi.single 2 1)).2 = 1
    rw [realCliffordZeroOneIsometry_apply]
    convert realCliffordSplitIsometry_snd_neg 0 0 2 1 (Pi.single 2 1) (0 : Fin 1)
      using 1 <;> simp

/-- The even Clifford algebra of the positive-definite three-dimensional real form is the
Hamilton quaternion algebra. -/
noncomputable def realCliffordThreeZeroEvenEquivQuaternion :
    CliffordAlgebra.even (realCliffordForm 3 0) ≃ₐ[ℝ] ℍ[ℝ] :=
  (CliffordAlgebra.evenEquivEvenNeg (realCliffordForm 3 0)).trans
    ((CliffordAlgebra.evenEquivOfIsometry (realCliffordFormNegIsometry 3 0)).trans
      ((CliffordAlgebra.evenEquivOfIsometry realCliffordZeroThreeAugmentedIsometry).trans
        ((CliffordAlgebra.equivEven (realCliffordForm 0 2)).symm.trans
          realCliffordZeroTwoEquivQuaternion)))

/-- The coordinate bivector `e₀e₁` maps to `-k`. -/
theorem realCliffordThreeZeroEvenEquivQuaternion_bivector_zero_one :
    realCliffordThreeZeroEvenEquivQuaternion
        ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin
          (Pi.single 0 1) (Pi.single 1 1)) = (⟨0, 0, 0, -1⟩ : ℍ[ℝ]) := by
  classical
  simp only [realCliffordThreeZeroEvenEquivQuaternion, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_apply, CliffordAlgebra.evenToNeg_ι]
  simp

/-- The coordinate bivector `e₁e₂` maps to `j`. -/
theorem realCliffordThreeZeroEvenEquivQuaternion_bivector_one_two :
    realCliffordThreeZeroEvenEquivQuaternion
        ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin
          (Pi.single 1 1) (Pi.single 2 1)) = (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) := by
  classical
  simp only [realCliffordThreeZeroEvenEquivQuaternion, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_apply, CliffordAlgebra.evenToNeg_ι]
  simp

/-- The coordinate bivector `e₂e₀` maps to `-i`. -/
theorem realCliffordThreeZeroEvenEquivQuaternion_bivector_two_zero :
    realCliffordThreeZeroEvenEquivQuaternion
        ((CliffordAlgebra.even.ι (realCliffordForm 3 0)).bilin
          (Pi.single 2 1) (Pi.single 0 1)) = (⟨0, -1, 0, 0⟩ : ℍ[ℝ]) := by
  classical
  simp only [realCliffordThreeZeroEvenEquivQuaternion, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_apply, CliffordAlgebra.evenToNeg_ι]
  simp

/-- In the compact three-dimensional quaternion model, Clifford reversal is quaternion
conjugation. -/
@[simp]
theorem realCliffordThreeZeroEvenEquivQuaternion_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 3 0)) :
    realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.reverseEven (realCliffordForm 3 0) x) =
      star (realCliffordThreeZeroEvenEquivQuaternion x) := by
  simp only [realCliffordThreeZeroEvenEquivQuaternion, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivEvenNeg_reverseEven,
    CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.equivEven_symm_reverseEven,
    realCliffordZeroTwoEquivQuaternion_star]

/-- The reverse norm in the compact three-dimensional even Clifford algebra is the quaternion
norm-square. -/
@[simp]
theorem realCliffordThreeZeroEvenEquivQuaternion_reverseEven_mul_self
    (x : CliffordAlgebra.even (realCliffordForm 3 0)) :
    realCliffordThreeZeroEvenEquivQuaternion
        (CliffordAlgebra.reverseEven (realCliffordForm 3 0) x * x) =
      Quaternion.normSq (realCliffordThreeZeroEvenEquivQuaternion x) := by
  rw [map_mul, realCliffordThreeZeroEvenEquivQuaternion_reverseEven,
    Quaternion.star_mul_self]

end TauCeti

end
