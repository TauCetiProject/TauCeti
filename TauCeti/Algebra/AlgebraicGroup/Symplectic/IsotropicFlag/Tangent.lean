/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.WeightParabolic.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Differential

/-!
# Positive symplectic root vectors in the isotropic flag Lie algebra

The Lie algebra of the standard complete isotropic flag stabilizer consists of symplectic
matrices upper triangular in the self-dual flag order. A normalized root vector belongs to
it exactly when its root is positive for the standard type-C base. The criterion works over
arbitrary nontrivial coefficient algebras, including characteristic two and nonreduced rings.
It identifies which represented root-subgroup differentials lie in the flag Lie algebra.

The forward implication uses the existing positive-root subgroup factorization. The converse
uses the flag tangent equations and the unit entry of each negative root matrix.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
-/

public section

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B] {m : ℕ}

/-- The flag Lie algebra is given by vanishing below the diagonal in the self-dual order. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (d : Derivation R (Symplectic.coordinateHopfAlgebra R m)
      (Bialgebra.CounitAlgebra R (Symplectic.coordinateHopfAlgebra R m) B)) :
    d ∈ (definingHopfIdeal R m).lieSubalgebra ↔
      ∀ i j : Fin m ⊕ Fin m,
        flagOrder m (finSumFinEquiv j) < flagOrder m (finSumFinEquiv i) →
          (tangentMatrix m d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) B) i j = 0 := by
  rw [definingHopfIdeal_def, mem_lieSubalgebra_map_weightParabolicDefiningHopfIdeal_iff]
  simp only [Matrix.BlockTriangular, Function.comp_apply, OrderDual.toDual_lt_toDual,
    weights_lt_weights_iff]

/-- A positive root vector belongs to the Lie algebra of the isotropic flag stabilizer,
over every coefficient algebra. -/
theorem rootVector_mem_lieSubalgebra_of_isPos (root : GLSymplecticFin.RootSubgroupIndex m)
    (hroot : (diagonalRootBase.{u} m).IsPos root) :
    rootVector (R := R) (B := B) root ∈ (definingHopfIdeal R m).lieSubalgebra := by
  rw [HopfIdeal.mem_lieSubalgebra_iff]
  intro x hx
  have hzero := RingHom.mem_ker.mp
    (definingHopfIdeal_toIdeal_le_ker_rootSubgroupCoordinateMap R m root hroot hx)
  have hv := derivationComp_rootSubgroup_eq_smul_rootVector (R := R) (B := B) root
    ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1)
  simp only [LinearEquiv.apply_symm_apply, one_smul] at hv
  rw [← hv, derivationComp_apply]
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom] using
    hzero ▸ (map_zero ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := B)).symm 1))

/-- A normalized root vector is in the flag Lie algebra exactly when its type-C root is
positive. Nontriviality of the coefficient algebra ensures that a forbidden unit entry
cannot vanish. -/
@[simp↓]
theorem rootVector_mem_lieSubalgebra_iff [Nontrivial B]
    (root : GLSymplecticFin.RootSubgroupIndex m) :
    rootVector (R := R) (B := B) root ∈ (definingHopfIdeal R m).lieSubalgebra ↔
      (diagonalRootBase.{u} m).IsPos root := by
  refine ⟨?_, rootVector_mem_lieSubalgebra_of_isPos root⟩
  intro hroot
  rw [mem_lieSubalgebra_definingHopfIdeal_iff] at hroot
  simp only [tangentMatrix_rootVector (R := R) (B := B)] at hroot
  cases root with
  | positiveLong i => exact diagonalRootBase_isPos_positiveLong i
  | positiveSum i j hij => exact diagonalRootBase_isPos_positiveSum hij
  | negativeLong i =>
      have h := hroot (.inr i) (.inl i) (by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using flagOrder_castAdd_lt_addNat m i i)
      simp at h
  | negativeSum i j hij =>
      have h := hroot (.inr i) (.inl j) (by
        simpa only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.natAdd_eq_addNat] using flagOrder_castAdd_lt_addNat m i j)
      simp [hij.ne'] at h
  | difference i j hij =>
      rw [diagonalRootBase_isPos_difference_iff]
      by_contra h
      have hji := lt_of_le_of_ne (le_of_not_gt h) hij.symm
      have h := hroot (.inl i) (.inl j) (by
        simpa only [finSumFinEquiv_apply_left, flagOrder_castAdd,
          Fin.lt_def, Fin.val_castAdd] using hji)
      simp at h

end TauCeti.Symplectic.IsotropicFlag
