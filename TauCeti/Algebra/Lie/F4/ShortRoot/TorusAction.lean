/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Action
public import Mathlib.Algebra.Lie.Matrix
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Torus weights of the modular short-root adjoint representation

This file records the integral weight support of the adjoint representation on the modular
short-root ideal.  The support statement is kept over `ZMod 2`, while the labels remain in the
integral character lattice so that they can be used for torus conjugation after scalar extension.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module

noncomputable section

private theorem f4ShortRootWeight_eq_root_of_eq_inl
    (i : Fin 26) (α : F4ShortRootIndex)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inl α) :
    f4ShortRootWeight i = f4Root α := by
  have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
  simp only [Equiv.symm_apply_apply] at hi'
  rw [hi', f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inl]

private theorem f4ShortRootWeight_eq_zero_of_eq_inr
    (i : Fin 26) (k : Fin 2)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inr k) :
    f4ShortRootWeight i = 0 := by
  have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
  simp only [Equiv.symm_apply_apply] at hi'
  rw [hi', f4ShortRootWeight_f4ShortRootWeightIndexEquiv_symm_inr]

private theorem f4Root_add_eq_zero_of_f4KillingRoot_add_eq_zero
    (α β : Fin 48)
    (h : (f4KillingRoot α : (F4.cartanSubalgebra valid_F4) → ℚ) +
      f4KillingRoot β = 0) :
    f4Root α + f4Root β = 0 := by
  have hβ := eq_neg_of_add_eq_zero_right h
  have hroot := (f4KillingRoot_eq_add_zsmul_iff α α β (-2)).mp (by
    rw [hβ]
    module)
  simp only [f4SimplyConnectedRootDatum_root] at hroot
  rw [hroot]
  module

private theorem f4ModularChevalleyBasis_repr_smul_rootVector_inr_eq_zero
    (c : ZMod 2) (α : Fin 48) (r : f4KillingBase.support) :
    f4ModularChevalleyBasis.repr (c • f4ModularRootVector α) (Sum.inr r) = 0 := by
  classical
  rw [map_smul, f4ModularRootVector_eq_basis,
    f4ModularChevalleyBasis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  simp

private theorem f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_inr_eq_zero
    (a : Fin F4.rank) (α : Fin 48) (r : f4KillingBase.support) :
    f4ModularChevalleyBasis.repr
      ⁅f4ModularSimpleCoroot a, f4ModularRootVector α⁆ (Sum.inr r) = 0 := by
  rw [f4Modular_lie_simpleCoroot_rootVector,
    f4ModularChevalleyBasis_repr_smul_rootVector_inr_eq_zero]

private theorem f4Root_add_eq_zero_of_repr_lie_rootVector_inr_ne_zero
    (α β : Fin 48) (r : f4KillingBase.support)
    (hne : f4ModularChevalleyBasis.repr
      ⁅f4ModularRootVector α, f4ModularRootVector β⁆ (Sum.inr r) ≠ 0) :
    f4Root β + f4Root α = 0 := by
  let H := F4.cartanSubalgebra valid_F4
  by_cases hsum :
      (f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ) = 0
  · simpa only [add_comm] using
      f4Root_add_eq_zero_of_f4KillingRoot_add_eq_zero α β hsum
  by_cases hbot : rootSpace H
      ((f4KillingRoot α : H → ℚ) + (f4KillingRoot β : H → ℚ)) = ⊥
  · have hlie := f4Modular_lie_rootVector_eq_zero_of_rootSpace_add_eq_bot α β hbot
    rw [hlie, map_zero] at hne
    exact (hne rfl).elim
  · obtain ⟨ε, hε⟩ := exists_f4_root_eq_add_of_rootSpace_ne_bot α β hsum hbot
    obtain ⟨z, _, hlie⟩ := exists_f4Modular_lie_rootVector_eq_smul_of_add α β ε hε
    rw [hlie, f4ModularChevalleyBasis_repr_smul_rootVector_inr_eq_zero] at hne
    exact (hne rfl).elim

private theorem f4ShortRootAdjointMatrix_root_root_support (α : Fin 48)
    (i j : Fin 26) (γ β : F4ShortRootIndex)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inl γ)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inl β)
    (hne : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4Root α := by
  have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
  have hj' := congrArg f4ShortRootWeightIndexEquiv.symm hj
  simp only [Equiv.symm_apply_apply] at hi' hj'
  have hcoord : f4ShortRootBasisCoordinate i =
      Sum.inl (f4KillingRootLabel γ) := by
    rw [hi', f4ShortRootBasisCoordinate_symm_inl]
  have hinput :
      (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) =
        f4ModularRootVector β := by
    rw [hj', coe_f4ShortRootLieIdealBasis,
      f4ShortRootBasisCoordinate_symm_inl,
      f4ModularChevalleyBasis_inl_eq_rootVector]
    simp only [f4PinnedRootIndex_f4KillingRootLabel]
  simp only [f4ShortRootAdjointMatrix_apply, hinput, hcoord] at hne
  have hroot := f4_root_eq_add_of_repr_lie_rootVector_ne_zero α β γ hne
  rw [f4ShortRootWeight_eq_root_of_eq_inl i γ hi,
    f4ShortRootWeight_eq_root_of_eq_inl j β hj]
  simpa only [f4SimplyConnectedRootDatum_root] using hroot

private theorem f4Root_eq_of_repr_smul_rootVector_inl_ne_zero
    (c : ZMod 2) (α γ : Fin 48)
    (hne : f4ModularChevalleyBasis.repr (c • f4ModularRootVector α)
      (Sum.inl (f4KillingRootLabel γ)) ≠ 0) :
    f4Root γ = f4Root α := by
  classical
  by_contra hroot
  have hlabel : f4KillingRootLabel α ≠ f4KillingRootLabel γ := by
    intro hlabel
    apply hroot
    have hindex : α = γ := by
      simpa only [f4PinnedRootIndex_f4KillingRootLabel] using
        congrArg f4PinnedRootIndex hlabel
    exact congrArg f4Root hindex.symm
  rw [map_smul, f4ModularRootVector_eq_basis,
    f4ModularChevalleyBasis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply] at hne
  simp only [Sum.inl.injEq, hlabel, ↓reduceIte, smul_zero] at hne
  exact hne rfl

private theorem f4Root_eq_of_adjointMatrix_root_simpleCoroot_input_ne_zero
    (α : Fin 48) (i j : Fin 26) (γ : F4ShortRootIndex) (a : Fin F4.rank)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inl γ)
    (hj : (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot a)
    (hne : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j ≠ 0) :
    f4Root γ = f4Root α := by
  have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
  simp only [Equiv.symm_apply_apply] at hi'
  have hcoord : f4ShortRootBasisCoordinate i =
      Sum.inl (f4KillingRootLabel γ) := by
    rw [hi', f4ShortRootBasisCoordinate_symm_inl]
  rw [f4ShortRootAdjointMatrix_apply, hj, hcoord,
    f4Modular_lie_rootVector_simpleCoroot] at hne
  exact f4Root_eq_of_repr_smul_rootVector_inl_ne_zero _ α γ hne

private theorem f4ShortRootAdjointMatrix_root_zero_input_support
    (α : Fin 48) (i j : Fin 26) (γ : F4ShortRootIndex) (l : Fin 2)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inl γ)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inr l)
    (hne : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4Root α := by
  have hroot : f4Root γ = f4Root α := by
    fin_cases l
    · have hj' : j = 12 :=
        (f4ShortRootWeightIndexEquiv_apply_eq_inr_zero_iff j).mp (by simpa using hj)
      subst j
      exact f4Root_eq_of_adjointMatrix_root_simpleCoroot_input_ne_zero
        α i 12 γ (Fin.cast rank_F4.symm (2 : Fin 4)) hi
        coe_f4ShortRootLieIdealBasis_twelve hne
    · have hj' : j = 13 :=
        (f4ShortRootWeightIndexEquiv_apply_eq_inr_one_iff j).mp (by simpa using hj)
      subst j
      exact f4Root_eq_of_adjointMatrix_root_simpleCoroot_input_ne_zero
        α i 13 γ (Fin.cast rank_F4.symm (3 : Fin 4)) hi
        coe_f4ShortRootLieIdealBasis_thirteen hne
  rw [f4ShortRootWeight_eq_root_of_eq_inl i γ hi,
    f4ShortRootWeight_eq_zero_of_eq_inr j l hj, zero_add]
  exact hroot

private theorem f4ShortRootAdjointMatrix_zero_root_input_support
    (α : Fin 48) (i j : Fin 26) (k : Fin 2) (β : F4ShortRootIndex)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inr k)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inl β)
    (hne : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4Root α := by
  let r := (F4.lieBasis valid_F4).baseSupportEquiv (f4ShortSimpleIndex k)
  have hcoord : f4ShortRootBasisCoordinate i = Sum.inr r := by
    have h := congrArg (f4ShortRootBasisCoordinate ∘ f4ShortRootWeightIndexEquiv.symm) hi
    simpa only [Function.comp_apply, Equiv.symm_apply_apply,
      f4ShortRootBasisCoordinate_symm_inr] using h
  have hj' := congrArg f4ShortRootWeightIndexEquiv.symm hj
  simp only [Equiv.symm_apply_apply] at hj'
  have hinput :
      (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) =
        f4ModularRootVector β := by
    rw [hj', coe_f4ShortRootLieIdealBasis_symm_inl]
  simp only [f4ShortRootAdjointMatrix_apply, hinput, hcoord] at hne
  have hzero :=
    f4Root_add_eq_zero_of_repr_lie_rootVector_inr_ne_zero α β r hne
  rw [f4ShortRootWeight_eq_zero_of_eq_inr i k hi,
    f4ShortRootWeight_eq_root_of_eq_inl j β hj]
  exact hzero.symm

private theorem f4ShortRootAdjointMatrix_root_simpleCoroot_zero_output_eq_zero
    (α : Fin 48) (i j : Fin 26) (k : Fin 2) (a : Fin F4.rank)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inr k)
    (hj : (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot a) :
    f4ShortRootAdjointMatrix (f4ModularRootVector α) i j = 0 := by
  let r := (F4.lieBasis valid_F4).baseSupportEquiv (f4ShortSimpleIndex k)
  have hcoord : f4ShortRootBasisCoordinate i = Sum.inr r := by
    have h := congrArg (f4ShortRootBasisCoordinate ∘ f4ShortRootWeightIndexEquiv.symm) hi
    simpa only [Function.comp_apply, Equiv.symm_apply_apply,
      f4ShortRootBasisCoordinate_symm_inr] using h
  rw [f4ShortRootAdjointMatrix_apply, hj, hcoord,
    f4Modular_lie_rootVector_simpleCoroot,
    f4ModularChevalleyBasis_repr_smul_rootVector_inr_eq_zero]

private theorem f4ShortRootAdjointMatrix_zero_zero_input_eq_zero
    (α : Fin 48) (i j : Fin 26) (k l : Fin 2)
    (hi : f4ShortRootWeightIndexEquiv i = Sum.inr k)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inr l) :
    f4ShortRootAdjointMatrix (f4ModularRootVector α) i j = 0 := by
  fin_cases l
  · have hj' : j = 12 :=
      (f4ShortRootWeightIndexEquiv_apply_eq_inr_zero_iff j).mp (by simpa using hj)
    subst j
    exact f4ShortRootAdjointMatrix_root_simpleCoroot_zero_output_eq_zero
      α i 12 k (Fin.cast rank_F4.symm (2 : Fin 4)) hi
      coe_f4ShortRootLieIdealBasis_twelve
  · have hj' : j = 13 :=
      (f4ShortRootWeightIndexEquiv_apply_eq_inr_one_iff j).mp (by simpa using hj)
    subst j
    exact f4ShortRootAdjointMatrix_root_simpleCoroot_zero_output_eq_zero
      α i 13 k (Fin.cast rank_F4.symm (3 : Fin 4)) hi
      coe_f4ShortRootLieIdealBasis_thirteen

/-- Every nonzero coefficient of a root-vector adjoint matrix has the corresponding integral
weight shift.  This retains the characteristic-zero torus labels after reduction modulo two. -/
theorem f4ShortRootAdjointMatrix_root_weight_support (α : Fin 48) (i j : Fin 26)
    (hne : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j + f4Root α := by
  classical
  rcases hi : f4ShortRootWeightIndexEquiv i with γ | k
  · rcases hj : f4ShortRootWeightIndexEquiv j with β | l
    · exact f4ShortRootAdjointMatrix_root_root_support α i j γ β hi hj hne
    · exact f4ShortRootAdjointMatrix_root_zero_input_support α i j γ l hi hj hne
  · rcases hj : f4ShortRootWeightIndexEquiv j with β | l
    · exact f4ShortRootAdjointMatrix_zero_root_input_support α i j k β hi hj hne
    · exact (hne (f4ShortRootAdjointMatrix_zero_zero_input_eq_zero α i j k l hi hj)).elim

private theorem f4ShortRootAdjointMatrix_simpleCoroot_root_input_support
    (a : Fin F4.rank) (i j : Fin 26) (β : F4ShortRootIndex)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inl β)
    (hne : f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j := by
  have hj' := congrArg f4ShortRootWeightIndexEquiv.symm hj
  simp only [Equiv.symm_apply_apply] at hj'
  have hinput :
      (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) =
        f4ModularRootVector β := by
    rw [hj', coe_f4ShortRootLieIdealBasis_symm_inl]
  rcases hi : f4ShortRootWeightIndexEquiv i with γ | k
  · have hi' := congrArg f4ShortRootWeightIndexEquiv.symm hi
    simp only [Equiv.symm_apply_apply] at hi'
    have hcoord : f4ShortRootBasisCoordinate i =
        Sum.inl (f4KillingRootLabel γ) := by
      rw [hi', f4ShortRootBasisCoordinate_symm_inl]
    rw [f4ShortRootAdjointMatrix_apply, hinput, hcoord,
      f4Modular_lie_simpleCoroot_rootVector] at hne
    have hroot := f4Root_eq_of_repr_smul_rootVector_inl_ne_zero _ β γ hne
    rw [f4ShortRootWeight_eq_root_of_eq_inl i γ hi,
      f4ShortRootWeight_eq_root_of_eq_inl j β hj]
    exact hroot
  · let r := (F4.lieBasis valid_F4).baseSupportEquiv (f4ShortSimpleIndex k)
    have hcoord : f4ShortRootBasisCoordinate i = Sum.inr r := by
      have h := congrArg (f4ShortRootBasisCoordinate ∘ f4ShortRootWeightIndexEquiv.symm) hi
      simpa only [Function.comp_apply, Equiv.symm_apply_apply,
        f4ShortRootBasisCoordinate_symm_inr] using h
    simp only [f4ShortRootAdjointMatrix_apply, hinput, hcoord] at hne
    have hz :=
      f4ModularChevalleyBasis_repr_lie_simpleCoroot_rootVector_inr_eq_zero a β r
    exact (hne hz).elim

private theorem f4ShortRootAdjointMatrix_simpleCoroot_zero_input_eq_zero
    (a : Fin F4.rank) (i j : Fin 26) (l : Fin 2)
    (hj : f4ShortRootWeightIndexEquiv j = Sum.inr l) :
    f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j = 0 := by
  fin_cases l
  · have hj' : j = 12 :=
      (f4ShortRootWeightIndexEquiv_apply_eq_inr_zero_iff j).mp (by simpa using hj)
    subst j
    rw [f4ShortRootAdjointMatrix_apply,
      coe_f4ShortRootLieIdealBasis_twelve,
      f4Modular_lie_simpleCoroot_simpleCoroot_eq_zero, map_zero]
    rfl
  · have hj' : j = 13 :=
      (f4ShortRootWeightIndexEquiv_apply_eq_inr_one_iff j).mp (by simpa using hj)
    subst j
    rw [f4ShortRootAdjointMatrix_apply,
      coe_f4ShortRootLieIdealBasis_thirteen,
      f4Modular_lie_simpleCoroot_simpleCoroot_eq_zero, map_zero]
    rfl

/-- Simple-coroot adjoint matrices preserve each integral weight coordinate. -/
theorem f4ShortRootAdjointMatrix_simpleCoroot_weight_support
    (a : Fin F4.rank) (i j : Fin 26)
    (hne : f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j ≠ 0) :
    f4ShortRootWeight i = f4ShortRootWeight j := by
  rcases hj : f4ShortRootWeightIndexEquiv j with β | l
  · exact f4ShortRootAdjointMatrix_simpleCoroot_root_input_support a i j β hj hne
  · exact (hne
      (f4ShortRootAdjointMatrix_simpleCoroot_zero_input_eq_zero a i j l hj)).elim

section TorusConjugation

variable {A : Type*} [CommRing A] [Algebra (ZMod 2) A]

/-- The short-root weight torus as an invertible matrix. -/
noncomputable abbrev f4ShortRootWeightTorusGL (s : Fin 4 → Aˣ) :
    GL (Fin 26) A :=
  TauCeti.diagGL fun i => TauCeti.torusCharacter s (f4ShortRootWeight i)

/-- Conjugation by the actual diagonal torus point scales a represented root vector by its
integral root character. -/
theorem f4ShortRootWeightTorusGL_conj_root
    (s : Fin 4 → Aˣ) (α : Fin 48) :
    (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A) *
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularRootVector α) *
        (((f4ShortRootWeightTorusGL s)⁻¹ : GL (Fin 26) A) :
          Matrix (Fin 26) (Fin 26) A) =
      ((TauCeti.torusCharacter s (f4Root α) : Aˣ) : A) •
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularRootVector α) := by
  classical
  simp only [f4ShortRootWeightTorusGL, ← map_inv, TauCeti.diagGL_coe]
  ext i j
  simp only [f4ShortRootAdjointMatrixBaseChange, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  -- Both sides are now scalar identities in the `i,j` matrix entry.
  change (TauCeti.torusCharacter s (f4ShortRootWeight i) : A) *
        algebraMap (ZMod 2) A
          (f4ShortRootAdjointMatrix (f4ModularRootVector α) i j) *
        ((TauCeti.torusCharacter s (f4ShortRootWeight j))⁻¹ : Aˣ) =
      (TauCeti.torusCharacter s (f4Root α) : A) *
        algebraMap (ZMod 2) A
          (f4ShortRootAdjointMatrix (f4ModularRootVector α) i j)
  by_cases hcoeff : f4ShortRootAdjointMatrix (f4ModularRootVector α) i j = 0
  · rw [hcoeff, map_zero, mul_zero, zero_mul, mul_zero]
  · have hweight := f4ShortRootAdjointMatrix_root_weight_support α i j hcoeff
    have hchar := TauCeti.torusCharacter_add s (f4ShortRootWeight j) (f4Root α)
    rw [hweight, hchar]
    simp only [Units.val_mul]
    calc
      _ = ((TauCeti.torusCharacter s (f4ShortRootWeight j) : A) *
          ((TauCeti.torusCharacter s (f4ShortRootWeight j))⁻¹ : Aˣ)) *
          ((TauCeti.torusCharacter s (f4Root α) : A) *
            algebraMap (ZMod 2) A (f4ShortRootAdjointMatrix (f4ModularRootVector α) i j)) := by
        ring
      _ = _ := by rw [Units.mul_inv, one_mul]

/-- Conjugation by the actual diagonal torus point fixes a represented simple coroot. -/
theorem f4ShortRootWeightTorusGL_conj_simpleCoroot
    (s : Fin 4 → Aˣ) (a : Fin F4.rank) :
    (f4ShortRootWeightTorusGL s : Matrix (Fin 26) (Fin 26) A) *
        f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularSimpleCoroot a) *
        (((f4ShortRootWeightTorusGL s)⁻¹ : GL (Fin 26) A) :
          Matrix (Fin 26) (Fin 26) A) =
      f4ShortRootAdjointMatrixBaseChange (A := A) (f4ModularSimpleCoroot a) := by
  classical
  simp only [f4ShortRootWeightTorusGL, ← map_inv, TauCeti.diagGL_coe]
  ext i j
  simp only [f4ShortRootAdjointMatrixBaseChange, Matrix.diagonal_mul, Matrix.mul_diagonal]
  -- A coroot has weight zero, so only the diagonal character factors remain.
  change (TauCeti.torusCharacter s (f4ShortRootWeight i) : A) *
        algebraMap (ZMod 2) A
          (f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j) *
        ((TauCeti.torusCharacter s (f4ShortRootWeight j))⁻¹ : Aˣ) =
      algebraMap (ZMod 2) A
        (f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j)
  by_cases hcoeff : f4ShortRootAdjointMatrix (f4ModularSimpleCoroot a) i j = 0
  · rw [hcoeff, map_zero, mul_zero, zero_mul]
  · have hweight := f4ShortRootAdjointMatrix_simpleCoroot_weight_support a i j hcoeff
    rw [hweight]
    rw [mul_right_comm, Units.mul_inv, one_mul]

end TorusConjugation

end

end TauCeti.DynkinType
