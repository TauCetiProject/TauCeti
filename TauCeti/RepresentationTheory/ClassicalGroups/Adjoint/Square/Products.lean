/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.SymmetricProduct
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The alternating and symmetric product intertwiners for the adjoint square of SLₙ

Over a commutative ring the Lie bracket gives an equivariant contraction that changes sign
under the tensor flip. When `n` is nonzero in the field, the traceless symmetric product lifts to
an equivariant linear map on the tensor square of the trace-zero matrices. Swapping the tensor
factors fixes this map.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix TauCeti.SLAdjoint LieAlgebra.SpecialLinear
open scoped TensorProduct

section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The Lie bracket as an equivariant map out of the tensor square. -/
noncomputable def alternatingProductMap :
    ((adjointRep K n).tprod (adjointRep K n)).IntertwiningMap (adjointRep K n) where
  toLinearMap :=
    TensorProduct.lift (LieAlgebra.ad K (LieAlgebra.SpecialLinear.sl (Fin n) K)).toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    simp only [Representation.tprod_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lift.tmul, LieHom.coe_toLinearMap, LieAlgebra.ad_apply]
    apply Subtype.ext
    simp only [LieAlgebra.SpecialLinear.sl_bracket, coe_adjointRep_apply]
    rw [SpecialLinearGroup.conj_eq_units_smul, SpecialLinearGroup.conj_eq_units_smul,
      SpecialLinearGroup.conj_eq_units_smul, smul_sub, smul_mul', smul_mul']

/-- On a simple tensor the alternating intertwiner is the commutator. -/
@[simp]
theorem alternatingProductMap_tmul (X Y : LieAlgebra.SpecialLinear.sl (Fin n) K) :
    alternatingProductMap K n (X ⊗ₜ[K] Y) = ⁅X, Y⁆ := by
  simp only [alternatingProductMap, Representation.IntertwiningMap.coe_mk,
    TensorProduct.lift.tmul, LieHom.coe_toLinearMap, LieAlgebra.ad_apply]

/-- Swapping the tensor factors negates the alternating intertwiner. -/
@[simp]
theorem alternatingProductMap_comm_eq_neg
    (T : LieAlgebra.SpecialLinear.sl (Fin n) K ⊗[K]
      LieAlgebra.SpecialLinear.sl (Fin n) K) :
    alternatingProductMap K n (TensorProduct.comm K _ _ T) =
      -alternatingProductMap K n T := by
  have h : (alternatingProductMap K n).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      -(alternatingProductMap K n).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      LinearMap.neg_apply, Representation.IntertwiningMap.toLinearMap_apply,
      alternatingProductMap_tmul]
    exact (lie_skew Y X).symm
  exact LinearMap.congr_fun h T

end

variable (K : Type*) [CommRing K] (n : ℕ) [Invertible (Fintype.card (Fin n) : K)]

local notation "V" => LieAlgebra.SpecialLinear.sl (Fin n) K

/-- The traceless anticommutator as an equivariant map out of the tensor square. -/
noncomputable def symmetricProductMap :
    ((adjointRep K n).tprod (adjointRep K n)).IntertwiningMap
      (adjointRep K n) where
  toLinearMap := TensorProduct.lift symmetricProduct
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    simp only [Representation.tprod_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lift.tmul]
    apply Subtype.ext
    simp only [coe_symmetricProduct, coe_adjointRep_apply, SpecialLinearGroup.conj_eq_units_smul,
      tracelessAnticommutator_units_smul]

/-- On a simple tensor the symmetric intertwiner is the traceless anticommutator. -/
@[simp]
theorem symmetricProductMap_tmul (X Y : V) :
    symmetricProductMap K n (X ⊗ₜ[K] Y) = symmetricProduct X Y := by
  simp only [symmetricProductMap, Representation.IntertwiningMap.coe_mk, TensorProduct.lift.tmul]

/-- Swapping the tensor factors fixes the symmetric intertwiner. -/
@[simp]
theorem symmetricProductMap_comm (T : V ⊗[K] V) :
    symmetricProductMap K n (TensorProduct.comm K _ _ T) = symmetricProductMap K n T := by
  have h : (symmetricProductMap K n).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      (symmetricProductMap K n).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      Representation.IntertwiningMap.toLinearMap_apply, symmetricProductMap_tmul]
    exact symmetricProduct_comm Y X
  exact LinearMap.congr_fun h T

end TauCeti.AdjointSquare
