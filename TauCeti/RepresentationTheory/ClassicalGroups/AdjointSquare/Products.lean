/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Basic
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjAct

/-!
# The symmetric product intertwiner for the adjoint square of SLₙ

When `n` is nonzero in the field, the traceless symmetric product lifts to an equivariant
linear map on the tensor square of the trace-zero matrices. Swapping the tensor factors
fixes this map.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix TauCeti.SLAdjoint
open scoped TensorProduct

variable (K : Type*) [Field K] (n : ℕ) [NeZero (n : K)]

local notation "V" => LieAlgebra.SpecialLinear.sl (Fin n) K

/-- The traceless anticommutator as an equivariant map out of the tensor square. -/
noncomputable def symmetricProductMap :
    ((adjointRep K n).tprod (adjointRep K n)).IntertwiningMap
      (adjointRep K n) where
  toLinearMap := TensorProduct.lift symmetricProduct
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    rw [Representation.tprod_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.lift.tmul]
    apply Subtype.ext
    simp only [coe_symmetricProduct, coe_adjointRep_apply, SpecialLinearGroup.conj_eq_units_smul,
      tracelessAnticommutator_units_smul]

/-- On a simple tensor the symmetric intertwiner is the traceless anticommutator. -/
@[simp]
theorem symmetricProductMap_tmul (X Y : V) :
    symmetricProductMap K n (X ⊗ₜ[K] Y) = symmetricProduct X Y :=
  (rfl)

/-- Swapping the tensor factors fixes the symmetric intertwiner. -/
theorem symmetricProductMap_comm (T : V ⊗[K] V) :
    symmetricProductMap K n (TensorProduct.comm K _ _ T) = symmetricProductMap K n T := by
  have h : (symmetricProductMap K n).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      (symmetricProductMap K n).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    exact symmetricProduct_comm Y X
  exact LinearMap.congr_fun h T

end TauCeti.AdjointSquare
