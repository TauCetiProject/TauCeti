/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint
public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The symmetric product intertwiner for the adjoint square of SL₃

The traceless symmetric product lifts to an equivariant linear map on the tensor square of
the trace-zero three-by-three matrices. The coefficient `2 / 3` is special to size three.
Swapping the tensor factors fixes this intertwiner. The Lie bracket intertwiner, which is
valid for every size, is `TauCeti.alternatingProductMap`.
-/

public section

namespace TauCeti.AdjointSquare

open Matrix
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [Field K]

local notation "V₃" => LieAlgebra.SpecialLinear.sl (Fin 3) K

/-- The traceless anticommutator as an equivariant map out of the tensor square. -/
noncomputable def symmetricProductMap [NeZero (3 : K)] :
    ((TauCeti.adjointRep K 3).tprod (TauCeti.adjointRep K 3)).IntertwiningMap
      (TauCeti.adjointRep K 3) where
  toLinearMap := TensorProduct.lift symmetricProduct
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    rw [Representation.tprod_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      TensorProduct.lift.tmul, LinearMap.comp_apply, TensorProduct.lift.tmul]
    apply Subtype.ext
    simp only [coe_symmetricProduct, TauCeti.coe_adjointRep_apply]
    exact symmetricProductMatrix_sl_conj g X.val Y.val

/-- On a simple tensor the symmetric intertwiner is the traceless anticommutator. -/
@[simp]
theorem symmetricProductMap_tmul [NeZero (3 : K)] (X Y : V₃) :
    symmetricProductMap K (X ⊗ₜ[K] Y) = symmetricProduct X Y :=
  (rfl)

/-- Swapping the tensor factors fixes the symmetric intertwiner. -/
theorem comm_symmetricProductMap [NeZero (3 : K)] (T : V₃ ⊗[K] V₃) :
    symmetricProductMap K (TensorProduct.comm K _ _ T) = symmetricProductMap K T := by
  have h : (symmetricProductMap K).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      (symmetricProductMap K).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    exact symmetricProduct_comm Y X
  exact LinearMap.congr_fun h T

end TauCeti.AdjointSquare
