/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.AdjointSquare.Representation
public import Mathlib.RepresentationTheory.Intertwining

/-!
# The two product intertwiners for the adjoint square of SL₃

The Lie bracket and traceless symmetric product lift to equivariant linear
maps on the tensor square. The tensor flip acts on the two products with
opposite signs. This supplies the forward maps for the adjoint-square worked
example in the TensorProductCombinatorics roadmap, intention 2823.
-/

@[expose] public section

namespace TauCeti.AdjointSquare

open Matrix
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type*) [Field K]

local notation "V₃" => LieAlgebra.SpecialLinear.sl (Fin 3) K

/-- The Lie bracket as an equivariant map out of the tensor square. -/
noncomputable def alternatingProductMap :
    ((adjointRep K).tprod (adjointRep K)).IntertwiningMap (adjointRep K) where
  toLinearMap := TensorProduct.lift (LieAlgebra.ad K ↥V₃).toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    change ⁅adjointRep K g X, adjointRep K g Y⁆ = adjointRep K g ⁅X, Y⁆
    apply Subtype.ext
    simp only [LieAlgebra.SpecialLinear.sl_bracket, coe_adjointRep_apply]
    exact commutator_sl_conj g X.val Y.val

/-- On a simple tensor the alternating intertwiner is the commutator. -/
@[simp] theorem alternatingProductMap_tmul (X Y : V₃) :
    alternatingProductMap K (X ⊗ₜ[K] Y) = ⁅X, Y⁆ := rfl

/-- The traceless anticommutator as an equivariant map out of the tensor square. -/
noncomputable def symmetricProductMap [NeZero (3 : K)] :
    ((adjointRep K).tprod (adjointRep K)).IntertwiningMap (adjointRep K) where
  toLinearMap := TensorProduct.lift symmetricProduct
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro X Y
    change symmetricProduct (adjointRep K g X) (adjointRep K g Y) =
      adjointRep K g (symmetricProduct X Y)
    apply Subtype.ext
    simp only [coe_symmetricProduct, coe_adjointRep_apply]
    exact symmetricProductMatrix_sl_conj g X.val Y.val

/-- On a simple tensor the symmetric intertwiner is the traceless anticommutator. -/
@[simp] theorem symmetricProductMap_tmul [NeZero (3 : K)] (X Y : V₃) :
    symmetricProductMap K (X ⊗ₜ[K] Y) = symmetricProduct X Y := rfl

/-- Flipping either tensor factor negates the alternating intertwiner. -/
theorem alternatingProductMap_comm (T : V₃ ⊗[K] V₃) :
    alternatingProductMap K (TensorProduct.comm K _ _ T) = -alternatingProductMap K T := by
  have h : (alternatingProductMap K).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      -(alternatingProductMap K).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    change ⁅Y, X⁆ = -⁅X, Y⁆
    exact (lie_skew Y X).symm
  exact LinearMap.congr_fun h T

/-- Flipping the tensor factors fixes the symmetric intertwiner. -/
theorem symmetricProductMap_comm [NeZero (3 : K)] (T : V₃ ⊗[K] V₃) :
    symmetricProductMap K (TensorProduct.comm K _ _ T) = symmetricProductMap K T := by
  have h : (symmetricProductMap K).toLinearMap.comp (TensorProduct.comm K _ _).toLinearMap =
      (symmetricProductMap K).toLinearMap := by
    apply TensorProduct.ext'
    intro X Y
    exact symmetricProduct_comm Y X
  exact LinearMap.congr_fun h T

end TauCeti.AdjointSquare
