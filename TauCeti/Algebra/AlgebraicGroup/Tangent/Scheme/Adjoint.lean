/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ComoduleAction

/-!
# The adjoint action on the tangent scheme

The polynomial adjoint coaction represents an action on the spectrum of polynomial functions.
The reflexive comparison with the tangent scheme transports this to the tangent scheme over
the ground field.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace TauCeti

universe u

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "P" => SymmetricAlgebra k (Module.Dual k 𝔤)
local notation "G" => Grp.X (Functor.obj (hopfSpec (CommRingCat.of k))
  (op (CommHopfAlgCat.of k H)))

attribute [local instance] adjointPolynomialComoduleAlgebra

/-- The adjoint action on the existing tangent scheme over its ground field. -/
@[implicit_reducible]
def lieAlgebraAdjointAction : ModObj G (lieAlgebraOver k H) := by
  letI : ModObj G ((algSpec (.of k)).obj (op (CommAlgCat.of k P))) :=
    ComoduleAlgebra.specModObj k H P
  letI : IsMonHom (Iso.refl G).hom := by
    simpa only [Iso.refl_hom] using (inferInstance : IsMonHom (𝟙 G))
  exact ModObj.ofIso (M := G) (Iso.refl G) (lieAlgebraOverIso k H)

/-- The transported adjoint action is computed in the polynomial presentation. -/
theorem lieAlgebraAdjointAction_smul :
    letI := lieAlgebraAdjointAction k H
    ModObj.smul (M := G) (X := lieAlgebraOver k H) =
      (𝟙 G ⊗ₘ (lieAlgebraOverIso k H).inv) ≫
        (ComoduleAlgebra.specModObj k H P).smul ≫ (lieAlgebraOverIso k H).hom := by
  -- In `ModObj.ofIso`, the group isomorphism is `Iso.refl`, and the self-action on
  -- morphisms is the monoidal tensor. Its inverse therefore contributes `𝟙 G`.
  rfl

end TauCeti
