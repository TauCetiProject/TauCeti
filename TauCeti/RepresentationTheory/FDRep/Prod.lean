/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# Products of finite representations through universe shrinking

`Representation.nonempty_fdRepIso_ofShrink_prod` identifies the componentwise product on
module-finite carriers with the categorical biproduct of their shrunk objects. This permits
direct-sum arguments for carriers in different universes, retaining their actual actions.
The comparison uses Mathlib's concrete product in `Rep` and the fully faithful forgetful functor.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace Representation

open FDRep

variable {R G V W : Type*} [CommRing R] [Monoid G]
  [AddCommGroup V] [Module R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W]

/-- Shrinking a product of module-finite representations gives the biproduct of the
shrunk representations. -/
theorem nonempty_fdRepIso_ofShrink_prod (π : Representation R G V) (ρ : Representation R G W)
    [HasBinaryBiproduct (ofShrink π) (ofShrink ρ)] :
    Nonempty (ofShrink (Representation.prod π ρ) ≅ ofShrink π ⊞ ofShrink ρ) := by
  let F := forget₂ (FDRep R G) (Rep R G)
  let eπ := ofShrinkEquiv π
  let eρ := ofShrinkEquiv ρ
  let ep : Representation.Equiv (Representation.prod π ρ)
      (Representation.prod (ofShrink π).ρ (ofShrink ρ).ρ) :=
    Representation.Equiv.mk (eπ.symm.toLinearEquiv.prodCongr eρ.symm.toLinearEquiv) (by
      intro g
      apply LinearMap.ext
      intro v
      exact Prod.ext (eπ.symm.toIntertwiningMap.isIntertwining _ _ g v.1)
        (eρ.symm.toIntertwiningMap.isIntertwining _ _ g v.2))
  let e := (ofShrinkEquiv (Representation.prod π ρ)).trans ep
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  refine ⟨F.preimageIso ?_⟩
  exact
    Rep.mkIso e ≪≫ Rep.prodIsoProduct (F.obj (ofShrink π)) (F.obj (ofShrink ρ)) ≪≫
      (biprod.isoProd (F.obj (ofShrink π)) (F.obj (ofShrink ρ))).symm ≪≫
      (F.mapBiprod (ofShrink π) (ofShrink ρ)).symm

end Representation
