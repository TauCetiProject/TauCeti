/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor.Automorphisms

/-!
# Extension of translations along a homomorphism

The extension functor `Torsor.mapFunctor` from `ContractedProduct` sends translations by
sections of the kernel to the identity. This supplies the automorphisms in lifting fibres.
The proof uses the naturality of `Torsor.toMap` and its equivariance.

The contracted product convention is that of Giraud, *Cohomologie non abélienne*, III §1.3.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {G H : Sheaf J GrpCat.{w}}

/-- A translation by a section killed by `φ` extends to the identity. -/
lemma mapFunctor_map_translationHom_eq_id [∀ U, IsMulCommutative (G.obj.obj U)]
    (φ : G ⟶ H) (P : Torsor G) (s : (G.obj ⋙ forget GrpCat).sections)
    (hs : ∀ U, φ.hom.app U (GrpCat.sectionsπMonoidHom G.obj U s) = 1) :
    (mapFunctor φ).map (P.translationHom s) = 𝟙 (P.map φ) := by
  apply map_hom_ext
  rw [toMap_mapFunctor_map]
  ext U p
  exact (congrArg ((P.toMap φ).hom.app U) (P.translationHom_hom_app s U p)).trans
    ((Torsor.toMap_smul φ P (GrpCat.sectionsπMonoidHom G.obj U s) p).trans (by
      rw [hs U]
      exact one_smul _ _))

end CategoryTheory.Sheaf.Torsor
