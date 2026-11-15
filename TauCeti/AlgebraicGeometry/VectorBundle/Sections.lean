/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.TotalSpace

/-!
# Global sections of a geometric vector bundle

Sections of the structure morphism `𝕍(E) → X` correspond to global sections of the finite
locally free sheaf `E`, expressed as maps `𝒪_X → E`. A geometric section is a morphism from
`Over.mk (𝟙 X)` in `Over X`, so its defining equation is part of its type. The correspondence
is natural in `E`: a bundle map acts on geometric sections by composition and on sheaf
sections by its underlying morphism of sheaves.

The construction specializes the section-valued universal property of the total space to
`X → X` and removes the identity pullback using `Scheme.Modules.pullbackId`.
The forward and inverse formulas identify this normalization explicitly.

Here `𝕍(E)` means `Spec_X (Sym E^∨)`, covariantly in the sheaf of sections `E`.
The references instead write `V(F) = Spec_X (Sym F)`, so this is their `V(E^∨)`;
its sections are `E^∨∨ ≅ E`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.18.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Sections of `𝕍(E) → X` are global sections `𝒪_X → E`. A section of the scheme morphism
is represented by a morphism in `Over X` from the identity of `X`. -/
def totalSpaceSectionEquiv (E : FiniteLocallyFreeSheaf X) :
    (Over.mk (𝟙 X) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) ≃
        (𝟙_ X.Modules ⟶ E.obj) :=
  (totalSpaceHomEquiv E (Over.mk (𝟙 X))).trans
    ((Iso.refl (𝟙_ X.Modules)).homCongr ((Scheme.Modules.pullbackId X).app E.obj))

/-- The sheaf section of a geometric section is obtained by identifying the identity
pullback of `E` with `E`. -/
theorem totalSpaceSectionEquiv_apply (E : FiniteLocallyFreeSheaf X)
    (s : Over.mk (𝟙 X) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceSectionEquiv E s =
      totalSpaceHomEquiv E (Over.mk (𝟙 X)) s ≫ (Scheme.Modules.pullbackId X).hom.app E.obj := by
  simp only [totalSpaceSectionEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp, Iso.app_hom]

/-- A global sheaf section gives a point of the total space after transporting it to the
identity pullback of `E`. -/
theorem totalSpaceSectionEquiv_symm_apply (E : FiniteLocallyFreeSheaf X)
    (s : 𝟙_ X.Modules ⟶ E.obj) :
    (totalSpaceSectionEquiv E).symm s =
      (totalSpaceHomEquiv E (Over.mk (𝟙 X))).symm
        (s ≫ (Scheme.Modules.pullbackId X).inv.app E.obj) := by
  simp [totalSpaceSectionEquiv, Iso.homCongr]

-- Not a simp lemma: totalSpaceScheme_map already simplifies the map inside its left-hand side.
/-- A bundle map acts on geometric sections by composition and on sheaf sections by its
underlying morphism of sheaves. -/
theorem totalSpaceSectionEquiv_comp_map {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F)
    (s : Over.mk (𝟙 X) ⟶
      (MorphismProperty.Over.forget _ _ X).obj ((totalSpaceScheme X).obj E)) :
    totalSpaceSectionEquiv F (s ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map a)) = totalSpaceSectionEquiv E s ≫ a.hom := by
  rw [totalSpaceSectionEquiv_apply, totalSpaceHomEquiv_comp_map, totalSpaceSectionEquiv_apply]
  exact (Category.assoc _ _ _).trans
    (congrArg (totalSpaceHomEquiv E (Over.mk (𝟙 X)) s ≫ ·)
      ((Scheme.Modules.pullbackId X).hom.naturality a.hom)) |>.trans
        (Category.assoc _ _ _).symm

/-- The geometric section associated to the image of a sheaf section is its composite with
the bundle map. -/
@[simp]
theorem totalSpaceSectionEquiv_symm_comp {E F : FiniteLocallyFreeSheaf X} (a : E ⟶ F)
    (s : 𝟙_ X.Modules ⟶ E.obj) :
    (totalSpaceSectionEquiv F).symm (s ≫ a.hom) =
      (totalSpaceSectionEquiv E).symm s ≫ (MorphismProperty.Over.forget _ _ X).map
        ((totalSpaceScheme X).map a) := by
  apply (totalSpaceSectionEquiv F).injective
  simp only [Equiv.apply_symm_apply, totalSpaceSectionEquiv_comp_map]

end

end TauCeti.AlgebraicGeometry
