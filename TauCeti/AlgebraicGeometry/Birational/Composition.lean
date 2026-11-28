/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Composition

/-!
# Composition of partial and rational maps

Mathlib composes a partial or rational map with a morphism on the right (`compHom`) and composes
partial or rational maps with each other (`comp`). This file shows that the two compositions
associate: composing `f.comp g` with a morphism `h` is composing `f` with `g.compHom h`.

It also gives the restriction `compDomainRestrict` of a partial map `f` to the domain of
`f.comp g`, as a morphism into the domain of `g`, and shows that a composite `f.comp g` equal to
the identity rational map is the inclusion of its domain. These are used to build partial
isomorphisms from mutually inverse partial maps.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.comp_compHom` and
  `AlgebraicGeometry.Scheme.RationalMap.comp_compHom`:
  `(f.comp g).compHom h = f.comp (g.compHom h)`.
* `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative_comp_representative`: the
  composite of the representatives of `f` and `g` represents `f.comp g`.
* `AlgebraicGeometry.Scheme.Hom.toRationalMap_comp`: the rational map of a composite of morphisms,
  the first dominant, is the composite of their rational maps.
* `AlgebraicGeometry.Scheme.PartialMap.compDomainRestrict`: the restriction of `f` to the domain of
  `f.comp g`, as a morphism into the domain of `g`, with `compDomainRestrict_hom` and
  `compDomainRestrict_ι`.
* `AlgebraicGeometry.Scheme.PartialMap.comp_hom_eq_ι`: if `f.comp g` is the identity as a rational
  map, its underlying morphism is the inclusion of its domain.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z W : Scheme.{u}} [PreirreducibleSpace X] [Nonempty Y]

/-- Composing a composite of partial maps with a morphism. -/
@[simp]
theorem PartialMap.comp_compHom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (h : Z ⟶ W) : (f.comp g).compHom h = f.comp (g.compHom h) := by
  -- the two domains agree only up to unfolding `compHom`, so `ext` would leave an `isoOfEq` that
  -- `simp` cannot remove; both sides are the same structure up to associativity
  simp only [PartialMap.comp, PartialMap.compHom, Category.assoc]

/-- Composing a composite of rational maps with a morphism. -/
@[simp]
theorem RationalMap.comp_compHom (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) (h : Z ⟶ W) :
    (f.comp g).compHom h = f.comp (g.compHom h) := by
  obtain ⟨g, rfl⟩ := g.exists_rep
  rw [← compHom_toRationalMap, comp_def, comp_def, ← compHom_toRationalMap,
    PartialMap.comp_compHom]

/-- The composite of the representatives of `f` and `g` represents `f.comp g`. -/
theorem RationalMap.toRationalMap_representative_comp_representative (f : X ⤏ Y) [f.IsDominant]
    (g : Y ⤏ Z) : (f.representative.comp g.representative).toRationalMap = f.comp g := by
  rw [← RationalMap.comp_def, g.toRationalMap_representative]

/-- The rational map of a composite `a ≫ b` of morphisms, with `a` dominant, is the composite of
their rational maps. -/
theorem Hom.toRationalMap_comp (a : X ⟶ Y) [IsDominant a] (b : Y ⟶ Z) :
    (a ≫ b).toRationalMap = a.toRationalMap.comp b.toRationalMap := by
  rw [RationalMap.comp_toRationalMap, Hom.toRationalMap, Hom.toRationalMap,
    ← RationalMap.compHom_toRationalMap, Hom.toPartialMap_compHom]

namespace PartialMap

/-- The domain of `F.comp G` lies in the domain of `F`. -/
theorem comp_domain_le (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap Z) :
    (F.comp G).domain ≤ F.domain := by
  rw [comp_domain]
  exact F.domain.ι_image_le _

/-- The restriction of `F` to the domain of `F.comp G`, as a morphism into the domain of `G`. -/
noncomputable def compDomainRestrict (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap Z) :
    (F.comp G).domain.toScheme ⟶ G.domain.toScheme :=
  (F.domain.ι.isoImage (F.hom ⁻¹ᵁ G.domain)).inv ≫ F.hom ∣_ G.domain

/-- `compDomainRestrict F G` followed by `G` is the composite `F.comp G`. -/
theorem compDomainRestrict_hom (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap Z) :
    compDomainRestrict F G ≫ G.hom = (F.comp G).hom := by
  rw [comp_hom, compDomainRestrict]
  -- the domain of `F.comp G` is the image of `F.hom ⁻¹ᵁ G.domain` only up to unfolding, so the
  -- motive of a `Category.assoc` rewrite is not type-correct: apply it as a term instead
  exact Category.assoc _ _ _

/-- `compDomainRestrict F G`, read in `Y`, is `F` on the domain of `F.comp G`. -/
theorem compDomainRestrict_ι (F : X.PartialMap Y) [IsDominant F.hom] (G : Y.PartialMap Z) :
    compDomainRestrict F G ≫ G.domain.ι = X.homOfLE (comp_domain_le F G) ≫ F.hom := by
  rw [compDomainRestrict]
  -- `Category.assoc` is applied as a term for the same reason as in `compDomainRestrict_hom`
  refine (Category.assoc _ _ _).trans ?_
  rw [morphismRestrict_ι]
  exact Opens.isoImage_ι_inv_ι_assoc _ _ _

/-- **A composite that is the identity rational map is the inclusion of its domain.** If
`F.comp G` is the identity as a rational map, its underlying morphism is the inclusion of its
domain: morphisms from a reduced scheme to a separated scheme agreeing on a dense open agree. -/
theorem comp_hom_eq_ι [IsReduced X] [X.IsSeparated] (F : X.PartialMap Y) [IsDominant F.hom]
    (G : Y.PartialMap X) (h : (F.comp G).toRationalMap = RationalMap.id X) :
    (F.comp G).hom = (F.comp G).domain.ι := by
  rw [RationalMap.id, toRationalMap_eq_iff] at h
  simpa using (equiv_toPartialMap_iff_of_isSeparated (Limits.terminal.from X)
    (Limits.terminal.from X) (g := 𝟙 X) (by simp)).1 h

end PartialMap

end AlgebraicGeometry.Scheme
