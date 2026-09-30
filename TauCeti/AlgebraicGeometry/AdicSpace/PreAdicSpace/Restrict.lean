/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Instances
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

/-!
# Restriction of pre-adic spaces to open subspaces

For a pre-adic space `X` and an open embedding `f : U ⟶ X` of topological spaces, the
restriction `X.restrict h` is the pre-adic space on `U` whose presheaf is the restriction of
the presheaf of `X`. Its stalk at `x` is the stalk of `X` at `f x`, and its valuation at `x` is
the valuation of `X` at `f x`, transported along this identification. The canonical morphism
`X.ofRestrict h : X.restrict h ⟶ X` is a morphism of pre-adic spaces.

Restrictions are the infrastructure for the locally affinoid condition, which is not defined
here: an adic space will be a pre-adic space admitting an open cover whose members, with the
restricted structure, are isomorphic in `𝒱^pre` to affinoid pre-adic spaces. A general
`PreAdicSpace` carries no such cover. The canonical morphism is a monomorphism whose stalk maps
are isomorphisms, and the restriction of `X` to the whole space is isomorphic to `X`, because
the forgetful functor to presheafed spaces reflects isomorphisms. An isomorphism `X ≅ Y` carries
the restriction of `X` to an open `U` isomorphically onto the restriction of `Y` to the image of
`U`: the two open immersions into `Y` have the same range, so Mathlib's
`PresheafedSpace.IsOpenImmersion.isoOfRangeEq` identifies the underlying presheafed spaces, and the
identification is a morphism of pre-adic spaces because it factors one through the other.

## Main definitions

* `TauCeti.PreAdicSpace.restrict`: the restriction of a pre-adic space along an open embedding.
* `TauCeti.PreAdicSpace.ofRestrict`: the canonical morphism from the restriction.
* `TauCeti.PreAdicSpace.restrictStalkIso`: the stalk of the restriction at `x` is the stalk of
  `X` at `f x`.
* `TauCeti.PreAdicSpace.restrictTopIso`: the restriction to the whole space is isomorphic to
  `X`.
* `TauCeti.PreAdicSpace.restrictIso`: the transport of a restriction along an isomorphism.

The design follows `AlgebraicGeometry.LocallyRingedSpace.restrict`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace ValuationSpectrum

variable {P Q : PresheafedSpace CommRingCat.{u}}

/-- Pulling a valuation on a stalk of `P` back along the stalk map of `P.ofRestrict h` and then
along the stalk identification of the restriction returns the valuation. -/
theorem comap_stalkMap_ofRestrict_comap_restrictStalkIso {U : TopCat.{u}}
    {f : U ⟶ (P : TopCat.{u})} (h : IsOpenEmbedding f) (x : U)
    (v : Spv (P.presheaf.stalk (f x))) :
    comap ((P.ofRestrict h).stalkMap x).hom (comap (P.restrictStalkIso h x).hom.hom v) = v := by
  rw [comap_hom_comap_hom, ← PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict]
  -- The point `x` of `U` is a point of the restriction only up to unfolding, so the
  -- cancellation and the identity law are applied as terms rather than rewritten.
  exact (congrArg (fun φ => comap (CommRingCat.Hom.hom φ) v) (Iso.inv_hom_id _)).trans
    (congrFun comap_id v)

end ValuationSpectrum

namespace PreAdicSpace

section Restrict

variable {U : TopCat.{u}} (X : PreAdicSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

-- The restriction is exposed, as the category structure is: a point of `X.restrict h` must
-- unfold to a point of `U` for statements about the restriction to typecheck.
@[expose] public section RestrictDef

/-- The restriction of a pre-adic space along an open embedding `f : U ⟶ X`. The presheaf is
the restriction of the presheaf of `X`; the stalk at `x` is identified with the stalk of `X` at
`f x`, and the valuation at `x` is the valuation of `X` at `f x` transported along this
identification. -/
noncomputable def restrict : PreAdicSpace.{u} where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  isLocalRing x :=
    @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x)) _
      (X.toRingPresheafedSpace.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  valuation x :=
    -- Mathlib's stalk identification is typed at the ring level, where `f x` is not
    -- syntactically a point of `X`, so the local-ring instances are passed explicitly.
    letI i : IsLocalRing (X.toRingPresheafedSpace.presheaf.stalk (f x)) := X.isLocalRing (f x)
    letI i' := @RingEquiv.isLocalRing _ _ _ i _
      (X.toRingPresheafedSpace.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
    ValuationSpectrum.comap
      (@IsLocalRing.ResidueField.map _ _ _ i' _ i
        (X.toRingPresheafedSpace.restrictStalkIso h x).hom.hom inferInstance)
      (X.valuation (f x))

end RestrictDef

@[simp]
theorem restrict_toPresheafedSpace :
    (X.restrict h).toPresheafedSpace = X.toPresheafedSpace.restrict h := by
  rfl

/-- The presheaf of rings of the restriction is the restriction of the presheaf of rings. -/
theorem restrict_toRingPresheafedSpace :
    (X.restrict h).toRingPresheafedSpace = X.toRingPresheafedSpace.restrict h := by
  rfl

/-- The stalk of the restriction at `x` is the stalk of `X` at `f x`. -/
noncomputable def restrictStalkIso (x : X.restrict h) :
    (X.restrict h).toRingPresheafedSpace.presheaf.stalk x ≅
      X.toRingPresheafedSpace.presheaf.stalk (f x) :=
  X.toRingPresheafedSpace.restrictStalkIso h x

/-- The stalk identification is Mathlib's, for the underlying presheafed spaces of rings. -/
theorem restrictStalkIso_def (x : X.restrict h) :
    X.restrictStalkIso h x = X.toRingPresheafedSpace.restrictStalkIso h x := by
  rfl

/-- The valuation of the restriction at `x` is the valuation of `X` at `f x`, pulled back along
the residue-field map of the stalk identification. -/
@[simp]
theorem valuation_restrict (x : X.restrict h) :
    (X.restrict h).valuation x =
      ValuationSpectrum.comap (IsLocalRing.ResidueField.map (X.restrictStalkIso h x).hom.hom)
        (X.valuation (f x)) := by
  rfl

/-- The stalk valuation of the restriction at `x` is the stalk valuation of `X` at `f x`,
pulled back along the stalk identification. -/
@[simp]
theorem stalkValuation_restrict (x : X.restrict h) :
    (X.restrict h).stalkValuation x =
      ValuationSpectrum.comap (X.restrictStalkIso h x).hom.hom (X.stalkValuation (f x)) := by
  rw [stalkValuation_def, stalkValuation_def, valuation_restrict,
    ← Function.comp_apply (f := ValuationSpectrum.comap _), ← ValuationSpectrum.comap_comp,
    IsLocalRing.ResidueField.map_comp_residue, ValuationSpectrum.comap_comp, Function.comp_apply]

-- The canonical morphism is exposed, as Mathlib's `LocallyRingedSpace.ofRestrict` is, so that
-- its base map unfolds to `f`: the stalk map of `X.ofRestrict h` at `x` is typed at the point
-- `(X.ofRestrict h).base x` of `X`, and identifying it with a map out of the stalk at `f x`, as
-- `restrictStalkIso_inv_eq_ofRestrict` does, needs the two points to be definitionally equal.
-- The propositional `ofRestrict_base` cannot rewrite inside the type of the stalk map.
@[expose] public section OfRestrictDef

/-- The canonical morphism from the restriction of a pre-adic space along an open embedding. -/
noncomputable def ofRestrict : X.restrict h ⟶ X where
  toHom := X.toPresheafedSpace.ofRestrict h
  stalkValuation_eq x := by
    -- Stated for a point of the restriction, where the rewrites below typecheck; the field's
    -- point ranges over the presheafed space of rings and is definitionally the same.
    have key : ∀ y : X.restrict h, X.stalkValuation (f y) =
        ValuationSpectrum.comap ((X.toRingPresheafedSpace.ofRestrict h).stalkMap y).hom
          ((X.restrict h).stalkValuation y) := by
      intro y
      rw [stalkValuation_restrict, restrictStalkIso_def]
      exact (ValuationSpectrum.comap_stalkMap_ofRestrict_comap_restrictStalkIso h y _).symm
    exact key x

end OfRestrictDef

@[simp]
theorem ofRestrict_toHom : (X.ofRestrict h).toHom = X.toPresheafedSpace.ofRestrict h := by
  rfl

theorem ofRestrict_base : (X.ofRestrict h).base = f := by
  rfl

/-- The inverse of the stalk identification is the stalk map of `X.ofRestrict h`. -/
theorem restrictStalkIso_inv_eq_ofRestrict (x : X.restrict h) :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x := by
  rw [Hom.stalkMap_def, restrictStalkIso_def]
  exact PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toRingPresheafedSpace h x

/-- The stalk maps of `X.ofRestrict h` are isomorphisms. -/
instance (x : X.restrict h) : IsIso ((X.ofRestrict h).stalkMap x) :=
  restrictStalkIso_inv_eq_ofRestrict X h x ▸ (X.restrictStalkIso h x).isIso_inv

/-- The canonical morphism from a restriction is a monomorphism, as its underlying morphism of
presheafed spaces is. -/
instance : Mono (X.ofRestrict h) :=
  forgetToPresheafedSpace.mono_of_mono_map (PresheafedSpace.ofRestrict_mono X.toPresheafedSpace f h)

/-- The restriction of a pre-adic space to the whole space is isomorphic to the space. -/
noncomputable def restrictTopIso : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  haveI := isIso_of_isIso_toHom (X.ofRestrict (Opens.isOpenEmbedding ⊤))
    (hf := (PresheafedSpace.restrictTopIso X.toPresheafedSpace).isIso_hom)
  asIso (X.ofRestrict (Opens.isOpenEmbedding ⊤))

@[simp]
theorem restrictTopIso_hom : X.restrictTopIso.hom = X.ofRestrict (Opens.isOpenEmbedding ⊤) := by
  rfl

end Restrict

section RestrictIso

variable {X Y : PreAdicSpace.{u}} (e : X ≅ Y) (U : Opens X)

-- The image of an open of `X` under an isomorphism `e : X ≅ Y` is the preimage under the
-- inverse, `e` being a homeomorphism on the underlying spaces; it is the range of the restriction
-- of `X` to `U` followed by `e`.
private theorem range_ofRestrict_comp_base :
    Set.range (X.toPresheafedSpace.ofRestrict U.isOpenEmbedding ≫ e.hom.toHom).base =
      Set.range (Y.toPresheafedSpace.ofRestrict
        ((Opens.map e.inv.base).obj U).isOpenEmbedding).base := by
  -- Both sides are ranges of inclusions of opens, composed with `e` on the left. The passage
  -- from `(ofRestrict ≫ e.hom.toHom).base` to `e.hom.base ∘ Opens.inclusion' U` is the pair of
  -- `rfl`-lemmas `PresheafedSpace.comp_base` and `PresheafedSpace.ofRestrict_base`, but it cannot
  -- be performed by rewriting: the source of `ofRestrict_base`'s right-hand side is the open
  -- `(Opens.toTopCat X).obj U`, while the source of the left-hand side is the carrier of
  -- `X.toPresheafedSpace.restrict _`, which unfolds to it only at default transparency, so the
  -- rewritten composite is ill-typed for `rw` and `TopCat.coe_comp` no longer fires on it.
  change Set.range (e.hom.base ∘ Opens.inclusion' U) = Set.range (Opens.inclusion' _)
  rw [Set.range_comp, Opens.set_range_inclusion', Opens.set_range_inclusion', Opens.map_coe]
  exact (TopCat.homeoOfIso (forgetToTop.mapIso e)).image_eq_preimage_symm (U : Set X)

/-- The underlying isomorphism of presheafed spaces of `restrictIso`: the two open immersions
`X.restrict U ⟶ X ⟶ Y` and `Y.restrict e(U) ⟶ Y` have the same range. -/
private noncomputable def restrictIsoPresheafedSpace :
    X.toPresheafedSpace.restrict U.isOpenEmbedding ≅
      Y.toPresheafedSpace.restrict ((Opens.map e.inv.base).obj U).isOpenEmbedding :=
  PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (X.toPresheafedSpace.ofRestrict U.isOpenEmbedding ≫ e.hom.toHom)
    (Y.toPresheafedSpace.ofRestrict ((Opens.map e.inv.base).obj U).isOpenEmbedding)
    (range_ofRestrict_comp_base e U)

private theorem restrictIsoPresheafedSpace_hom_ofRestrict :
    (restrictIsoPresheafedSpace e U).hom ≫
        Y.toPresheafedSpace.ofRestrict ((Opens.map e.inv.base).obj U).isOpenEmbedding =
      X.toPresheafedSpace.ofRestrict U.isOpenEmbedding ≫ e.hom.toHom :=
  PresheafedSpace.IsOpenImmersion.lift_fac _ _ (le_of_eq (range_ofRestrict_comp_base e U))

-- The isomorphism of presheafed spaces factors `X.ofRestrict ≫ e.hom` through `Y.ofRestrict`,
-- whose stalk maps are isomorphisms, so it is a morphism of pre-adic spaces.
private noncomputable def restrictHom :
    X.restrict U.isOpenEmbedding ⟶ Y.restrict ((Opens.map e.inv.base).obj U).isOpenEmbedding :=
  Hom.ofFac (X.ofRestrict U.isOpenEmbedding ≫ e.hom)
    (Y.ofRestrict ((Opens.map e.inv.base).obj U).isOpenEmbedding)
    (restrictIsoPresheafedSpace e U).hom (restrictIsoPresheafedSpace_hom_ofRestrict e U)

private theorem restrictHom_toHom :
    (restrictHom e U).toHom = (restrictIsoPresheafedSpace e U).hom :=
  Hom.ofFac_toHom _ _ _ _

/-- An isomorphism `e : X ≅ Y` of pre-adic spaces restricts to an isomorphism from the
restriction of `X` to an open `U` onto the restriction of `Y` to the image of `U`. It is the
unique morphism compatible with the canonical morphisms from the restrictions
(`restrictIso_hom_ofRestrict`). -/
noncomputable def restrictIso :
    X.restrict U.isOpenEmbedding ≅ Y.restrict ((Opens.map e.inv.base).obj U).isOpenEmbedding :=
  haveI := isIso_of_isIso_toHom (restrictHom e U)
    (hf := restrictHom_toHom e U ▸ (restrictIsoPresheafedSpace e U).isIso_hom)
  asIso (restrictHom e U)

private theorem restrictIso_hom : (restrictIso e U).hom = restrictHom e U := rfl

/-- The transported restriction composed with the canonical morphism from the restriction of
`Y` is the canonical morphism from the restriction of `X` followed by `e`. -/
@[reassoc (attr := simp)]
theorem restrictIso_hom_ofRestrict :
    (restrictIso e U).hom ≫ Y.ofRestrict ((Opens.map e.inv.base).obj U).isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding ≫ e.hom := by
  apply Hom.ext'
  rw [comp_toHom, comp_toHom, restrictIso_hom, restrictHom_toHom]
  exact restrictIsoPresheafedSpace_hom_ofRestrict e U

/-- The inverse of the transported restriction composed with the canonical morphism from the
restriction of `X` is the canonical morphism from the restriction of `Y` followed by `e⁻¹`. -/
@[reassoc (attr := simp)]
theorem restrictIso_inv_ofRestrict :
    (restrictIso e U).inv ≫ X.ofRestrict U.isOpenEmbedding =
      Y.ofRestrict ((Opens.map e.inv.base).obj U).isOpenEmbedding ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, restrictIso_hom_ofRestrict, Category.assoc,
    e.hom_inv_id, Category.comp_id]

end RestrictIso

end PreAdicSpace

end TauCeti

end
