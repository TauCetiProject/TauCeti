/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Instances
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

/-!
# Descending a pre-adic structure along a surjection

Let `X` be a pre-adic space, `Z` a presheafed space of complete separated topological rings and
`π : X ⟶ Z` a morphism of presheafed spaces which is surjective on points and induces isomorphisms
on all stalks. Then every stalk of `Z` is local, being isomorphic to a stalk of `X`, and each
point `π x` of `Z` receives a valuation, the pullback of the stalk valuation of `X` at `x` along
the stalk map. If these valuations agree for any two points of `X` with the same image, they make
`Z` a pre-adic space `X.descend π`, and `π` a morphism of pre-adic spaces `X ⟶ X.descend π`.

The typical source of the agreement hypothesis is a group of automorphisms of `X` acting
transitively on the fibres of `π` and commuting with `π`: a morphism of pre-adic spaces `g : X ⟶ X`
with `g ≫ π = π` carries the valuation descended from `x` to the one descended from `g x`
(`comap_stalkMap_base_eq_of_comp_eq`). This is how a quotient of a pre-adic space by a group
acting with wandering neighbourhoods, such as the adic Fargues–Fontaine curve, becomes a pre-adic
space.

## Main definitions

* `TauCeti.PreAdicSpace.descend`: the pre-adic space with underlying presheafed space `Z`.
* `TauCeti.PreAdicSpace.toDescend`: `π` as a morphism of pre-adic spaces `X ⟶ X.descend π`.

## Main results

* `TauCeti.PreAdicSpace.stalkValuation_descend_base`: the stalk valuation of `X.descend π` at
  `π x` is the pullback of the stalk valuation of `X` at `x`.
* `TauCeti.PreAdicSpace.comap_stalkMap_base_eq_of_comp_eq`: a pre-adic endomorphism `g` of `X`
  with `g ≫ π = π` preserves the valuations descended along `π`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1, for the category `𝒱^pre`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

namespace PreAdicSpace

/-- Forgetting the topology on the sections of a presheaf of complete separated rings. -/
local notation "forgetTop" =>
  TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat

variable {X : PreAdicSpace.{u}} {Z : PresheafedSpace CompleteSeparatedTopCommRingCat.{u}}
  {π : X.toPresheafedSpace ⟶ Z}
variable (hsurj : Function.Surjective π.base)
  (hiso : ∀ x, IsIso ((toRingPresheafedSpaceHom π).stalkMap x))
  (hcompat : ∀ (x x' : X) (h : π.base x = π.base x'),
    ValuationSpectrum.comap ((toRingPresheafedSpaceHom π).stalkMap x').hom (X.stalkValuation x') =
      ValuationSpectrum.comap (eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
          h.symm)).hom
        (ValuationSpectrum.comap ((toRingPresheafedSpaceHom π).stalkMap x).hom
          (X.stalkValuation x)))

-- The construction is exposed, as `PreAdicSpace.restrict` is: a point of `X.descend π` must be a
-- point of `Z`, and its stalk the stalk of `Z`, for statements about `π` as a morphism into the
-- descended space to typecheck.
@[expose] public section DescendDef

/-- The stalk of `Z` at `z` is identified with the stalk of `X` at the preimage
`Function.surjInv hsurj z` of `z`, through the stalk map of `π`. This is the identification
through which `descend` transports local rings and valuations. -/
noncomputable def descendStalkIso (z : Z) :
    ((forgetTop).mapPresheaf.obj Z).presheaf.stalk z ≅
      X.toRingPresheafedSpace.presheaf.stalk (Function.surjInv hsurj z) :=
  eqToIso (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
      (Function.surjInv_eq hsurj z).symm) ≪≫
    @asIso _ _ _ _ ((toRingPresheafedSpaceHom π).stalkMap (Function.surjInv hsurj z))
      (hiso (Function.surjInv hsurj z))

variable (X π) in
/-- **The pre-adic structure descended along `π`.** For a morphism of presheafed spaces
`π : X ⟶ Z` from a pre-adic space, surjective on points and with invertible stalk maps, the
presheafed space `Z` with its stalks, local through `descendStalkIso`, and the valuation at `z`
descended from the preimage `Function.surjInv hsurj z`. When two points of `X` with the same image
induce the same valuation on the stalk of `Z` (`hcompat`), the valuation at `π x` is the one
descended from `x` (`stalkValuation_descend_base`), and `π` is a morphism of pre-adic spaces
(`toDescend`). -/
noncomputable def descend : PreAdicSpace.{u} where
  toPresheafedSpace := Z
  isLocalRing z := by
    obtain ⟨x, rfl⟩ := hsurj z
    have := hiso x
    exact (asIso ((toRingPresheafedSpaceHom π).stalkMap x)).symm.commRingCatIsoToRingEquiv
      |>.isLocalRing
  valuation z :=
    letI : IsLocalRing (X.toRingPresheafedSpace.presheaf.stalk (Function.surjInv hsurj z)) :=
      X.isLocalRing _
    letI : IsLocalRing (((forgetTop).mapPresheaf.obj Z).presheaf.stalk z) :=
      (descendStalkIso hsurj hiso z).symm.commRingCatIsoToRingEquiv.isLocalRing
    haveI := isLocalHom_of_isIso (descendStalkIso hsurj hiso z).hom
    ValuationSpectrum.comap (IsLocalRing.ResidueField.map (descendStalkIso hsurj hiso z).hom.hom)
      (X.valuation (Function.surjInv hsurj z))

end DescendDef

/-- `descendStalkIso` is the identification of the stalks at `z` and at `π` of its preimage,
followed by the stalk map of `π`. -/
theorem descendStalkIso_hom (z : Z) :
    (descendStalkIso hsurj hiso z).hom =
      eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
        (Function.surjInv_eq hsurj z).symm) ≫
        (toRingPresheafedSpaceHom π).stalkMap (Function.surjInv hsurj z) :=
  (rfl)

/-- The presheafed space underlying the descended pre-adic space is `Z`. -/
@[simp]
theorem descend_toPresheafedSpace :
    (X.descend π hsurj hiso).toPresheafedSpace = Z :=
  (rfl)

/-- The stalk valuation of the descended space at `z` is the stalk valuation of `X` at the chosen
preimage of `z`, pulled back to the stalk of `Z`. -/
private theorem stalkValuation_descend (z : X.descend π hsurj hiso) :
    (X.descend π hsurj hiso).stalkValuation z =
      ValuationSpectrum.comap (descendStalkIso hsurj hiso z).hom.hom
        (X.stalkValuation (Function.surjInv hsurj z)) := by
  rw [stalkValuation_def, stalkValuation_def]
  -- the stalk of `X` at the preimage is not syntactically a stalk at a point of `X`, so the
  -- local-ring and local-homomorphism instances chosen in `descend` are supplied by hand
  have : IsLocalRing (X.toRingPresheafedSpace.presheaf.stalk (Function.surjInv hsurj z)) :=
    X.isLocalRing _
  exact @ValuationSpectrum.comap_residue_comap_residueFieldMap _ _ _ _
    (descendStalkIso hsurj hiso z).symm.commRingCatIsoToRingEquiv.isLocalRing _ _
    (isLocalHom_of_isIso _) _

/-- **Endomorphisms over `Z` preserve the descended valuations.** If a morphism of pre-adic spaces
`g : X ⟶ X` satisfies `g ≫ π = π`, the valuation on the stalk of `Z` at `π x = π (g x)` descended
from `g x` is the one descended from `x`. This supplies the compatibility hypothesis of `descend`
when such endomorphisms act transitively on the fibres of `π`. -/
theorem comap_stalkMap_base_eq_of_comp_eq (g : X ⟶ X) (hg : g.toHom ≫ π = π) (x : X)
    (h : π.base x = π.base (g.base x)) :
    ValuationSpectrum.comap ((toRingPresheafedSpaceHom π).stalkMap (g.base x)).hom
        (X.stalkValuation (g.base x)) =
      ValuationSpectrum.comap (eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
          h.symm)).hom
        (ValuationSpectrum.comap ((toRingPresheafedSpaceHom π).stalkMap x).hom
          (X.stalkValuation x)) := by
  -- the stalk map of `g ≫ π` at `x`, computed once as a composite and once from `g ≫ π = π`
  have hcomp : (toRingPresheafedSpaceHom π).stalkMap (g.base x) ≫
      (toRingPresheafedSpaceHom g.toHom).stalkMap x =
      eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk h.symm) ≫
        (toRingPresheafedSpaceHom π).stalkMap x :=
    (PresheafedSpace.stalkMap.comp (toRingPresheafedSpaceHom g.toHom)
      (toRingPresheafedSpaceHom π) x).symm.trans
      (PresheafedSpace.stalkMap.congr_hom _ _
        (((forgetTop).mapPresheaf.map_comp g.toHom π).symm.trans
          (congrArg (forgetTop).mapPresheaf.map hg)) x)
  -- points of `X` and of its presheafed space of rings are identified only up to unfolding, so the
  -- chain is assembled as a term rather than by rewriting
  exact ((congrArg (ValuationSpectrum.comap _) (g.stalkValuation_eq x)).trans
    (ValuationSpectrum.comap_hom_comap_hom _ _ _)).trans
      ((congrArg (fun f ↦ ValuationSpectrum.comap f.hom (X.stalkValuation x)) hcomp).trans
        (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm)

include hcompat in
/-- **The stalk valuation of the descended space at `π x`** is the stalk valuation of `X` at `x`,
pulled back along the stalk map of `π`. -/
theorem stalkValuation_descend_base (x : X) :
    (X.descend π hsurj hiso).stalkValuation (π.base x) =
      ValuationSpectrum.comap ((toRingPresheafedSpaceHom π).stalkMap x).hom
        (X.stalkValuation x) := by
  refine (stalkValuation_descend hsurj hiso (π.base x)).trans ?_
  rw [hcompat (Function.surjInv hsurj (π.base x)) x (Function.surjInv_eq hsurj _),
    descendStalkIso_hom]
  exact (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm

/-- **`π` as a morphism of pre-adic spaces** into the descended space. -/
noncomputable def toDescend : X ⟶ X.descend π hsurj hiso where
  toHom := π
  stalkValuation_eq x := stalkValuation_descend_base hsurj hiso hcompat x

/-- The morphism of presheafed spaces underlying `toDescend` is `π`. -/
@[simp]
theorem toDescend_toHom : (toDescend hsurj hiso hcompat).toHom = π :=
  (rfl)

end PreAdicSpace

end TauCeti

end
