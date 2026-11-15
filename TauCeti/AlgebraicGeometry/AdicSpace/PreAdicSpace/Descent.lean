/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Instances
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Hom

/-!
# Descending a pre-adic structure along a jointly surjective family

Let `X i` be a family of pre-adic spaces, `Z` a presheafed space of complete separated topological
rings and `π i : X i ⟶ Z` morphisms of presheafed spaces which are jointly surjective on points
and induce isomorphisms on all stalks. Then every stalk of `Z` is local, being isomorphic to a
stalk of some `X i`, and each point `π i x` of `Z` receives a valuation, the pullback of the stalk
valuation of `X i` at `x` along the stalk map. If these valuations agree for any two points with
the same image, they make `Z` a pre-adic space `descend X π`, and every `π i` a morphism of
pre-adic spaces `X i ⟶ descend X π`.

The agreement hypothesis holds as soon as any two points with the same image come from a common
point `w` of a pre-adic space `W`, through morphisms of pre-adic spaces `g₁ : W ⟶ X i` and
`g₂ : W ⟶ X j` with `g₁ ≫ π i = g₂ ≫ π j` (`comap_stalkMap_base_eq_of_comp_eq`). Two cases of
this are the following.

* A single surjection `π : X ⟶ Z`, the family indexed by `Unit`, with a group of automorphisms
  `g` of `X` acting transitively on the fibres of `π` and satisfying `g ≫ π = π`. This is how a
  quotient of a pre-adic space by a group acting with wandering neighbourhoods, such as the adic
  Fargues–Fontaine curve, becomes a pre-adic space.
* The charts `U i ⟶ Z` of a presheafed space glued from pre-adic spaces along open immersions,
  where two points with the same image come from a point of an overlap `V i j`. This is how glued
  pre-adic spaces are constructed (`TauCeti.PreAdicSpace.GlueData`).

## Main definitions

* `TauCeti.PreAdicSpace.descend`: the pre-adic space with underlying presheafed space `Z`.
* `TauCeti.PreAdicSpace.toDescend`: `π i` as a morphism of pre-adic spaces `X i ⟶ descend X π`.

## Main results

* `TauCeti.PreAdicSpace.stalkValuation_descend_base`: the stalk valuation of `descend X π` at
  `π i x` is the pullback of the stalk valuation of `X i` at `x`.
* `TauCeti.PreAdicSpace.comap_stalkMap_base_eq_of_comp_eq`: points with the same image under `π`
  that come from a common point through morphisms of pre-adic spaces induce the same valuation.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1, for the category `𝒱^pre`.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u v

namespace PreAdicSpace

/-- Forgetting the topology on the sections of a presheaf of complete separated rings. -/
local notation "forgetTop" =>
  TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat

variable {ι : Type v} {X : ι → PreAdicSpace.{u}}
  {Z : PresheafedSpace CompleteSeparatedTopCommRingCat.{u}} {π : ∀ i, (X i).toPresheafedSpace ⟶ Z}
variable (hsurj : ∀ z : Z, ∃ (i : ι) (x : X i), (π i).base x = z)
  (hiso : ∀ (i : ι) (x : X i), IsIso ((toRingPresheafedSpaceHom (π i)).stalkMap x))
  (hcompat : ∀ (i j : ι) (x : X i) (x' : X j) (h : (π i).base x = (π j).base x'),
    ValuationSpectrum.comap ((toRingPresheafedSpaceHom (π j)).stalkMap x').hom
        ((X j).stalkValuation x') =
      ValuationSpectrum.comap (eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
          h.symm)).hom
        (ValuationSpectrum.comap ((toRingPresheafedSpaceHom (π i)).stalkMap x).hom
          ((X i).stalkValuation x)))

-- The construction is exposed, as `PreAdicSpace.restrict` is: a point of `descend X π` must be a
-- point of `Z`, and its stalk the stalk of `Z`, for statements about `π i` as a morphism into the
-- descended space to typecheck.
@[expose] public section DescendDef

/-- The stalk of `Z` at `z` is identified with the stalk of `X i` at a chosen preimage `x` of `z`,
`π i x = z`, through the stalk map of `π i`. This is the identification through which `descend`
transports local rings and valuations. -/
noncomputable def descendStalkIso (z : Z) :
    ((forgetTop).mapPresheaf.obj Z).presheaf.stalk z ≅
      (X (hsurj z).choose).toRingPresheafedSpace.presheaf.stalk (hsurj z).choose_spec.choose :=
  eqToIso (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
      (hsurj z).choose_spec.choose_spec.symm) ≪≫
    @asIso _ _ _ _ ((toRingPresheafedSpaceHom (π _)).stalkMap (hsurj z).choose_spec.choose)
      (hiso _ _)

variable (X π) in
/-- **The pre-adic structure descended along `π`.** For morphisms of presheafed spaces
`π i : X i ⟶ Z` from pre-adic spaces, jointly surjective on points and with invertible stalk
maps, the presheafed space `Z` with its stalks, local through `descendStalkIso`, and the valuation
at `z` descended from a chosen preimage of `z`. When two points with the same image induce the
same valuation on the stalk of `Z` (`hcompat`), the valuation at `π i x` is the one descended from
`x` (`stalkValuation_descend_base`), and every `π i` is a morphism of pre-adic spaces
(`toDescend`). -/
noncomputable def descend : PreAdicSpace.{u} where
  toPresheafedSpace := Z
  isLocalRing z := by
    obtain ⟨i, x, rfl⟩ := hsurj z
    have := hiso i x
    exact (asIso ((toRingPresheafedSpaceHom (π i)).stalkMap x)).symm.commRingCatIsoToRingEquiv
      |>.isLocalRing
  valuation z :=
    letI : IsLocalRing (((forgetTop).mapPresheaf.obj Z).presheaf.stalk z) :=
      (descendStalkIso hsurj hiso z).symm.commRingCatIsoToRingEquiv.isLocalRing
    haveI := isLocalHom_of_isIso (descendStalkIso hsurj hiso z).hom
    ValuationSpectrum.comap (IsLocalRing.ResidueField.map (descendStalkIso hsurj hiso z).hom.hom)
      ((X _).valuation _)

end DescendDef

/-- `descendStalkIso` is the identification of the stalks at `z` and at `π i` of its chosen
preimage, followed by the stalk map of `π i`. -/
theorem descendStalkIso_hom (z : Z) :
    (descendStalkIso hsurj hiso z).hom =
      eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
        (hsurj z).choose_spec.choose_spec.symm) ≫
        (toRingPresheafedSpaceHom (π _)).stalkMap (hsurj z).choose_spec.choose :=
  (rfl)

/-- The presheafed space underlying the descended pre-adic space is `Z`. -/
@[simp]
theorem descend_toPresheafedSpace :
    (descend X π hsurj hiso).toPresheafedSpace = Z :=
  (rfl)

/-- The stalk valuation of the descended space at `z` is the stalk valuation of `X i` at the
chosen preimage of `z`, pulled back to the stalk of `Z`. -/
private theorem stalkValuation_descend (z : descend X π hsurj hiso) :
    (descend X π hsurj hiso).stalkValuation z =
      ValuationSpectrum.comap (descendStalkIso hsurj hiso z).hom.hom
        ((X _).stalkValuation (hsurj z).choose_spec.choose) := by
  rw [stalkValuation_def, stalkValuation_def]
  exact @ValuationSpectrum.comap_residue_comap_residueFieldMap _ _ _ _
    (descendStalkIso hsurj hiso z).symm.commRingCatIsoToRingEquiv.isLocalRing _ _
    (isLocalHom_of_isIso _) _

/-- **Points coming from a common point induce the same valuation.** If morphisms of pre-adic
spaces `g₁ : W ⟶ X i` and `g₂ : W ⟶ X j` satisfy `g₁ ≫ π i = g₂ ≫ π j`, then for every point `w`
of `W` the valuations on the stalk of `Z` at `π i (g₁ w) = π j (g₂ w)` descended from `g₁ w` and
from `g₂ w` agree. This supplies the compatibility hypothesis of `descend`: for a group of
automorphisms of a single `X` over `Z` with `g₁ = 𝟙`, and for glued spaces with `W` an overlap. -/
theorem comap_stalkMap_base_eq_of_comp_eq {W : PreAdicSpace.{u}} {i j : ι} (g₁ : W ⟶ X i)
    (g₂ : W ⟶ X j) (hg : g₁.toHom ≫ π i = g₂.toHom ≫ π j) (w : W)
    (h : (π i).base (g₁.base w) = (π j).base (g₂.base w)) :
    ValuationSpectrum.comap ((toRingPresheafedSpaceHom (π j)).stalkMap (g₂.base w)).hom
        ((X j).stalkValuation (g₂.base w)) =
      ValuationSpectrum.comap (eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk
          h.symm)).hom
        (ValuationSpectrum.comap ((toRingPresheafedSpaceHom (π i)).stalkMap (g₁.base w)).hom
          ((X i).stalkValuation (g₁.base w))) := by
  -- the stalk map of `g₂ ≫ π j = g₁ ≫ π i` at `w`, computed as a composite in two ways
  have hcomp : (toRingPresheafedSpaceHom (π j)).stalkMap (g₂.base w) ≫
      (toRingPresheafedSpaceHom g₂.toHom).stalkMap w =
      eqToHom (congrArg ((forgetTop).mapPresheaf.obj Z).presheaf.stalk h.symm) ≫
        (toRingPresheafedSpaceHom (π i)).stalkMap (g₁.base w) ≫
          (toRingPresheafedSpaceHom g₁.toHom).stalkMap w :=
    -- the points `g₁ w`, `g₂ w` occur in the types of the stalk maps, so the stalk-map lemmas are
    -- chained as terms rather than rewritten
    (PresheafedSpace.stalkMap.comp (toRingPresheafedSpaceHom g₂.toHom)
      (toRingPresheafedSpaceHom (π j)) w).symm.trans
      ((PresheafedSpace.stalkMap.congr_hom _ _
        (((forgetTop).mapPresheaf.map_comp g₂.toHom (π j)).symm.trans
          ((congrArg (forgetTop).mapPresheaf.map hg.symm).trans
            ((forgetTop).mapPresheaf.map_comp g₁.toHom (π i)))) w).trans
        (congrArg (eqToHom _ ≫ ·) (PresheafedSpace.stalkMap.comp
          (toRingPresheafedSpaceHom g₁.toHom) (toRingPresheafedSpaceHom (π i)) w)))
  -- points of `W` and of its presheafed space of rings are identified only up to unfolding, so
  -- the chain is assembled as a term rather than by rewriting
  exact ((congrArg (ValuationSpectrum.comap _) (g₂.stalkValuation_eq w)).trans
    (ValuationSpectrum.comap_hom_comap_hom _ _ _)).trans
      ((congrArg (fun f ↦ ValuationSpectrum.comap f.hom (W.stalkValuation w)) hcomp).trans
        ((ValuationSpectrum.comap_hom_comap_hom _ _ _).symm.trans
          (congrArg (ValuationSpectrum.comap _)
            ((ValuationSpectrum.comap_hom_comap_hom _ _ _).symm.trans
              (congrArg (ValuationSpectrum.comap _) (g₁.stalkValuation_eq w).symm)))))

include hcompat in
/-- **The stalk valuation of the descended space at `π i x`** is the stalk valuation of `X i` at
`x`, pulled back along the stalk map of `π i`. -/
theorem stalkValuation_descend_base (i : ι) (x : X i) :
    (descend X π hsurj hiso).stalkValuation ((π i).base x) =
      ValuationSpectrum.comap ((toRingPresheafedSpaceHom (π i)).stalkMap x).hom
        ((X i).stalkValuation x) := by
  refine (stalkValuation_descend hsurj hiso ((π i).base x)).trans ?_
  rw [hcompat _ i _ x (hsurj ((π i).base x)).choose_spec.choose_spec, descendStalkIso_hom]
  exact (ValuationSpectrum.comap_hom_comap_hom _ _ _).symm

-- The morphism is exposed, as `descend` is: its underlying morphism must be definitionally `π i`
-- where a diagram of these morphisms is compared with the diagram of the `π i` in presheafed
-- spaces, as for the charts of glued spaces, and `toDescend_toHom` cannot be rewritten there.
/-- **`π i` as a morphism of pre-adic spaces** into the descended space. -/
@[expose] noncomputable def toDescend (i : ι) : X i ⟶ descend X π hsurj hiso where
  toHom := π i
  stalkValuation_eq x := stalkValuation_descend_base hsurj hiso hcompat i x

/-- The morphism of presheafed spaces underlying `toDescend` is `π i`. -/
@[simp]
theorem toDescend_toHom (i : ι) : (toDescend hsurj hiso hcompat i).toHom = π i :=
  (rfl)

end PreAdicSpace

end TauCeti

end
