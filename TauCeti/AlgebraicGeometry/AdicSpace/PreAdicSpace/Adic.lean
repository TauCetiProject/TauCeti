/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen

/-!
# Adic spaces and open adic subspaces

An *adic space* is an object of `𝒱`, a pre-adic space whose structure presheaf is a sheaf, that
admits an open cover by affinoid adic spaces; since the restriction of a sheaf to an open subspace
is a sheaf, this is the condition that the object is sheafy and locally affinoid. Their full
subcategory of `𝒱^pre` is Wedhorn's category `(Adic)`, here `TauCeti.AdicSpace`.

This file proves that the adic-space structure passes to open subspaces. The open affinoid
subspaces of a restriction `X|_U` are the open affinoid subspaces of `X` contained in `U`: the
restriction of `X|_U` to an open `V` of `U` is the restriction of `X` to the image of `V`, since
both are open subspaces of `X` with the same image (`restrictRestrictIso`). From this and the fact
that rational subsets are open affinoid subspaces of an affinoid pre-adic space, the open affinoid
subspaces of a locally affinoid object form a basis of its topology (`isBasis_affinoidOpens`), so
the restriction of a locally affinoid object to an open is locally affinoid, and the restriction of
an adic space to an open, or more generally the source of an open immersion into an adic space, is
an adic space: the *open adic subspaces*.

The basis theorem also discharges the basis hypothesis of
`TauCeti.PreAdicSpace.isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`: a pre-adic space in
Wedhorn's sense is sheafy exactly when its structure presheaf is a sheaf on its open affinoid
subspaces (`isPreAdic.isSheafy_iff`), the mechanism of Wedhorn's Remark 8.27.

## Main definitions

* `TauCeti.PreAdicSpace.isAdic`: the adic spaces among the objects of `𝒱^pre`.
* `TauCeti.AdicSpace`: Wedhorn's category `(Adic)`, the full subcategory of `𝒱^pre` of adic
  spaces.
* `TauCeti.PreAdicSpace.restrictRestrictIso`: restricting a restriction is restricting to the
  image.

## Main results

* `TauCeti.PreAdicSpace.mem_affinoidOpens_restrict_iff`: an open of `X|_U` is an open affinoid
  subspace exactly when its image in `X` is.
* `TauCeti.PreAdicSpace.isBasis_affinoidOpens`: the open affinoid subspaces of a locally affinoid
  object form a basis of its topology.
* `TauCeti.PreAdicSpace.isLocallyAffinoid_restrict`, `TauCeti.PreAdicSpace.isSheafy_restrict`,
  `TauCeti.PreAdicSpace.isAdic_restrict`: being locally affinoid, sheafy, or adic passes to
  restrictions to opens, and `TauCeti.PreAdicSpace.isAdic_of_isOpenImmersion`: to the source of
  an open immersion.
* `TauCeti.PreAdicSpace.isPreAdic.isSheafy_iff`: a pre-adic space is sheafy exactly when its
  structure presheaf is a sheaf on its open affinoid subspaces.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace`: `Spa(A, A⁺)` with a sheaf
  structure presheaf is an adic space.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.22, Remark 8.27 and §8.2.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace PreAdicSpace

/-! ### Open affinoid subspaces of a restriction -/

section Restrict

variable {U : TopCat.{u}} (X : PreAdicSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

-- Both bases are the inclusion of a subtype followed by `f`, so a point lies in either range
-- exactly when it is the image of a point of `V`. The identifications of the two bases with
-- `f ∘ Subtype.val` are the `rfl`-lemmas `comp_base` and `ofRestrict_base`, which cannot be
-- rewritten inside `Set.range`: the source of the right-hand side of `ofRestrict_base` is the open
-- `(Opens.toTopCat _).obj V`, while the source of the left-hand side is the carrier of a
-- restriction, which unfolds to it only at default transparency, so the rewritten composite is
-- ill-typed for `rw`. The two sets are compared pointwise instead.
private theorem range_ofRestrict_comp_ofRestrict_base (V : Opens (X.restrict h)) :
    Set.range ((X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h).base =
      Set.range (X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding).base := by
  ext y
  constructor
  · rintro ⟨⟨v, hv⟩, rfl⟩
    exact ⟨⟨f v, v, hv, rfl⟩, rfl⟩
  · rintro ⟨⟨_, v, hv, rfl⟩, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Restricting a restriction is restricting to the image: `X` restricted to `U` and then to an
open `V` of `U` is isomorphic in `𝒱^pre` to `X` restricted to the image of `V` in `X`, both being
open subspaces of `X` with the same image. The isomorphism is compatible with the canonical
morphisms to `X` (`restrictRestrictIso_hom_ofRestrict`). -/
noncomputable def restrictRestrictIso (V : Opens (X.restrict h)) :
    (X.restrict h).restrict V.isOpenEmbedding ≅
      X.restrict (h.isOpenMap.functor.obj V).isOpenEmbedding :=
  IsOpenImmersion.isoOfRangeEq ((X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h)
    (X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding)
    (range_ofRestrict_comp_ofRestrict_base X h V)

@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_ofRestrict (V : Opens (X.restrict h)) :
    (restrictRestrictIso X h V).hom ≫ X.ofRestrict (h.isOpenMap.functor.obj V).isOpenEmbedding =
      (X.restrict h).ofRestrict V.isOpenEmbedding ≫ X.ofRestrict h :=
  IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _

/-- An open `V` of the restriction of `X` along an open embedding is an open affinoid subspace of
the restriction exactly when its image in `X` is an open affinoid subspace of `X`. -/
theorem mem_affinoidOpens_restrict_iff (V : Opens (X.restrict h)) :
    V ∈ (X.restrict h).affinoidOpens ↔ h.isOpenMap.functor.obj V ∈ X.affinoidOpens :=
  ObjectProperty.prop_iff_of_iso isAffinoid (restrictRestrictIso X h V)

end Restrict

/-! ### Open subspaces of locally affinoid and sheafy objects -/

/-- **The open affinoid subspaces of a locally affinoid object form a basis of its topology.**
Every point lies in an open affinoid subspace `U`, which is isomorphic to some `Spa(A, A⁺)`, and
the open affinoid subspaces of `Spa(A, A⁺)` form a basis of its topology; they are carried to open
affinoid subspaces of `X` contained in `U`. -/
theorem isBasis_affinoidOpens {X : PreAdicSpace.{u}} (hX : isLocallyAffinoid X) :
    Opens.IsBasis X.affinoidOpens := by
  refine Opens.isBasis_iff_nbhd.mpr fun {W x} hxW ↦ ?_
  obtain ⟨U, hU, hxU⟩ := hX x
  obtain ⟨A, _, _, _, _, S, P, hP, ⟨e⟩⟩ := (isAffinoid_iff _).mp hU
  -- `x` lies in `W ∩ U`, read as an open of `X|_U`, which is the preimage under `e` of its
  -- preimage under `e⁻¹`; `e` is `forgetToTop.mapIso e` on the underlying spaces
  have hxW₀ : (⟨x, hxU⟩ : X.restrict U.isOpenEmbedding) ∈
      (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W := hxW
  have hW₀ := Opens.map_hom_obj_map_inv_obj (forgetToTop.mapIso e)
    ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W)
  rw [← hW₀] at hxW₀
  -- an open affinoid subspace `V'` of `Spa(A, A⁺)` between `e x` and the image of `W ∩ U`
  obtain ⟨V', hV', hxV', hV'W⟩ := Opens.isBasis_iff_nbhd.mp
    (ValuationSpectrum.isBasis_affinoidOpens_presentationLimitPreAdicSpace P S.plus _ hP)
    (U := (Opens.map e.inv.base).obj ((Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W))
    (x := e.hom.base ⟨x, hxU⟩) hxW₀
  -- the preimage of `V'` under `e` is an open affinoid subspace of `X|_U` contained in `W ∩ U`
  have hV'W' : (Opens.map e.hom.base).obj V' ≤
      (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj W :=
    ((Opens.map e.hom.base).monotone hV'W).trans (le_of_eq hW₀)
  refine ⟨U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map e.hom.base).obj V'), ?_, ?_, ?_⟩
  · exact (mem_affinoidOpens_restrict_iff X U.isOpenEmbedding _).mp
      ((map_hom_base_mem_affinoidOpens_iff e).mpr hV')
  · exact ⟨⟨x, hxU⟩, hxV', rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hV'W' hz

variable {U : TopCat.{u}} {X : PreAdicSpace.{u}} {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

/-- The restriction of a locally affinoid object of `𝒱^pre` to an open is locally affinoid: the
open affinoid subspaces of `X` contained in the image of the open cover it. -/
theorem isLocallyAffinoid_restrict (hX : isLocallyAffinoid X) :
    isLocallyAffinoid (X.restrict h) := by
  intro x
  obtain ⟨V, hV, hxV, hVf⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_affinoidOpens hX)
    (U := h.isOpenMap.functor.obj ⊤) (x := f x) ⟨x, trivial, rfl⟩
  refine ⟨(Opens.map f).obj V, (mem_affinoidOpens_restrict_iff X h _).mpr ?_, hxV⟩
  rw [Opens.functor_obj_map_obj, inf_eq_right.mpr hVf]
  exact hV

/-- The restriction of a sheafy object of `𝒱^pre` to an open is sheafy, since the restriction of a
sheaf to an open subspace is a sheaf. -/
theorem isSheafy_restrict (hX : isSheafy X) : isSheafy (X.restrict h) := by
  unfold isSheafy
  rw [restrict_toPresheafedSpace, PresheafedSpace.restrict_presheaf]
  exact TopCat.Presheaf.isSheaf_of_isOpenEmbedding h hX

/-- The source of an open immersion into a locally affinoid object is locally affinoid. -/
theorem isLocallyAffinoid_of_isOpenImmersion {Y : PreAdicSpace.{u}} (hX : isLocallyAffinoid X)
    (f : Y ⟶ X) [IsOpenImmersion f] : isLocallyAffinoid Y :=
  ObjectProperty.prop_of_iso isLocallyAffinoid (IsOpenImmersion.isoRestrict f).symm
    (isLocallyAffinoid_restrict f.isOpenEmbedding hX)

/-- The source of an open immersion into a sheafy object is sheafy. -/
theorem isSheafy_of_isOpenImmersion {Y : PreAdicSpace.{u}} (hX : isSheafy X) (f : Y ⟶ X)
    [IsOpenImmersion f] : isSheafy Y :=
  ObjectProperty.prop_of_iso isSheafy (IsOpenImmersion.isoRestrict f).symm
    (isSheafy_restrict f.isOpenEmbedding hX)

/-- **A pre-adic space is sheafy exactly when its structure presheaf is a sheaf on its open
affinoid subspaces**, for the topology restricted to them: the open affinoid subspaces form a basis
to which the structure presheaf is adapted. This is the mechanism of Wedhorn's Remark 8.27, which
produces adic spaces from pre-adic spaces covered by sheafy affinoids. -/
theorem isPreAdic.isSheafy_iff (hX : isPreAdic X) :
    isSheafy X ↔ Presheaf.IsSheaf
      ((inducedFunctor (Subtype.val : X.affinoidOpens → Opens X)).restrictedTopology
        (Opens.grothendieckTopology X))
      ((inducedFunctor (Subtype.val : X.affinoidOpens → Opens X)).op ⋙
        X.toPresheafedSpace.presheaf) :=
  TopCat.Presheaf.isSheaf_iff_of_isAdapted _ _ (isBasis_affinoidOpens hX.isLocallyAffinoid)
    hX.isAdapted

/-! ### Adic spaces -/

/-- **Adic spaces** (Wedhorn, Definition 8.22): the objects of `𝒱`, the sheafy objects of
`𝒱^pre`, that admit an open cover by affinoid adic spaces. Since the restriction of a sheafy object
to an open is sheafy (`isSheafy_restrict`), an open cover by affinoid adic spaces is the same as an
open cover by open affinoid subspaces: an adic space is a sheafy locally affinoid object of
`𝒱^pre`. Their full subcategory of `𝒱^pre` is Wedhorn's category `(Adic)`, `TauCeti.AdicSpace`. -/
def isAdic : ObjectProperty PreAdicSpace.{u} :=
  fun X ↦ isSheafy X ∧ isLocallyAffinoid X

theorem isAdic_iff : isAdic X ↔ isSheafy X ∧ isLocallyAffinoid X := Iff.rfl

theorem isAdic.isSheafy (hX : isAdic X) : isSheafy X := hX.1

theorem isAdic.isLocallyAffinoid (hX : isAdic X) : isLocallyAffinoid X := hX.2

theorem isAdic_le_isSheafy : isAdic.{u} ≤ isSheafy := fun _ hX ↦ hX.1

theorem isAdic_le_isLocallyAffinoid : isAdic.{u} ≤ isLocallyAffinoid := fun _ hX ↦ hX.2

/-- Being an adic space is invariant under isomorphism in `𝒱^pre`. -/
instance isAdic.instIsClosedUnderIsomorphisms : isAdic.{u}.IsClosedUnderIsomorphisms where
  of_iso e hX :=
    ⟨ObjectProperty.prop_of_iso PreAdicSpace.isSheafy e hX.1,
      ObjectProperty.prop_of_iso PreAdicSpace.isLocallyAffinoid e hX.2⟩

/-- A sheafy affinoid pre-adic space, an affinoid adic space, is an adic space. -/
theorem isAdic_of_isAffinoid (hX : isAffinoid X) (hs : isSheafy X) : isAdic X :=
  ⟨hs, isLocallyAffinoid_of_isAffinoid hX⟩

/-- **The restriction of an adic space to an open is an adic space**: the open adic subspaces of
an adic space are its open subsets with the restricted structure. -/
theorem isAdic_restrict (hX : isAdic X) : isAdic (X.restrict h) :=
  ⟨isSheafy_restrict h hX.1, isLocallyAffinoid_restrict h hX.2⟩

/-- The source of an open immersion into an adic space is an adic space. -/
theorem isAdic_of_isOpenImmersion {Y : PreAdicSpace.{u}} (hX : isAdic X) (f : Y ⟶ X)
    [IsOpenImmersion f] : isAdic Y :=
  ⟨isSheafy_of_isOpenImmersion hX.1 f, isLocallyAffinoid_of_isOpenImmersion hX.2 f⟩

end PreAdicSpace

/-- Wedhorn's category `(Adic)` of adic spaces: the full subcategory of `𝒱^pre` whose objects are
the sheafy locally affinoid objects (`PreAdicSpace.isAdic`). -/
abbrev AdicSpace : Type (u + 1) :=
  PreAdicSpace.isAdic.{u}.FullSubcategory

/-- Adic spaces are objects of `𝒱`: the full inclusion of `(Adic)` into the category of sheafy
pre-adic spaces. -/
abbrev AdicSpace.toSheafyPreAdicSpace : AdicSpace.{u} ⥤ SheafyPreAdicSpace.{u} :=
  ObjectProperty.ιOfLE PreAdicSpace.isAdic_le_isSheafy

namespace ValuationSpectrum

open Huber

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (Aplus : Subring A) (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
  (hP : P.ringOfDefinition ≤ Aplus)

/-- The presentation-limit pre-adic space of `(A, A⁺)` is sheafy exactly when its
presentation-limit presheaf is a sheaf. -/
theorem isSheafy_presentationLimitPreAdicSpace_iff :
    PreAdicSpace.isSheafy (presentationLimitPreAdicSpace P Aplus hAplus hP) ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) :=
  Iff.rfl

/-- **`Spa(A, A⁺)` with a sheaf structure presheaf is an adic space**, an affinoid adic space: it
is locally affinoid, being a pre-adic space. -/
theorem isAdic_presentationLimitPreAdicSpace
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    PreAdicSpace.isAdic (presentationLimitPreAdicSpace P Aplus hAplus hP) :=
  ⟨hs, (isPreAdic_presentationLimitPreAdicSpace P Aplus hAplus hP).isLocallyAffinoid⟩

end ValuationSpectrum

end TauCeti

end
