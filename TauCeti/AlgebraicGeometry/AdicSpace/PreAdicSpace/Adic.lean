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

## Main results

* `TauCeti.PreAdicSpace.mem_affinoidOpens_restrict_iff`: an open of `X|_U` is an open affinoid
  subspace exactly when its image in `X` is.
* `TauCeti.PreAdicSpace.isBasis_affinoidOpens`: the open affinoid subspaces of a locally affinoid
  object form a basis of its topology.
* `TauCeti.PreAdicSpace.isLocallyAffinoid_restrict`, `TauCeti.PreAdicSpace.isSheafy_restrict`,
  `TauCeti.PreAdicSpace.isAdic_restrict`: being locally affinoid, sheafy, or adic passes to
  restrictions to opens, and `TauCeti.PreAdicSpace.isAdic_of_isOpenImmersion`: to the source of
  an open immersion.
* `TauCeti.PreAdicSpace.isSheafy_restrict_of_range_subset`: if the restriction of `X` to an open
  is sheafy, so is its restriction to every smaller open.

* `TauCeti.PreAdicSpace.isPreAdic_restrict`: the restriction of a pre-adic space to an open is
  pre-adic.
* `TauCeti.PreAdicSpace.isLocallyAffinoid_of_jointly_surjective`: an object covered by open
  immersions from locally affinoid objects is locally affinoid.
* `TauCeti.PreAdicSpace.isPreAdic.isSheafy_iff`: a pre-adic space is sheafy exactly when its
  structure presheaf is a sheaf on its open affinoid subspaces.
* `TauCeti.PreAdicSpace.isPreAdic.isSheafy_of_forall_exists_le`,
  `TauCeti.PreAdicSpace.isPreAdic.isSheafy_of_directed`: a pre-adic space is sheafy if each open
  affinoid subspace lies in a sheafy open, for instance if it is exhausted by a directed family of
  sheafy opens.
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace`: `Spa(A, A⁺)` with a sheaf
  structure presheaf is an adic space.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_completionLocalization`: if the
  structure presheaf of `Spa(A, A⁺)` is a sheaf, so is that of every rational localisation
  `Spa(A⟨T/s⟩, A_U⁺)`.

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

/-- If the restriction of `X` along an open embedding `g` is sheafy, then so is its restriction
along every open embedding `f` whose image lies in the image of `g`: `X|_f` is the restriction of
`X|_g` to the preimage of the image of `f`. -/
theorem isSheafy_restrict_of_range_subset {V : TopCat.{u}} {g : V ⟶ X.toTopCat}
    (hg : IsOpenEmbedding g) (hfg : Set.range f ⊆ Set.range g) (hX : isSheafy (X.restrict hg)) :
    isSheafy (X.restrict h) := by
  let W : Opens (X.restrict hg) := ⟨g ⁻¹' Set.range f, h.isOpenMap.isOpen_range.preimage g.hom.2⟩
  -- the image of `W` in `X` is the image of `f`; the open `W` of the restriction is an open of
  -- `V` only up to unfolding, so the image is compared pointwise rather than rewritten
  have hW : Set.range (Opens.inclusion' (hg.isOpenMap.functor.obj W)) = Set.range f := by
    rw [Opens.set_range_inclusion']
    ext y
    refine ⟨fun ⟨_, hv, hy⟩ ↦ hy ▸ hv, fun hy ↦ ?_⟩
    obtain ⟨v, rfl⟩ := hfg hy
    exact ⟨v, hy, rfl⟩
  exact ObjectProperty.prop_of_iso isSheafy
    (restrictRestrictIso X hg W ≪≫ X.restrictIsoOfRangeEq _ h hW)
    (isSheafy_restrict W.isOpenEmbedding hX)

/-- **The restriction of a pre-adic space to an open is pre-adic.** It is locally affinoid, and its
open affinoid subspaces are the opens whose images are open affinoid subspaces of `X`, to which
the restricted structure presheaf is adapted (`TopCat.Presheaf.IsAdapted.restrict`). -/
theorem isPreAdic_restrict (hX : isPreAdic X) : isPreAdic (X.restrict h) := by
  refine ⟨isLocallyAffinoid_restrict h hX.isLocallyAffinoid, ?_⟩
  rw [show (X.restrict h).affinoidOpens = h.functor.obj ⁻¹' X.affinoidOpens from
    Set.ext (mem_affinoidOpens_restrict_iff X h)]
  -- the structure presheaf of `X.restrict h` is `h.functor.op ⋙ X.presheaf` by definition
  -- (`PresheafedSpace.restrict_presheaf`); rewriting with it is blocked by the dependence of the
  -- family of opens on the carrier
  exact hX.isAdapted.restrict h

/-- The source of an open immersion into a locally affinoid object is locally affinoid. -/
theorem isLocallyAffinoid_of_isOpenImmersion {Y : PreAdicSpace.{u}} (hX : isLocallyAffinoid X)
    (f : Y ⟶ X) [IsOpenImmersion f] : isLocallyAffinoid Y :=
  ObjectProperty.prop_of_iso isLocallyAffinoid (IsOpenImmersion.isoRestrict f).symm
    (isLocallyAffinoid_restrict f.isOpenEmbedding hX)

/-- **An object of `𝒱^pre` covered by open immersions from locally affinoid objects is locally
affinoid.** A point `x = f i y` has an open affinoid neighbourhood in `U i`, which `f i` identifies
with an open affinoid subspace of `X` containing `x`. -/
theorem isLocallyAffinoid_of_jointly_surjective {ι : Type*} {U : ι → PreAdicSpace.{u}}
    (f : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hU : ∀ i, isLocallyAffinoid (U i))
    (hf : ∀ x : X, ∃ (i : ι) (y : U i), (f i).base y = x) : isLocallyAffinoid X := by
  intro x
  obtain ⟨i, y, rfl⟩ := hf x
  obtain ⟨V, hV, hyV⟩ := ObjectProperty.prop_of_iso isLocallyAffinoid
    (IsOpenImmersion.isoRestrict (f i)) (hU i) y
  exact ⟨_, (mem_affinoidOpens_restrict_iff X (f i).isOpenEmbedding V).mp hV, y, hyV, rfl⟩

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

/-- **A pre-adic space is sheafy if each open affinoid subspace lies in a sheafy open.** If every
open affinoid subspace `V` of the pre-adic space `X` is contained in an open `U` with `X|_U`
sheafy, then `X` is sheafy. The structure presheaf is determined by its values on the open affinoid
subspaces, and the sheaf condition for a cover of `V` by open affinoid subspaces holds inside the
sheafy open `U`. -/
theorem isPreAdic.isSheafy_of_forall_exists_le (hX : isPreAdic X)
    (h : ∀ V ∈ X.affinoidOpens, ∃ U : Opens X, V ≤ U ∧ isSheafy (X.restrict U.isOpenEmbedding)) :
    isSheafy X :=
  -- `X|_U` is sheafy when `U.isOpenEmbedding.functor.op ⋙ X.presheaf` is a sheaf, by definition of
  -- the presheaf of a restriction (`PresheafedSpace.restrict_presheaf`)
  TopCat.Presheaf.isSheaf_of_isAdapted_of_forall_exists_le _ _
    (isBasis_affinoidOpens hX.isLocallyAffinoid) hX.isAdapted h

/-- **A pre-adic space exhausted by sheafy opens is sheafy.** If a directed family of opens `U i`
covers the pre-adic space `X` and every `X|_{U i}` is sheafy, then `X` is sheafy: an open affinoid
subspace is quasi-compact, so it lies in a single `U i`. -/
theorem isPreAdic.isSheafy_of_directed {ι : Type*} [Nonempty ι] (hX : isPreAdic X)
    {U : ι → Opens X} (hU : Directed (· ≤ ·) U) (hcov : iSup U = ⊤)
    (h : ∀ i, isSheafy (X.restrict (U i).isOpenEmbedding)) : isSheafy X := by
  refine hX.isSheafy_of_forall_exists_le fun V hV ↦ ?_
  have := (spectralSpace_of_isAffinoid hV).toCompactSpace
  obtain ⟨i, hi⟩ := (isCompact_iff_compactSpace.mpr this).elim_directed_cover
    (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen)
    (by rw [← Opens.coe_iSup, hcov]; exact Set.subset_univ _)
    fun i j ↦ hU i j
  exact ⟨U i, hi, h i⟩

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

include hAplus hP in
/-- **Rational localisation preserves the sheaf condition**: if the structure presheaf of
`Spa(A, A⁺)` is a sheaf and `T` spans an open ideal, then the structure presheaf of
`Spa(A⟨T/s⟩, A_U⁺)` is a sheaf. By Wedhorn's Remark 8.8
(`presentationLimitPreAdicSpaceLocIso`), `Spa(A⟨T/s⟩, A_U⁺)` is isomorphic in `𝒱^pre` to the
restriction of `Spa(A, A⁺)` to `R(T/s)`, and the restriction of a sheaf to an open is a sheaf. -/
theorem isSheaf_presentationLimitPresheaf_completionLocalization (T : Finset A) (s : A)
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away s S]
    (hden : P.HasDenominatorPower T s S) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hs : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
      (presentationLimitPresheaf P Aplus)) :
    letI := P.locUniformSpace T s S hden
    letI := P.isUniformAddGroup_locUniformSpace T s S hden
    letI := P.isTopologicalRing_locUniformSpace T s S hden
    Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa (P.completedPlusSubring Aplus T s S hden)))
      (presentationLimitPresheaf (P.completionLocalization T s S hden)
        (P.completedPlusSubring Aplus T s S hden)) :=
  letI := P.locUniformSpace T s S hden
  letI := P.isUniformAddGroup_locUniformSpace T s S hden
  letI := P.isTopologicalRing_locUniformSpace T s S hden
  ObjectProperty.prop_of_iso PreAdicSpace.isSheafy
    (presentationLimitPreAdicSpaceLocIso P Aplus T s S hden hAplus hP hT)
    (PreAdicSpace.isSheafy_restrict _ hs)

end ValuationSpectrum

end TauCeti

end
