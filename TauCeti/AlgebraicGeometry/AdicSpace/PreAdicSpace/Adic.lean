/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.OpenImmersion
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.RationalOpen
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing

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
* `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace` and
  `TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isSheafyRing`: `Spa(A, A⁺)`
  with a sheaf structure presheaf — in particular, the adic spectrum of a sheafy Huber pair — is
  an adic space.
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_completionLocalization`: if the
  structure presheaf of `Spa(A, A⁺)` is a sheaf, so is that of every rational localisation
  `Spa(A⟨T/s⟩, A_U⁺)`.
* `TauCeti.ValuationSpectrum.exists_isSheaf_isOpenImmersion_comap_completionLocalization`: the
  structure map of a rational localisation induces an open immersion onto `R(T/s)` between sheafy
  pre-adic spaces.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 8.22, Definition 8.26, Remark 8.27
  and §8.2.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

universe u

namespace PreAdicSpace

/-! ### Open subspaces of locally affinoid and sheafy objects -/

/-- **The open affinoid subspaces of a locally affinoid object form a basis of its topology.**
Every point lies in an open affinoid subspace `U`, which is isomorphic to some `Spa(A, A⁺)`, and
the open affinoid subspaces of `Spa(A, A⁺)` form a basis of its topology; they are carried to open
affinoid subspaces of `X` contained in `U`. -/
theorem isBasis_affinoidOpens {X : PreAdicSpace.{u}} (hX : isLocallyAffinoid X) :
    Opens.IsBasis X.affinoidOpens :=
  isBasis_propOpens isAffinoid (fun _ hY ↦
    let ⟨_, _, _, _, _, S, P, hP, ⟨e⟩⟩ := (isAffinoid_iff _).mp hY
    isBasis_propOpens_of_iso isAffinoid e
      (ValuationSpectrum.isBasis_affinoidOpens_presentationLimitPreAdicSpace P S.plus _ hP)) hX

variable {U : TopCat.{u}} {X : PreAdicSpace.{u}} {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)

/-- The restriction of a locally affinoid object of `𝒱^pre` to an open is locally affinoid: the
open affinoid subspaces of `X` contained in the image of the open cover it. -/
theorem isLocallyAffinoid_restrict (hX : isLocallyAffinoid X) :
    isLocallyAffinoid (X.restrict h) :=
  exists_mem_propOpens_restrict h isAffinoid (isBasis_affinoidOpens hX)

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
    Set.ext (mem_propOpens_restrict_iff X h isAffinoid)]
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
  exact ⟨_, (mem_propOpens_restrict_iff X (f i).isOpenEmbedding isAffinoid V).mp hV, y, hyV, rfl⟩

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
  obtain ⟨i, hi⟩ := (isCompact_of_mem_affinoidOpens hV).elim_directed_cover
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

section

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

end

open Huber.PairOfDefinition PreAdicSpace in
/-- The structure map of a rational localisation induces an open immersion onto `R(T/s)`: if `T`
spans an open ideal and the structure presheaf of `Spa(A, A⁺)` is a sheaf, then so is that of the
rational localisation `Spa(A⟨T/s⟩, A_U⁺)`, and the morphism `Spa(A⟨T/s⟩, A_U⁺) ⟶ Spa(A, A⁺)`
induced by `(A, A⁺) → (A⟨T/s⟩, A_U⁺)` is an open immersion with image `R(T/s)`. -/
theorem exists_isSheaf_isOpenImmersion_comap_completionLocalization {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    (P : PairOfDefinition A) (U : Pair A) (hP : P.ringOfDefinition ≤ U.plus) (T : Finset A) (s : A)
    (L : Type u) [CommRing L] [Algebra A L] [IsLocalization.Away s L]
    (hden : P.HasDenominatorPower T s L) (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf P U.plus)) :
    letI := P.locUniformSpace T s L hden
    letI := P.isUniformAddGroup_locUniformSpace T s L hden
    letI := P.isTopologicalRing_locUniformSpace T s L hden
    letI := P.isHuberRing_completion_locTopology T s L hden
    ∃ hs : Presheaf.IsSheaf
        (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
        (presentationLimitPresheaf (P.completionLocalization T s L hden)
          (P.rationalLocalizationPair U hP T s L hden).plus),
      ∃ v, v = presentationLimitPreAdicSpaceComap
        (P' := P.completionLocalization T s L hden) (P.toCompletionLocHom U hP T s L hden).toRingHom
        (P.toCompletionLocHom U hP T s L hden).continuous_toRingHom
        (P.toCompletionLocHom U hP T s L hden).map_mem_plus
        U.isRingOfIntegralElements.isPowerBounded_of_mem
        (P.rationalLocalizationPair U hP T s L hden).isRingOfIntegralElements.isPowerBounded_of_mem
        hP (P.completionLocalization_ringOfDefinition_le_rationalLocalizationPair U hP T s L hden)
        hs ∧ IsOpenImmersion v ∧
          Set.range v.base = (spaBasicOpen U.plus T s : Set (spa U.plus)) := by
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  have hs : Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
      (presentationLimitPresheaf (P.completionLocalization T s L hden)
        (P.rationalLocalizationPair U hP T s L hden).plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hP T s L hden hT hsheaf
  exact ⟨hs, _, rfl,
    isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT hs,
    range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s L hden hs⟩

/-- **The adic spectrum of a sheafy Huber pair is an affinoid adic space.** The ring need not be
complete, Hausdorff, or Tate. -/
theorem isAdic_presentationLimitPreAdicSpace_of_isSheafyRing {A : Type u} [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [IsHuberRing A]
    (P : PairOfDefinition A) {Aplus : Subring A} (hAplus : IsRingOfIntegralElements Aplus)
    (hP : P.ringOfDefinition ≤ Aplus) (hA : IsSheafyRing A) :
    PreAdicSpace.isAdic
      (presentationLimitPreAdicSpace P Aplus hAplus.isPowerBounded_of_mem hP) :=
  isAdic_presentationLimitPreAdicSpace P Aplus hAplus.isPowerBounded_of_mem hP
    (isSheaf_presentationLimitPresheaf_of_isSheafyRing P hAplus hP hA)

end ValuationSpectrum

end TauCeti

end
