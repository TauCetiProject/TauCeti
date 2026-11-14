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

In `(Adic)` the open adic subspace `X.restrict U` comes with its inclusion `X.ofRestrict U`, and a
morphism `f : X ⟶ Y` restricts to `restrictPreimage f V : f⁻¹(V) ⟶ V` over each open `V ⊆ Y`.
Pullbacks along open immersions exist in `(Adic)`, being computed in `𝒱^pre`, and the open adic
subspace `f⁻¹(V)` is the fibre product `X ×_Y V` with no hypothesis on `f`
(`isPullback_restrictPreimage`).

The basis theorem also discharges the basis hypothesis of
`TauCeti.PreAdicSpace.isSheafy_of_isAdapted_of_isSheaf_affinoidOpens`: a pre-adic space in
Wedhorn's sense is sheafy exactly when its structure presheaf is a sheaf on its open affinoid
subspaces (`isPreAdic.isSheafy_iff`), the mechanism of Wedhorn's Remark 8.27.

## Main definitions

* `TauCeti.PreAdicSpace.isAdic`: the adic spaces among the objects of `𝒱^pre`.
* `TauCeti.AdicSpace`: Wedhorn's category `(Adic)`, the full subcategory of `𝒱^pre` of adic
  spaces.
* `TauCeti.AdicSpace.liftOfIsOpenImmersion`: the factorisation of a morphism of adic spaces
  through an open immersion whose image contains the image of the morphism.
* `TauCeti.AdicSpace.restrict`, `TauCeti.AdicSpace.ofRestrict`: the open adic subspace of an adic
  space on an open subset, and its inclusion, with the factorisation
  `TauCeti.AdicSpace.liftRestrict`.
* `TauCeti.AdicSpace.restrictPreimage`: the restriction `f⁻¹(V) ⟶ V` of a morphism of adic spaces
  over an open of its target.

## Main results

* `TauCeti.PreAdicSpace.isBasis_affinoidOpens`: the open affinoid subspaces of a locally affinoid
  object form a basis of its topology.
* `TauCeti.PreAdicSpace.isLocallyAffinoid_restrict`, `TauCeti.PreAdicSpace.isSheafy_restrict`,
  `TauCeti.PreAdicSpace.isAdic_restrict`: being locally affinoid, sheafy, or adic passes to
  restrictions to opens, and `TauCeti.PreAdicSpace.isAdic_of_isOpenImmersion`: to the source of
  an open immersion.
* `TauCeti.PreAdicSpace.isSheafy_restrict_of_range_subset`: if the restriction of `X` to an open
  is sheafy, so is its restriction to every smaller open.
* `TauCeti.AdicSpace.isPullback_of_isOpenImmersion`: a commutative square of adic spaces with an
  open immersion opposite a monomorphism is a pullback once the preimage of the image of the
  monomorphism lies in the image of the open immersion;
  `TauCeti.AdicSpace.hasPullback_of_isOpenImmersion_left`: pullbacks of open immersions exist in
  `(Adic)` and are computed in `𝒱^pre`
  (`TauCeti.AdicSpace.preservesLimit_cospan_of_isOpenImmersion_left`), and their base changes are
  open immersions.
* `TauCeti.AdicSpace.isPullback_restrictPreimage`: for any morphism `f : X ⟶ Y` of adic spaces and
  open `V ⊆ Y`, the open adic subspace `f⁻¹(V)` is the fibre product `X ×_Y V`.

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
* `TauCeti.ValuationSpectrum.isSheaf_presentationLimitPresheaf_rationalLocalizationPair`: the same,
  for the rational localisation as a pair.

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

namespace AdicSpace

open Limits

/-- Open immersions of adic spaces are stable under composition. -/
instance isOpenImmersion_comp {X Y Z : AdicSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [PreAdicSpace.IsOpenImmersion f.hom] [PreAdicSpace.IsOpenImmersion g.hom] :
    PreAdicSpace.IsOpenImmersion (f ≫ g).hom := by
  rw [ObjectProperty.FullSubcategory.comp_hom]
  infer_instance

/-- A morphism of adic spaces whose underlying morphism of pre-adic spaces is an open immersion is
a monomorphism of adic spaces. -/
instance mono_of_isOpenImmersion {X Y : AdicSpace.{u}} (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : Mono f :=
  (ObjectProperty.ι _).mono_of_mono_map (inferInstanceAs (Mono f.hom))

section Lift

variable {X Y Z : AdicSpace.{u}} (f : X ⟶ Z) [PreAdicSpace.IsOpenImmersion f.hom] (g : Y ⟶ Z)

/-- For a morphism `f : X ⟶ Z` of adic spaces whose underlying morphism is an open immersion and a
morphism `g : Y ⟶ Z` whose image lies in the image of `f`, the morphism `Y ⟶ X` through which `g`
factors. -/
noncomputable def liftOfIsOpenImmersion (H : Set.range g.hom.base ⊆ Set.range f.hom.base) :
    Y ⟶ X :=
  ObjectProperty.homMk (PreAdicSpace.IsOpenImmersion.lift f.hom g.hom H)

/-- The underlying morphism of pre-adic spaces of the factorization through an open immersion. -/
@[simp]
theorem liftOfIsOpenImmersion_hom (H : Set.range g.hom.base ⊆ Set.range f.hom.base) :
    (liftOfIsOpenImmersion f g H).hom = PreAdicSpace.IsOpenImmersion.lift f.hom g.hom H :=
  (rfl)

/-- Composing the factorization with the open immersion recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem liftOfIsOpenImmersion_fac (H : Set.range g.hom.base ⊆ Set.range f.hom.base) :
    liftOfIsOpenImmersion f g H ≫ f = g := by
  ext1
  exact PreAdicSpace.IsOpenImmersion.lift_fac _ _ _

/-- The factorization through an open immersion is unique. -/
theorem liftOfIsOpenImmersion_uniq (H : Set.range g.hom.base ⊆ Set.range f.hom.base) (l : Y ⟶ X)
    (hl : l ≫ f = g) : l = liftOfIsOpenImmersion f g H := by
  rw [← cancel_mono f, hl, liftOfIsOpenImmersion_fac]

/-- The factorization of an open immersion through another open immersion is an open
immersion. -/
instance isOpenImmersion_liftOfIsOpenImmersion [PreAdicSpace.IsOpenImmersion g.hom]
    (H : Set.range g.hom.base ⊆ Set.range f.hom.base) :
    PreAdicSpace.IsOpenImmersion (liftOfIsOpenImmersion f g H).hom := by
  rw [liftOfIsOpenImmersion_hom]
  infer_instance

/-- A morphism factors through an open immersion exactly when its image lies in the image of the
open immersion. -/
theorem exists_comp_eq_iff_of_isOpenImmersion :
    (∃ l : Y ⟶ X, l ≫ f = g) ↔ Set.range g.hom.base ⊆ Set.range f.hom.base := by
  refine ⟨?_, fun H ↦ ⟨liftOfIsOpenImmersion f g H, liftOfIsOpenImmersion_fac f g H⟩⟩
  rintro ⟨l, rfl⟩
  rw [ObjectProperty.FullSubcategory.comp_hom, PreAdicSpace.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

end Lift

/-- **Pullback criterion along an open immersion of adic spaces.** A commutative square of adic
spaces whose left side `iU` is an open immersion and whose right side `iV` is a monomorphism is a
pullback square as soon as every point of `X` mapped by `g` into the image of `iV` lies in the
image of `iU`. -/
theorem isPullback_of_isOpenImmersion {U V X Y : AdicSpace.{u}} (f : U ⟶ V) (iU : U ⟶ X)
    (iV : V ⟶ Y) (g : X ⟶ Y) [PreAdicSpace.IsOpenImmersion iU.hom] [Mono iV]
    (w : f ≫ iV = iU ≫ g)
    (hrange : g.hom.base ⁻¹' Set.range iV.hom.base ⊆ Set.range iU.hom.base) :
    IsPullback f iU iV g := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w) ?_
  refine PullbackCone.isLimitAux' _ fun s ↦ ?_
  have hs : Set.range s.snd.hom.base ⊆ Set.range iU.hom.base := by
    rintro _ ⟨t, rfl⟩
    exact hrange ⟨s.fst.hom.base t, congrArg (fun φ : s.pt ⟶ Y ↦ φ.hom.base t) s.condition⟩
  refine ⟨liftOfIsOpenImmersion iU s.snd hs, ?_, liftOfIsOpenImmersion_fac _ _ _,
    fun {m} _ hm ↦ liftOfIsOpenImmersion_uniq _ _ _ m hm⟩
  rw [← cancel_mono iV, PullbackCone.mk_fst, Category.assoc, w,
    liftOfIsOpenImmersion_fac_assoc, s.condition]

section HasPullback

variable {U X Y : AdicSpace.{u}} (i : U ⟶ Y) [PreAdicSpace.IsOpenImmersion i.hom] (f : X ⟶ Y)

/-- The pullback of pre-adic spaces of an open immersion of adic spaces is a pullback square of
adic spaces. -/
private theorem exists_isPullback_of_isOpenImmersion :
    ∃ (P : AdicSpace.{u}) (fst : P ⟶ U) (snd : P ⟶ X),
      IsPullback fst snd i f ∧ IsPullback fst.hom snd.hom i.hom f.hom :=
  ⟨⟨pullback i.hom f.hom,
      PreAdicSpace.isAdic_of_isOpenImmersion X.property (pullback.snd i.hom f.hom)⟩,
    ObjectProperty.homMk (pullback.fst i.hom f.hom),
    ObjectProperty.homMk (pullback.snd i.hom f.hom),
    IsPullback.of_map_of_faithful PreAdicSpace.isAdic.ι (IsPullback.of_hasPullback i.hom f.hom),
    IsPullback.of_hasPullback i.hom f.hom⟩

/-- Adic spaces have pullbacks of open immersions. -/
instance hasPullback_of_isOpenImmersion_left : HasPullback i f :=
  let ⟨_, _, _, h, _⟩ := exists_isPullback_of_isOpenImmersion i f
  h.hasPullback

/-- Adic spaces have pullbacks of open immersions. -/
instance hasPullback_of_isOpenImmersion_right : HasPullback f i :=
  hasPullback_symmetry i f

/-- Pullbacks of open immersions of adic spaces are computed in `𝒱^pre`. -/
instance preservesLimit_cospan_of_isOpenImmersion_left :
    PreservesLimit (cospan i f) PreAdicSpace.isAdic.ι :=
  let ⟨_, _, _, h, h'⟩ := exists_isPullback_of_isOpenImmersion i f
  h.preservesLimit_cospan_iff.mpr h'

/-- Pullbacks of open immersions of adic spaces are computed in `𝒱^pre`. -/
instance preservesLimit_cospan_of_isOpenImmersion_right :
    PreservesLimit (cospan f i) PreAdicSpace.isAdic.ι :=
  preservesPullback_symmetry _ _ _

/-- The pullback square of adic spaces of an open immersion is a pullback square of pre-adic
spaces. -/
theorem isPullback_pullback_hom_of_isOpenImmersion_left :
    IsPullback (pullback.fst i f).hom (pullback.snd i f).hom i.hom f.hom :=
  (IsPullback.of_hasPullback i f).map PreAdicSpace.isAdic.ι

/-- The pullback square of adic spaces of an open immersion is a pullback square of pre-adic
spaces. -/
theorem isPullback_pullback_hom_of_isOpenImmersion_right :
    IsPullback (pullback.fst f i).hom (pullback.snd f i).hom f.hom i.hom :=
  (IsPullback.of_hasPullback f i).map PreAdicSpace.isAdic.ι

/-- Open immersions of adic spaces are stable under base change. -/
instance isOpenImmersion_pullback_snd_of_left :
    PreAdicSpace.IsOpenImmersion (pullback.snd i f).hom := by
  rw [← (isPullback_pullback_hom_of_isOpenImmersion_left i f).isoPullback_hom_snd]
  infer_instance

/-- Open immersions of adic spaces are stable under base change. -/
instance isOpenImmersion_pullback_fst_of_right :
    PreAdicSpace.IsOpenImmersion (pullback.fst f i).hom := by
  rw [← pullbackSymmetry_hom_comp_snd, ObjectProperty.FullSubcategory.comp_hom]
  infer_instance

/-- The image of the base change of an open immersion `i` along `f` is the preimage under `f` of
the image of `i`. -/
theorem range_pullback_snd_of_isOpenImmersion_left :
    Set.range (pullback.snd i f).hom.base = f.hom.base ⁻¹' Set.range i.hom.base := by
  rw [← (isPullback_pullback_hom_of_isOpenImmersion_left i f).isoPullback_hom_snd,
    PreAdicSpace.comp_base, TopCat.coe_comp, Function.Surjective.range_comp ?_,
    PreAdicSpace.IsOpenImmersion.range_pullback_snd_of_left]
  exact (TopCat.homeoOfIso (PreAdicSpace.forgetToTop.mapIso _)).surjective

/-- The image of the base change of an open immersion `i` along `f` is the preimage under `f` of
the image of `i`. -/
theorem range_pullback_fst_of_isOpenImmersion_right :
    Set.range (pullback.fst f i).hom.base = f.hom.base ⁻¹' Set.range i.hom.base := by
  rw [← pullbackSymmetry_hom_comp_snd, ObjectProperty.FullSubcategory.comp_hom,
    PreAdicSpace.comp_base, TopCat.coe_comp, Function.Surjective.range_comp ?_,
    range_pullback_snd_of_isOpenImmersion_left]
  exact (TopCat.homeoOfIso (PreAdicSpace.forgetToTop.mapIso
    (PreAdicSpace.isAdic.ι.mapIso (pullbackSymmetry f i)))).surjective

end HasPullback

section Restrict

variable (X : AdicSpace.{u}) (U : Opens X.obj)

/-- The open adic subspace of an adic space `X` on an open subset `U`: the restriction of `X` to
`U`, which is again an adic space. -/
@[expose] noncomputable def restrict : AdicSpace.{u} :=
  ⟨X.obj.restrict U.isOpenEmbedding, PreAdicSpace.isAdic_restrict _ X.property⟩

/-- The pre-adic space underlying an open adic subspace is the restriction of the underlying
pre-adic space. -/
@[simp]
theorem restrict_obj : (X.restrict U).obj = X.obj.restrict U.isOpenEmbedding :=
  (rfl)

/-- The inclusion of an open adic subspace. -/
noncomputable def ofRestrict : X.restrict U ⟶ X :=
  ObjectProperty.homMk (X.obj.ofRestrict U.isOpenEmbedding)

/-- The underlying morphism of pre-adic spaces of the inclusion of an open adic subspace. -/
@[simp]
theorem ofRestrict_hom : (X.ofRestrict U).hom = X.obj.ofRestrict U.isOpenEmbedding :=
  (rfl)

instance : PreAdicSpace.IsOpenImmersion (X.ofRestrict U).hom :=
  PreAdicSpace.IsOpenImmersion.ofRestrict X.obj U.isOpenEmbedding

/-- On points, the inclusion of an open adic subspace is the inclusion of the open subset. -/
-- Not a simp lemma: `ofRestrict_hom` already simplifies the underlying morphism.
theorem ofRestrict_base_apply (x : X.obj.restrict U.isOpenEmbedding) :
    (X.ofRestrict U).hom.base x = x.1 := by
  rw [ofRestrict_hom, PreAdicSpace.ofRestrict_base]
  rfl

/-- The image of the inclusion of an open adic subspace is the open subset. -/
-- Not a simp lemma: `ofRestrict_hom` already simplifies the underlying morphism.
theorem range_ofRestrict : Set.range (X.ofRestrict U).hom.base = U := by
  rw [ofRestrict_hom, PreAdicSpace.ofRestrict_base]
  exact Opens.set_range_inclusion' U

/-- The open adic subspace on the whole space is the space itself. -/
noncomputable def restrictTopIso : X.restrict ⊤ ≅ X :=
  ObjectProperty.isoMk _ X.obj.restrictTopIso

/-- The isomorphism `restrictTopIso` is the inclusion of the open adic subspace. -/
@[simp]
theorem restrictTopIso_hom : X.restrictTopIso.hom = X.ofRestrict ⊤ := by
  ext1
  exact X.obj.restrictTopIso_hom

/-- The inverse of `restrictTopIso` followed by the inclusion of the open adic subspace on `⊤` is
the identity of `X`. -/
@[reassoc (attr := simp)]
theorem restrictTopIso_inv_ofRestrict : X.restrictTopIso.inv ≫ X.ofRestrict ⊤ = 𝟙 X := by
  rw [← restrictTopIso_hom, Iso.inv_hom_id]

/-- The inclusion of the open adic subspace on `⊤` followed by the inverse of `restrictTopIso` is
the identity of `X.restrict ⊤`. -/
@[reassoc (attr := simp)]
theorem ofRestrict_restrictTopIso_inv : X.ofRestrict ⊤ ≫ X.restrictTopIso.inv = 𝟙 _ := by
  rw [← restrictTopIso_hom, Iso.hom_inv_id]

instance : IsIso (X.ofRestrict ⊤) := by
  rw [← restrictTopIso_hom]
  infer_instance

/-- Restricting an open adic subspace `X|_U` to an open `V` of `U` is restricting `X` to the image
of `V` in `X`. -/
noncomputable def restrictRestrictIso (V : Opens (X.restrict U).obj) :
    (X.restrict U).restrict V ≅ X.restrict (U.isOpenEmbedding.isOpenMap.functor.obj V) :=
  ObjectProperty.isoMk _ (X.obj.restrictRestrictIso U.isOpenEmbedding V)

/-- The underlying isomorphism of pre-adic spaces of `restrictRestrictIso`. -/
@[simp]
theorem restrictRestrictIso_hom_hom (V : Opens (X.restrict U).obj) :
    (X.restrictRestrictIso U V).hom.hom = (X.obj.restrictRestrictIso U.isOpenEmbedding V).hom :=
  (rfl)

/-- The underlying isomorphism of pre-adic spaces of `restrictRestrictIso`. -/
@[simp]
theorem restrictRestrictIso_inv_hom (V : Opens (X.restrict U).obj) :
    (X.restrictRestrictIso U V).inv.hom = (X.obj.restrictRestrictIso U.isOpenEmbedding V).inv :=
  (rfl)

/-- The nested-restriction isomorphism commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_hom_ofRestrict (V : Opens (X.restrict U).obj) :
    (X.restrictRestrictIso U V).hom ≫ X.ofRestrict _ =
      (X.restrict U).ofRestrict V ≫ X.ofRestrict U := by
  ext1
  exact X.obj.restrictRestrictIso_hom_ofRestrict U.isOpenEmbedding V

/-- The inverse nested-restriction isomorphism commutes with the inclusions into `X`. -/
@[reassoc (attr := simp)]
theorem restrictRestrictIso_inv_ofRestrict (V : Opens (X.restrict U).obj) :
    (X.restrictRestrictIso U V).inv ≫ (X.restrict U).ofRestrict V ≫ X.ofRestrict U =
      X.ofRestrict _ := by
  rw [Iso.inv_comp_eq, restrictRestrictIso_hom_ofRestrict]

variable {X} {T : AdicSpace.{u}}

/-- A morphism of adic spaces whose image lies in `U` factors through the open adic subspace on
`U`. -/
noncomputable def liftRestrict (g : T ⟶ X) (hg : Set.range g.hom.base ⊆ U) : T ⟶ X.restrict U :=
  liftOfIsOpenImmersion (X.ofRestrict U) g (by rwa [range_ofRestrict])

/-- The underlying morphism of pre-adic spaces of the factorization through an open adic
subspace. -/
@[simp]
theorem liftRestrict_hom (g : T ⟶ X) (hg : Set.range g.hom.base ⊆ U) :
    (liftRestrict U g hg).hom =
      PreAdicSpace.IsOpenImmersion.lift (X.ofRestrict U).hom g.hom (by rwa [range_ofRestrict]) :=
  (rfl)

/-- The factorization of an open immersion through an open adic subspace is an open
immersion. -/
instance (g : T ⟶ X) [PreAdicSpace.IsOpenImmersion g.hom] (hg : Set.range g.hom.base ⊆ U) :
    PreAdicSpace.IsOpenImmersion (liftRestrict U g hg).hom := by
  rw [liftRestrict_hom]
  infer_instance

/-- Composing the factorization with the inclusion recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem liftRestrict_ofRestrict (g : T ⟶ X) (hg : Set.range g.hom.base ⊆ U) :
    liftRestrict U g hg ≫ X.ofRestrict U = g :=
  liftOfIsOpenImmersion_fac _ _ _

/-- The factorization through an open adic subspace is unique. -/
theorem liftRestrict_uniq (g : T ⟶ X) (hg : Set.range g.hom.base ⊆ U) (l : T ⟶ X.restrict U)
    (hl : l ≫ X.ofRestrict U = g) : l = liftRestrict U g hg :=
  liftOfIsOpenImmersion_uniq _ _ _ l hl

/-- On points, the factorization through an open adic subspace is the original map with codomain
restricted to `U`. -/
-- Not a simp lemma: `liftRestrict_hom` already simplifies the underlying morphism.
theorem liftRestrict_base_apply (g : T ⟶ X) (hg : Set.range g.hom.base ⊆ U) (x : T.obj) :
    (liftRestrict U g hg).hom.base x = ⟨g.hom.base x, hg (Set.mem_range_self x)⟩ := by
  rw [liftRestrict_hom]
  apply Subtype.ext
  exact congrArg (fun φ ↦ φ.base x)
    (PreAdicSpace.IsOpenImmersion.lift_fac (X.ofRestrict U).hom g.hom _)

/-- A morphism factors through the open adic subspace on `U` exactly when its image lies in
`U`. -/
theorem exists_comp_ofRestrict_eq_iff (g : T ⟶ X) :
    (∃ l : T ⟶ X.restrict U, l ≫ X.ofRestrict U = g) ↔ Set.range g.hom.base ⊆ U := by
  rw [exists_comp_eq_iff_of_isOpenImmersion, range_ofRestrict]

end Restrict

section RestrictPreimage

variable {X Y Z : AdicSpace.{u}} (f : X ⟶ Y) (V : Opens Y.obj)

/-- The restriction `f⁻¹(V) ⟶ V` of a morphism of adic spaces over an open of its target. -/
noncomputable def restrictPreimage :
    X.restrict ((Opens.map f.hom.base).obj V) ⟶ Y.restrict V :=
  ObjectProperty.homMk (f.hom.restrictPreimage V)

/-- The underlying morphism of pre-adic spaces of the restriction. -/
@[simp]
theorem restrictPreimage_hom : (restrictPreimage f V).hom = f.hom.restrictPreimage V :=
  (rfl)

/-- The restriction of a morphism commutes with the inclusions of the open subspaces. -/
@[reassoc (attr := simp)]
theorem restrictPreimage_ofRestrict :
    restrictPreimage f V ≫ Y.ofRestrict V = X.ofRestrict ((Opens.map f.hom.base).obj V) ≫ f := by
  ext1
  simp only [ObjectProperty.FullSubcategory.comp_hom, restrictPreimage_hom, ofRestrict_hom]
  exact f.hom.restrictPreimage_ofRestrict V

/-- Any morphism between the open adic subspaces that commutes with their inclusions is the
restriction of the original morphism. -/
theorem restrictPreimage_uniq (g : X.restrict ((Opens.map f.hom.base).obj V) ⟶ Y.restrict V)
    (hg : g ≫ Y.ofRestrict V = X.ofRestrict ((Opens.map f.hom.base).obj V) ≫ f) :
    g = restrictPreimage f V := by
  rw [← cancel_mono (Y.ofRestrict V), hg, restrictPreimage_ofRestrict]

/-- On points, the restriction is the original map with codomain restricted to `V`. -/
-- Not a simp lemma: `restrictPreimage_hom` already simplifies the underlying morphism.
theorem restrictPreimage_base_apply
    (x : X.obj.restrict ((Opens.map f.hom.base).obj V).isOpenEmbedding) :
    (restrictPreimage f V).hom.base x = ⟨f.hom.base x.1, Opens.mem_map.mp x.2⟩ := by
  rw [restrictPreimage_hom]
  exact f.hom.restrictPreimage_base_apply V x

/-- Restricting the identity over an open gives the identity. -/
@[simp]
theorem restrictPreimage_id (U : Opens X.obj) : restrictPreimage (𝟙 X) U = 𝟙 _ :=
  (restrictPreimage_uniq _ _ _ ((Category.id_comp _).trans (Category.comp_id _).symm)).symm

/-- Restricting a composite over an open is composing the restrictions. -/
theorem restrictPreimage_comp (g : Y ⟶ Z) (W : Opens Z.obj) :
    restrictPreimage (f ≫ g) W =
      restrictPreimage f ((Opens.map g.hom.base).obj W) ≫ restrictPreimage g W :=
  (restrictPreimage_uniq _ _ _ (by simp)).symm

/-- **Pullback along an open adic subspace.** For a morphism `f : X ⟶ Y` of adic spaces and an
open `V ⊆ Y`, the open adic subspace `f⁻¹(V)` is the fibre product `X ×_Y V`, with no hypothesis on
`f`. -/
theorem isPullback_restrictPreimage :
    IsPullback (restrictPreimage f V) (X.ofRestrict ((Opens.map f.hom.base).obj V))
      (Y.ofRestrict V) f :=
  isPullback_of_isOpenImmersion _ _ _ _ (restrictPreimage_ofRestrict f V) <| by
    rw [range_ofRestrict, range_ofRestrict]
    rfl

/-- The restriction of an isomorphism of adic spaces over an open is an isomorphism. -/
instance [IsIso f] : IsIso (restrictPreimage f V) :=
  (isPullback_restrictPreimage f V).isIso_fst_of_isIso

/-- The restriction of an open immersion of adic spaces over an open is an open immersion. -/
instance [PreAdicSpace.IsOpenImmersion f.hom] :
    PreAdicSpace.IsOpenImmersion (restrictPreimage f V).hom := by
  rw [restrictPreimage_hom]
  -- `X.restrict` unfolds to `X.obj.restrict` only at default transparency
  exact inferInstanceAs (PreAdicSpace.IsOpenImmersion (f.hom.restrictPreimage V))

end RestrictPreimage

end AdicSpace

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
/-- If `T` spans an open ideal and the structure presheaf of `Spa(A, A⁺)` is a sheaf, then so is the
structure presheaf of `Spa` of the rational localisation `(A⟨T/s⟩, A_U⁺)`, as a pair
(`PairOfDefinition.rationalLocalizationPair`). -/
theorem isSheaf_presentationLimitPresheaf_rationalLocalizationPair {A : Type u}
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
    Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa (P.rationalLocalizationPair U hP T s L hden).plus))
      (presentationLimitPresheaf (P.completionLocalization T s L hden)
        (P.rationalLocalizationPair U hP T s L hden).plus) := by
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  rw [rationalLocalizationPair_plus]
  exact isSheaf_presentationLimitPresheaf_completionLocalization P U.plus
    U.isRingOfIntegralElements.isPowerBounded_of_mem hP T s L hden hT hsheaf

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
