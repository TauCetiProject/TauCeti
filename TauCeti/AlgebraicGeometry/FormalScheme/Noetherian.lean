/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Noetherian

import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Locally noetherian and noetherian formal schemes

A formal scheme `X` is locally noetherian (`TauCeti.FormalScheme.IsLocallyNoetherian`) if every
point has an open neighbourhood admitting an open immersion from `Spf A` for a noetherian adic
ring `A` (EGA I, Ch. I, 10.4.2), and noetherian (`TauCeti.FormalScheme.IsNoetherian`) if it is
locally noetherian and quasi-compact.

The nontrivial foundational theorem is the converse on affine formal opens (EGA I, Ch. I, 10.6.5):
if `ofSpf B` is locally noetherian for an adic ring `B`, then `B` itself is a noetherian ring
(`TauCeti.FormalScheme.isLocallyNoetherian_ofSpf_iff`), and consequently on any locally noetherian
formal scheme `X`, the section ring `Γ(U, O_X)` over *every* affine formal open `U` is noetherian
(`TauCeti.FormalScheme.IsAffineOpen.isNoetherianRing`).

To prove EGA I, Ch. I, 10.6.5: for an ideal of definition `J` of `B`, the thickening
`Spec (B ⧸ J) ⟶ Spf B` is a homeomorphism that is surjective on stalks
(`TauCeti.FormalScheme.Spf.fromSpecQuotient`). Around every prime of `B ⧸ J`, shrinking to a
principal open `D(g) ≅ Spec ((B ⧸ J)_g)` lands inside a noetherian chart `Spf C ⟶ Spf B`. Lifting
`Spec ((B ⧸ J)_g) ⟶ Spf B` into `Spf C` yields an open embedding on underlying spaces that is
surjective on stalks, so `TauCeti.FormalScheme.Spf.isNoetherianRing_of_isOpenEmbedding_fromSpec`
implies that `(B ⧸ J)_g` is noetherian for `g` spanning the unit ideal of `B ⧸ J`. Hence `B ⧸ J` is
noetherian, and `Ideal.isNoetherianRing_of_isAdicComplete` concludes that `B` is noetherian.

## Main definitions

* `TauCeti.FormalScheme.IsLocallyNoetherian`: locally noetherian formal schemes.
* `TauCeti.FormalScheme.IsNoetherian`: noetherian formal schemes (locally noetherian and
  quasi-compact).

## Main results

* `TauCeti.FormalScheme.stalk_isNoetherianRing`: the stalks of a locally noetherian formal scheme
  are noetherian local rings.
* `TauCeti.FormalScheme.isLocallyNoetherian_ofSpf_iff`,
  `TauCeti.FormalScheme.isNoetherian_ofSpf_iff`: `ofSpf A` is (locally) noetherian if and only if
  `A` is a noetherian ring (EGA I, Ch. I, 10.6.5).
* `TauCeti.FormalScheme.IsAffineOpen.isNoetherianRing`,
  `TauCeti.FormalScheme.isLocallyNoetherian_iff_of_iSup_eq_top`,
  `TauCeti.FormalScheme.isLocallyNoetherian_iff_forall_isAffineOpen`: `X` is locally noetherian if
  and only if `Γ(U, O_X)` is noetherian on an affine open cover (equivalently, on every affine
  formal open `U`).
* `TauCeti.FormalScheme.isNoetherian_iff_of_finite_iSup_eq_top`,
  `TauCeti.FormalScheme.isNoetherian_iff_exists_finite_affine_cover_isNoetherianRing`: `X` is
  noetherian if and only if it is covered by finitely many affine formal opens with noetherian
  section rings.
* `TauCeti.FormalScheme.IsNoetherian.noetherianSpace`: every noetherian formal scheme has a
  noetherian underlying topological space.
* `AlgebraicGeometry.Scheme.isLocallyNoetherian_toFormalScheme_iff`,
  `AlgebraicGeometry.Scheme.isNoetherian_toFormalScheme_iff`: `Scheme.toFormalScheme` (`ofScheme`)
  preserves and reflects both `IsLocallyNoetherian` and `IsNoetherian`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.2 and
  10.6.5.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY) and
  [Tag 01OU](https://stacks.math.columbia.edu/tag/01OU).
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme

/-- For a noetherian adic ring `A`, `ofSpf A` has a noetherian underlying topological space. -/
instance noetherianSpace_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [IsNoetherianRing A] : NoetherianSpace (ofSpf A) :=
  Spf.noetherianSpace_carrier

/-- A formal scheme `X` is locally noetherian if every point admits an open immersion from `Spf A`
for a noetherian adic ring `A` (EGA I, Ch. I, 10.4.2). -/
@[mk_iff]
class IsLocallyNoetherian (X : FormalScheme) : Prop where
  /-- Around every point of `X` there is an open-immersion chart from the formal spectrum of a
  noetherian adic ring. -/
  exists_noetherian_spf (x : X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (_ : IsNoetherianRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base

/-- A formal scheme `X` is noetherian if it is locally noetherian and quasi-compact
(EGA I, Ch. I, 10.4.2). -/
@[mk_iff]
class IsNoetherian (X : FormalScheme) : Prop extends X.IsLocallyNoetherian, CompactSpace X

section BasicProperties

/-- For a noetherian adic ring `A`, `ofSpf A` is locally noetherian. -/
instance isLocallyNoetherian_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [IsNoetherianRing A] :
    (ofSpf A).IsLocallyNoetherian where
  exists_noetherian_spf x :=
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      𝟙 (Spf A), inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A))), ⟨x, rfl⟩⟩

/-- For a noetherian adic ring `A`, `ofSpf A` is noetherian. -/
instance isNoetherian_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [IsNoetherianRing A] :
    (ofSpf A).IsNoetherian where

/-- Every open neighbourhood of a point in a locally noetherian formal scheme contains a
noetherian `Spf` chart around that point. -/
theorem exists_noetherian_spf_mem_range_and_range_subset (X : FormalScheme)
    [X.IsLocallyNoetherian] (U : Opens X) (x : X) (hx : x ∈ U) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (_ : IsNoetherianRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base ∧
        Set.range f.base ⊆ (U : Set X) := by
  obtain ⟨A, _, _, _, _, _, i, hi, y, hy⟩ := IsLocallyNoetherian.exists_noetherian_spf x
  have := hi
  obtain ⟨V, ⟨a, rfl⟩, hyV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen) (Opens.mem_map.mpr (hy.symm ▸ hx))
  obtain ⟨z, hz⟩ := (Spf.range_basicOpenι a).ge hyV
  refine ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Spf.basicOpenι a ≫ i, inferInstance, ⟨z, ?_⟩, ?_⟩
  · simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hz] using hy
  · rintro _ ⟨w, rfl⟩
    exact hVU ((Spf.range_basicOpenι a).le (Set.mem_range_self w))

/-- An open immersion into a locally noetherian formal scheme has locally noetherian source. -/
theorem isLocallyNoetherian_of_isOpenImmersion {X Y : FormalScheme} (f : X ⟶ Y)
    [hf : LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f)]
    [Y.IsLocallyNoetherian] : X.IsLocallyNoetherian where
  exists_noetherian_spf x := by
    let j : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace := forgetToLocallyRingedSpace.map f
    have hj : LocallyRingedSpace.IsOpenImmersion j := hf
    let U : Opens Y := ⟨Set.range j.base, hj.base_open.isOpen_range⟩
    obtain ⟨A, _, _, _, _, _, i, hi, hx, hU⟩ :=
      Y.exists_noetherian_spf_mem_range_and_range_subset U (j.base x) ⟨x, rfl⟩
    have := hi
    let g := LocallyRingedSpace.IsOpenImmersion.lift j i hU
    have hg : LocallyRingedSpace.IsOpenImmersion g :=
      LocallyRingedSpace.IsOpenImmersion.isOpenImmersion_lift j i hU
    obtain ⟨y, hy⟩ := hx
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      g, hg, y, hj.base_open.injective ?_⟩
    have hfac := congrArg (fun t : Spf A ⟶ Y.toLocallyRingedSpace ↦ t.base y)
      (LocallyRingedSpace.IsOpenImmersion.lift_fac j i hU)
    exact hfac.trans hy

/-- Every open formal subscheme of a locally noetherian formal scheme is locally noetherian. -/
instance isLocallyNoetherian_restrict (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X) :
    (X.restrict U).IsLocallyNoetherian :=
  isLocallyNoetherian_of_isOpenImmersion (X.ofRestrict U)

/-- Every quasi-compact open formal subscheme of a locally noetherian formal scheme is
noetherian. -/
instance isNoetherian_restrict (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X)
    [CompactSpace U] : (X.restrict U).IsNoetherian where
  toCompactSpace := ‹CompactSpace U›

/-- `IsLocallyNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isLocallyNoetherian_iff_of_iso {X Y : FormalScheme} (e : X ≅ Y) :
    X.IsLocallyNoetherian ↔ Y.IsLocallyNoetherian :=
  ⟨fun _ ↦ isLocallyNoetherian_of_isOpenImmersion e.inv,
    fun _ ↦ isLocallyNoetherian_of_isOpenImmersion e.hom⟩

/-- `IsNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isNoetherian_iff_of_iso {X Y : FormalScheme} (e : X ≅ Y) :
    X.IsNoetherian ↔ Y.IsNoetherian := by
  have hcomp : CompactSpace X ↔ CompactSpace Y := by
    let h := TopCat.homeoOfIso
      (LocallyRingedSpace.forgetToTop.mapIso (forgetToLocallyRingedSpace.mapIso e))
    refine ⟨fun hX ↦ ?_, fun hY ↦ ?_⟩
    · have : CompactSpace
          (LocallyRingedSpace.forgetToTop.obj (forgetToLocallyRingedSpace.obj X)) := hX
      exact h.compactSpace
    · have : CompactSpace
          (LocallyRingedSpace.forgetToTop.obj (forgetToLocallyRingedSpace.obj Y)) := hY
      exact h.symm.compactSpace
  rw [isNoetherian_iff, isNoetherian_iff, isLocallyNoetherian_iff_of_iso e, hcomp]

/-- Every stalk of a locally noetherian formal scheme is a noetherian ring. -/
instance stalk_isNoetherianRing (X : FormalScheme) [X.IsLocallyNoetherian] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨A, _, _, _, _, _, f, hf, y, rfl⟩ := IsLocallyNoetherian.exists_noetherian_spf x
  have := hf
  have : IsNoetherianRing ((Spf A).presheaf.stalk y) := Spf.isNoetherianRing_stalk y
  let e := asIso (f.stalkMap y)
  exact isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv

end BasicProperties

section ConverseAffine

private theorem isNoetherianRing_away_quotient_of_chart {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] [(ofSpf B).IsLocallyNoetherian]
    (y : PrimeSpectrum (B ⧸ IsAdicRing.ideal B)) :
    ∃ g : B ⧸ IsAdicRing.ideal B, y ∈ PrimeSpectrum.basicOpen g ∧
      IsNoetherianRing (Localization.Away g) := by
  let J := IsAdicRing.ideal B
  have hJ : IsAdic J := (IsAdicRing.ideal_spec B).2.1
  let R₀ := B ⧸ J
  let qJ := Spf.fromSpecQuotient hJ
  obtain ⟨C, _, _, _, _, _, j₀, hj₀, hqy⟩ :=
    IsLocallyNoetherian.exists_noetherian_spf (X := ofSpf B) (qJ.base y)
  let j : Spf C ⟶ Spf B := j₀
  have hj : LocallyRingedSpace.IsOpenImmersion j := hj₀
  let V : Opens (PrimeSpectrum R₀) :=
    ⟨qJ.base ⁻¹' Set.range j.base, hj.base_open.isOpen_range.preimage qJ.base.hom.continuous⟩
  obtain ⟨_, ⟨g, rfl⟩, hyg, hgV⟩ :=
    Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens (U := V)
      (Opens.mem_mk.mpr (Set.mem_preimage.mpr hqy))
  let R := Localization.Away g
  let ιg : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap R₀ R))
  have : AlgebraicGeometry.IsOpenImmersion ιg :=
    AlgebraicGeometry.IsOpenImmersion.of_isLocalization g
  let β : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf B :=
    Scheme.forgetToLocallyRingedSpace.map ιg ≫ qJ
  have hrange : Set.range β.base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    have hmem : PrimeSpectrum.comap (algebraMap R₀ R) x ∈
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R₀)) := by
      rw [← PrimeSpectrum.localization_away_comap_range R g]
      exact ⟨x, rfl⟩
    exact hgV hmem
  have hβ_open : Topology.IsOpenEmbedding β.base :=
    (Spf.fromSpecQuotient_isHomeomorph hJ).isOpenEmbedding.comp ιg.isOpenEmbedding
  have hβ_stalk (x : Spec (CommRingCat.of R)) : Function.Surjective (β.stalkMap x) := by
    have hcomp := PresheafedSpace.stalkMap.comp ιg.toPshHom qJ.toHom x
    intro z
    obtain ⟨w, hw⟩ := ((ConcreteCategory.bijective_of_isIso (ιg.stalkMap x)).surjective.comp
      (Spf.fromSpecQuotient_stalk_surjective hJ (ιg x))) z
    exact ⟨w, (ConcreteCategory.congr_hom hcomp w).trans hw⟩
  exact ⟨g, hyg, Spf.isNoetherianRing_of_isOpenEmbedding_fromSpec _
    (LocallyRingedSpace.IsOpenImmersion.isOpenEmbedding_lift j β hβ_open hrange)
    fun x ↦ LocallyRingedSpace.IsOpenImmersion.stalkMap_lift_surjective j β hrange (hβ_stalk x)⟩

/-- For an adic ring `A`, the affine formal scheme `ofSpf A` is locally noetherian if and only if
`A` is a noetherian ring (EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem isLocallyNoetherian_ofSpf_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).IsLocallyNoetherian ↔ IsNoetherianRing A := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  let J := IsAdicRing.ideal A
  have hJfg : J.FG := (IsAdicRing.ideal_spec A).1
  have : IsAdicComplete J A := (IsAdicRing.ideal_spec A).2.2
  choose g hyg hnoeth using isNoetherianRing_away_quotient_of_chart (B := A)
  have htop : (⨆ y, PrimeSpectrum.basicOpen (g y)) = ⊤ :=
    eq_top_iff.mpr fun y _ ↦ Opens.mem_iSup.mpr ⟨y, hyg y⟩
  have hspan : Ideal.span (Set.range g) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp htop
  obtain ⟨S, hSsub, hS1⟩ := Submodule.mem_span_finite_of_mem_span
    (hspan.symm ▸ Submodule.mem_top : (1 : A ⧸ J) ∈ Ideal.span (Set.range g))
  have hSspan : Ideal.span (S : Set (A ⧸ J)) = ⊤ := Ideal.eq_top_of_isUnit_mem _ hS1 isUnit_one
  have : IsNoetherianRing (A ⧸ J) := by
    refine AlgebraicGeometry.isNoetherianRing_of_away S hSspan fun s ↦ ?_
    obtain ⟨y, hy⟩ := hSsub s.property
    exact hy ▸ hnoeth y
  exact Ideal.isNoetherianRing_of_isAdicComplete J hJfg

/-- For an adic ring `A`, `ofSpf A` is noetherian if and only if `A` is a noetherian ring
(EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem isNoetherian_ofSpf_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).IsNoetherian ↔ IsNoetherianRing A := by
  have hc : CompactSpace (ofSpf A) := inferInstance
  rw [isNoetherian_iff, isLocallyNoetherian_ofSpf_iff, and_iff_left hc]

end ConverseAffine

section AffineOpensAndTopology

/-- On a locally noetherian formal scheme `X`, the topologized section ring `hU.Sections` over any
affine formal open `U` is a noetherian ring (EGA I, Ch. I, 10.6.5). -/
instance IsAffineOpen.isNoetherianRing_sections {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : IsNoetherianRing hU.Sections :=
  (isLocallyNoetherian_ofSpf_iff hU.Sections).mp
    ((isLocallyNoetherian_iff_of_iso hU.isoSpf).mp inferInstance)

/-- On a locally noetherian formal scheme `X`, `Γ(U, O_X)` is a noetherian ring for every affine
formal open `U` (EGA I, Ch. I, 10.6.5). -/
theorem IsAffineOpen.isNoetherianRing {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : IsNoetherianRing (X.presheaf.obj (op U)) :=
  inferInstanceAs (IsNoetherianRing hU.Sections)

/-- An affine formal open `U` whose section ring `Γ(U, O_X)` is noetherian has a noetherian
underlying topological space. -/
theorem noetherianSpace_of_isAffineOpen {X : FormalScheme} (U : Opens X) (hU : X.IsAffineOpen U)
    [IsNoetherianRing (X.presheaf.obj (op U))] : NoetherianSpace U := by
  have : IsNoetherianRing hU.Sections :=
    inferInstanceAs (IsNoetherianRing (X.presheaf.obj (op U)))
  have : NoetherianSpace
      (LocallyRingedSpace.forgetToTop.obj
        (forgetToLocallyRingedSpace.obj (ofSpf hU.Sections))) :=
    noetherianSpace_ofSpf hU.Sections
  let h := TopCat.homeoOfIso
    (LocallyRingedSpace.forgetToTop.mapIso (forgetToLocallyRingedSpace.mapIso hU.isoSpf))
  exact (noetherianSpace_iff_of_homeomorph h).mpr inferInstance

/-- On a locally noetherian formal scheme `X`, every affine formal open is a noetherian topological
space. -/
theorem IsAffineOpen.noetherianSpace {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : NoetherianSpace U :=
  have := hU.isNoetherianRing
  noetherianSpace_of_isAffineOpen U hU

/-- Given an affine open cover `⨆ i, U i = ⊤` of `X`, `X` is locally noetherian if and only if
every section ring `Γ(U i, O_X)` is noetherian. -/
theorem isLocallyNoetherian_iff_of_iSup_eq_top {X : FormalScheme} {ι : Type*} {U : ι → Opens X}
    (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    X.IsLocallyNoetherian ↔ ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  refine ⟨fun _ i ↦ (hU i).isNoetherianRing, fun hnoeth ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcov ▸ Opens.mem_top x)
  have : IsNoetherianRing (hU i).Sections := hnoeth i
  exact ⟨(hU i).Sections, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, forgetToLocallyRingedSpace.map (hU i).fromSpf, (hU i).isOpenImmersion_fromSpf,
    ((hU i).range_fromSpf).ge hxi⟩

/-- If `X` is covered by affine formal opens with noetherian section rings, then `X` is locally
noetherian. -/
theorem isLocallyNoetherian_of_iSup_eq_top {X : FormalScheme} {ι : Type*} {U : ι → Opens X}
    (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hnoeth : ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i)))) :
    X.IsLocallyNoetherian :=
  (isLocallyNoetherian_iff_of_iSup_eq_top hU hcov).mpr hnoeth

/-- A formal scheme `X` is locally noetherian if and only if `Γ(U, O_X)` is a noetherian ring for
every affine formal open `U` of `X`. -/
theorem isLocallyNoetherian_iff_forall_isAffineOpen (X : FormalScheme) :
    X.IsLocallyNoetherian ↔
      ∀ (U : Opens X), X.IsAffineOpen U → IsNoetherianRing (X.presheaf.obj (op U)) :=
  (isLocallyNoetherian_iff_of_iSup_eq_top (fun U : {U : Opens X // X.IsAffineOpen U} ↦ U.property)
    X.iSup_affineOpens_eq_top).trans Subtype.forall

/-- Given a finite affine open cover `⨆ i, U i = ⊤` of `X`, `X` is noetherian if and only if every
section ring `Γ(U i, O_X)` is noetherian. -/
theorem isNoetherian_iff_of_finite_iSup_eq_top {X : FormalScheme} {ι : Type*} [Finite ι]
    {U : ι → Opens X} (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    X.IsNoetherian ↔ ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  have huniv : (Set.univ : Set X) = ⋃ i, (U i : Set X) :=
    Set.ext fun x ↦ by simp [← Opens.mem_iSup, hcov]
  have hc : CompactSpace X :=
    isCompact_univ_iff.mp (huniv ▸ isCompact_iUnion fun i ↦ (hU i).isCompact)
  rw [isNoetherian_iff, isLocallyNoetherian_iff_of_iSup_eq_top hU hcov, and_iff_left hc]

/-- A formal scheme is noetherian if and only if it admits a finite affine open cover with
noetherian section rings. -/
theorem isNoetherian_iff_exists_finite_affine_cover_isNoetherianRing (X : FormalScheme) :
    X.IsNoetherian ↔
      ∃ (n : ℕ) (U : Fin n → Opens X), (∀ i, X.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ ∧
        ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨n, U, hU, hcov⟩ := X.exists_finite_affine_cover
    exact ⟨n, U, hU, hcov, (isNoetherian_iff_of_finite_iSup_eq_top hU hcov).mp inferInstance⟩
  · rintro ⟨n, U, hU, hcov, hnoeth⟩
    exact (isNoetherian_iff_of_finite_iSup_eq_top hU hcov).mpr hnoeth

/-- Every noetherian formal scheme has a noetherian underlying topological space. -/
instance IsNoetherian.noetherianSpace (X : FormalScheme) [X.IsNoetherian] :
    NoetherianSpace X := by
  obtain ⟨n, U, hU, hcov⟩ := X.exists_finite_affine_cover
  have huniv : (⋃ i, (U i : Set X)) = Set.univ :=
    Set.ext fun x ↦ by simp [← Opens.mem_iSup, hcov]
  have (i : Fin n) : NoetherianSpace (U i : Set X) := (hU i).noetherianSpace
  exact TopologicalSpace.noetherian_univ_iff.mp
    (huniv ▸ TopologicalSpace.NoetherianSpace.iUnion fun i ↦ (U i : Set X))

/-- A locally noetherian formal scheme with noetherian underlying space is noetherian. -/
theorem isNoetherian_of_noetherianSpace (X : FormalScheme) [X.IsLocallyNoetherian]
    [NoetherianSpace X] : X.IsNoetherian :=
  have : CompactSpace X := TopologicalSpace.NoetherianSpace.compactSpace X
  ⟨⟩

end AffineOpensAndTopology

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- An ordinary scheme `Y` is locally noetherian as a formal scheme if and only if it is locally
noetherian as a scheme. -/
@[simp]
theorem isLocallyNoetherian_toFormalScheme_iff (Y : Scheme.{u}) :
    Y.toFormalScheme.IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian Y := by
  rw [isLocallyNoetherian_iff_forall_isAffineOpen]
  constructor
  · intro h
    refine ⟨fun U ↦ ?_⟩
    exact h U.val ((Y.isAffineOpen_toFormalScheme_iff U.val).mpr U.property)
  · intro h U hU
    exact AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
      ⟨U, (Y.isAffineOpen_toFormalScheme_iff U).mp hU⟩

instance isLocallyNoetherian_toFormalScheme (Y : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian Y] : Y.toFormalScheme.IsLocallyNoetherian :=
  Y.isLocallyNoetherian_toFormalScheme_iff.mpr inferInstance

/-- An ordinary scheme `Y` is noetherian as a formal scheme if and only if it is noetherian as a
scheme. -/
@[simp]
theorem isNoetherian_toFormalScheme_iff (Y : Scheme.{u}) :
    Y.toFormalScheme.IsNoetherian ↔ AlgebraicGeometry.IsNoetherian Y := by
  rw [FormalScheme.isNoetherian_iff, AlgebraicGeometry.isNoetherian_iff,
    Y.isLocallyNoetherian_toFormalScheme_iff]
  rfl

instance isNoetherian_toFormalScheme (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y] :
    Y.toFormalScheme.IsNoetherian :=
  Y.isNoetherian_toFormalScheme_iff.mpr inferInstance

end AlgebraicGeometry.Scheme
