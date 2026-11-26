/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Locally noetherian formal schemes

A formal scheme `X` is *locally noetherian* if every point has an open neighbourhood isomorphic to
the formal spectrum `Spf A` of a noetherian adic ring `A`, and *noetherian* if moreover its
underlying space is quasi-compact (EGA I, Ch. I, 10.4.2). This file shows that the condition does
not depend on the chosen charts: on a locally noetherian formal scheme, the ring of sections of
every affine formal open is noetherian. In particular `Spf A` is (locally) noetherian exactly when
`A` is a noetherian ring (EGA I, Ch. I, 10.6.5). Every noetherian formal scheme has a noetherian
underlying topological space (`IsNoetherian.noetherianSpace`), and for ordinary schemes the notion
agrees with Mathlib's `AlgebraicGeometry.IsLocallyNoetherian`.

## Implementation notes

The key step is affine. Let `Spf B` be an affine formal open of `X`. Every point of `Spf B` lies in
a basic open set `D(b)` that is also a basic open set of a noetherian chart `Spf A` of `X`. Indeed,
the basic open set `D(a)` of `Spf A` is the locus where the global section `a` is invertible, and
being invertible is preserved by the stalk maps of an open immersion, which are isomorphisms. So
the completed localisation `B_{b} ≅ A_{a}` is noetherian. Reducing modulo an ideal of definition
`J` of `B`, the localisations of `B ⧸ J` at the images of the elements `b` are the quotients
`B_{b} ⧸ J B_{b}`, hence noetherian; as these elements generate the unit ideal of `B ⧸ J`, the ring
`B ⧸ J` is noetherian. Since `B` is `J`-adically complete and `J` is finitely generated, `B` is
noetherian (EGA I, Ch. 0, 7.2.6).

## Main definitions

* `TauCeti.FormalScheme.IsLocallyNoetherian`: every point lies in an open formal spectrum of a
  noetherian adic ring.
* `TauCeti.FormalScheme.IsNoetherian`: locally noetherian with quasi-compact underlying space.

## Main results

* `TauCeti.FormalScheme.isNoetherianRing_of_isOpenImmersion`: an open formal spectrum `Spf B` of a
  locally noetherian formal scheme has `B` noetherian.
* `TauCeti.FormalScheme.isLocallyNoetherian_iff_forall_isAffineOpen`,
  `TauCeti.FormalScheme.isLocallyNoetherian_iff_of_iSup_eq_top`: a formal scheme is locally
  noetherian if and only if the ring of sections over every open in an affine open cover
  (equivalently, over every affine formal open) is noetherian.
* `TauCeti.FormalScheme.isNoetherian_iff_of_finite_iSup_eq_top`,
  `TauCeti.FormalScheme.isNoetherian_iff_exists_finite_affine_cover_isNoetherianRing`: a formal
  scheme is noetherian if and only if it is covered by finitely many affine formal opens with
  noetherian section rings.
* `TauCeti.FormalScheme.isLocallyNoetherian_ofSpf_iff`,
  `TauCeti.FormalScheme.isNoetherian_ofSpf_iff`: `Spf A` is (locally) noetherian if and only if
  `A` is noetherian.
* `TauCeti.FormalScheme.IsLocallyNoetherian.of_isOpenImmersion`,
  `TauCeti.FormalScheme.isLocallyNoetherian_iff_of_iso`,
  `TauCeti.FormalScheme.isNoetherian_iff_of_iso`: stability under open immersions, open
  restrictions (`isNoetherian_restrict`), and isomorphisms.
* `TauCeti.FormalScheme.isNoetherianRing_stalk`: the stalks of a locally noetherian formal scheme
  are noetherian local rings.
* `TauCeti.FormalScheme.IsNoetherian.noetherianSpace`: every noetherian formal scheme has a
  noetherian underlying topological space.
* `TauCeti.FormalScheme.isLocallyNoetherian_toFormalScheme_iff`,
  `TauCeti.FormalScheme.isNoetherian_toFormalScheme_iff`: an ordinary scheme is a (locally)
  noetherian formal scheme if and only if it is a (locally) noetherian scheme.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.2.6, and
  Ch. I, 10.1.6, 10.4.2 and 10.6.5.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

namespace TauCeti.FormalScheme

namespace Spf

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B]

/-- If an open immersion from the formal spectrum of a noetherian adic ring hits the open prime `y`
of `B`, then `y` lies in a basic open set `D(b)` whose completed localisation `B_{b}` is
noetherian. -/
private theorem exists_mem_basicOpen_isNoetherianRing [IsNoetherianRing A] (χ : Spf A ⟶ Spf B)
    [hχ : LocallyRingedSpace.IsOpenImmersion χ] {y : carrier B} (hy : y ∈ Set.range χ.base) :
    ∃ b : B, y ∈ basicOpen b ∧ IsNoetherianRing (AdicRing.CompletedAway B b) := by
  -- the range of `χ` as an open set, so that the basis lemma knows which neighbourhood of `y`
  -- to shrink; membership in it is membership in the range, which is `hy`
  let V : Opens (carrier B) := ⟨Set.range χ.base, hχ.base_open.isOpen_range⟩
  have hyV : y ∈ V := hy
  obtain ⟨_, ⟨b, rfl⟩, hyb, hbχ⟩ := (Opens.isBasis_iff_nbhd.mp isBasis_basicOpen) hyV
  refine ⟨b, hyb, ?_⟩
  -- the preimage of `D(b)` is the basic open set of the pulled-back global section
  set a := (topSectionsIso A).hom (χ.c.app (op ⊤) ((topSectionsIso B).inv b))
  have hpre : (Opens.map χ.base).obj (basicOpen b) = basicOpen a := by
    have ha : χ.c.app (op ⊤) ((topSectionsIso B).inv b) = (topSectionsIso A).inv a :=
      (Iso.hom_inv_id_apply _ _).symm
    exact (congrArg (Opens.map χ.base).obj (basicOpen_topSectionsIso_inv b).symm).trans
      ((LocallyRingedSpace.preimage_basicOpen χ _).trans
        ((congrArg _ ha).trans (basicOpen_topSectionsIso_inv a)))
  -- `χ` identifies `D(a) ≅ Spf A_{a}` with `D(b) ≅ Spf B_{b}`
  let f₁ := (Spf A).ofRestrict (basicOpen a).isOpenEmbedding ≫ χ
  let f₂ := (Spf B).ofRestrict (basicOpen b).isOpenEmbedding
  have hD : Set.range ((Spf A).ofRestrict (basicOpen a).isOpenEmbedding).base =
      χ.base ⁻¹' (basicOpen b : Set (carrier B)) :=
    Subtype.range_coe.trans (congrArg SetLike.coe hpre).symm
  have hrange : Set.range f₁.base = Set.range f₂.base := by
    simp only [f₁, f₂, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (congrArg _ hD).trans ((Set.image_preimage_eq_of_subset hbχ).trans
      Subtype.range_coe.symm)
  let e : (Spf A).restrict (basicOpen a).isOpenEmbedding ≅
      (Spf B).restrict (basicOpen b).isOpenEmbedding :=
    LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.IsOpenImmersion.isoOfRangeEq f₁.toHom f₂.toHom hrange
  exact isNoetherianRing_of_ringEquiv _
    (isoToRingEquiv ((restrictBasicOpenIso a).symm ≪≫ e ≪≫ restrictBasicOpenIso b).symm)

/-- If every open prime of `B` lies in a basic open set `D(b)` whose completed localisation `B_{b}`
is noetherian, then `B` is noetherian. -/
private theorem isNoetherianRing_of_forall_exists
    (h : ∀ y : carrier B, ∃ b : B, y ∈ basicOpen b ∧
      IsNoetherianRing (AdicRing.CompletedAway B b)) :
    IsNoetherianRing B := by
  obtain ⟨hJfg, hJ, hJc⟩ := IsAdicRing.ideal_spec B
  set J := IsAdicRing.ideal B
  choose b hb hN using h
  -- the images of the elements `b y` generate the unit ideal of `B ⧸ J`
  have hspan : Ideal.span (Set.range fun y ↦ Ideal.Quotient.mk (J ^ 1) (b y)) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let P : PrimeSpectrum B := ⟨M.comap (Ideal.Quotient.mk _), Ideal.comap_isPrime _ _⟩
    have hP : P ∈ carrier B := (mem_carrier_iff_le hJ).mpr fun x hx ↦ Ideal.mem_comap.mpr <| by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [pow_one])]
      exact M.zero_mem
    exact mem_basicOpen.mp (hb ⟨P, hP⟩) (hle (Ideal.subset_span ⟨⟨P, hP⟩, rfl⟩))
  obtain ⟨S, hSsub, hS⟩ := (Ideal.span_eq_top_iff_finite _).mp hspan
  -- each localisation of `B ⧸ J` is a quotient of a noetherian completed localisation
  have : IsNoetherianRing (B ⧸ J ^ 1) := isNoetherianRing_of_away S hS fun ⟨s, hs⟩ ↦ by
    obtain ⟨y, rfl⟩ := hSsub hs
    exact isNoetherianRing_of_ringEquiv _
      (AdicRing.CompletedAway.quotientPowEquiv B (b y) 1).toRingEquiv
  have : IsNoetherianRing (B ⧸ J) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.quotEquivOfEq (pow_one J))
  exact Ideal.isNoetherianRing_of_isAdicComplete J hJfg

end Spf

/-- A formal scheme is **locally noetherian** if every point lies in an open formal spectrum
`Spf A` of a noetherian adic ring `A` (EGA I, Ch. I, 10.4.2). By
`isLocallyNoetherian_iff_forall_isAffineOpen`, the ring of sections of every affine formal open is
then noetherian. -/
class IsLocallyNoetherian (X : FormalScheme.{u}) : Prop where
  /-- Every point lies in the image of an open immersion from the formal spectrum of a noetherian
  adic ring. -/
  exists_isNoetherianRing (x : X) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (_ : IsNoetherianRing A) (f : Spf A ⟶ X.toLocallyRingedSpace),
      LocallyRingedSpace.IsOpenImmersion f ∧ x ∈ Set.range f.base

/-- A formal scheme is **noetherian** if it is locally noetherian and its underlying space is
quasi-compact (EGA I, Ch. I, 10.4.2). -/
class IsNoetherian (X : FormalScheme.{u}) : Prop extends IsLocallyNoetherian X, CompactSpace X

variable {X : FormalScheme.{u}}

/-- The ring of sections of `X` over the image `U` of an open immersion `Spf B → X` is noetherian
if and only if `B` is. -/
private theorem isNoetherianRing_sections_iff {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsAdicRing B] (f : Spf B ⟶ X.toLocallyRingedSpace)
    [hf : LocallyRingedSpace.IsOpenImmersion f] {U : Opens X}
    (hU : Set.range f.base = (U : Set X)) :
    IsNoetherianRing (X.presheaf.obj (op U)) ↔ IsNoetherianRing B := by
  -- the chart `X|_U ≅ Spf B` given by `f`, whose ring isomorphism `Γ(X, U) ≅ B` transfers
  -- noetherianity
  let e : X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅ Spf B :=
    (LocallyRingedSpace.isoOfSheafedSpaceIso <| SheafedSpace.isoMk <|
      PresheafedSpace.IsOpenImmersion.isoOfRangeEq f.toHom
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).toHom
        (hU.trans Subtype.range_coe.symm)).symm
  let φ := (chartSectionsIso X U e).commRingCatIsoToRingEquiv
  exact ⟨fun _ ↦ isNoetherianRing_of_ringEquiv _ φ, fun _ ↦ isNoetherianRing_of_ringEquiv _ φ.symm⟩

/-- On a locally noetherian formal scheme, every point of the source of an open immersion into it
lies in an open formal spectrum of a noetherian adic ring. -/
private theorem exists_isNoetherianRing_of_isOpenImmersion [X.IsLocallyNoetherian]
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ X.toLocallyRingedSpace)
    [hg : LocallyRingedSpace.IsOpenImmersion g] (y : Y) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsAdicRing A) (_ : IsNoetherianRing A) (f : Spf A ⟶ Y),
      LocallyRingedSpace.IsOpenImmersion f ∧ y ∈ Set.range f.base := by
  obtain ⟨A, _, _, _, _, _, φ, hφ, hx⟩ := IsLocallyNoetherian.exists_isNoetherianRing (g.base y)
  obtain ⟨a, hxa, haW⟩ := exists_basicOpenι_comp_mem_range_and_range_subset φ
    ⟨_, hg.base_open.isOpen_range⟩ (Set.mem_range_self y) hx
  -- the open set in `haW` is the range of `g`, as `lift` expects
  replace haW : Set.range (Spf.basicOpenι a ≫ φ).base ⊆ Set.range g.base := haW
  refine ⟨AdicRing.CompletedAway A a, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, LocallyRingedSpace.IsOpenImmersion.lift g _ haW,
    LocallyRingedSpace.IsOpenImmersion.isOpenImmersion_lift g _ haW, ?_⟩
  rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
  exact hxa

/-- **An open formal spectrum of a locally noetherian formal scheme is noetherian**: if
`Spf B → X` is an open immersion and `X` is locally noetherian, then `B` is noetherian
(EGA I, Ch. I, 10.6.5). -/
theorem isNoetherianRing_of_isOpenImmersion [X.IsLocallyNoetherian] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsAdicRing B] (f : Spf B ⟶ X.toLocallyRingedSpace)
    [hf : LocallyRingedSpace.IsOpenImmersion f] : IsNoetherianRing B :=
  Spf.isNoetherianRing_of_forall_exists fun y ↦ by
    obtain ⟨A, _, _, _, _, _, χ, hχ, hy⟩ := exists_isNoetherianRing_of_isOpenImmersion f y
    exact Spf.exists_mem_basicOpen_isNoetherianRing χ hy

/-- A formal scheme is locally noetherian if and only if the ring of sections of every affine
formal open is noetherian (EGA I, Ch. I, 10.4.2 and 10.6.5). -/
theorem isLocallyNoetherian_iff_forall_isAffineOpen :
    X.IsLocallyNoetherian ↔
      ∀ U : Opens X, X.IsAffineOpen U → IsNoetherianRing (X.presheaf.obj (op U)) := by
  refine ⟨fun _ U hU ↦ ?_, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  · obtain ⟨B, _, _, _, _, f, hf, hU⟩ := (isAffineOpen_def X U).mp hU
    exact (isNoetherianRing_sections_iff f hU).mpr (isNoetherianRing_of_isOpenImmersion f)
  · obtain ⟨B, _, _, _, _, f, hf, hx⟩ := X.local_spf x
    have := h ⟨_, hf.base_open.isOpen_range⟩ ((isAffineOpen_def X _).mpr ⟨B, inferInstance,
      inferInstance, inferInstance, inferInstance, f, hf, rfl⟩)
    exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
      (isNoetherianRing_sections_iff f (U := ⟨_, hf.base_open.isOpen_range⟩) rfl).mp this,
      f, hf, hx⟩

/-- The ring of sections of an affine formal open of a locally noetherian formal scheme is
noetherian. -/
theorem IsAffineOpen.isNoetherianRing [X.IsLocallyNoetherian] {U : Opens X}
    (hU : X.IsAffineOpen U) : IsNoetherianRing (X.presheaf.obj (op U)) :=
  isLocallyNoetherian_iff_forall_isAffineOpen.mp ‹_› U hU

/-- The source of an open immersion into a locally noetherian formal scheme is locally
noetherian. -/
theorem IsLocallyNoetherian.of_isOpenImmersion {Y : FormalScheme.{u}} [X.IsLocallyNoetherian]
    (f : Y ⟶ X) [LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map f)] :
    Y.IsLocallyNoetherian :=
  ⟨exists_isNoetherianRing_of_isOpenImmersion (hg := ‹_›) (forgetToLocallyRingedSpace.map f)⟩

/-- Open formal subschemes of a locally noetherian formal scheme are locally noetherian. -/
instance [X.IsLocallyNoetherian] (U : Opens X) : (X.restrict U).IsLocallyNoetherian :=
  IsLocallyNoetherian.of_isOpenImmersion (X := X) (X.ofRestrict U)

/-- A quasi-compact open formal subscheme of a locally noetherian formal scheme is noetherian. -/
theorem isNoetherian_restrict [X.IsLocallyNoetherian] {U : Opens X}
    (hU : IsCompact (U : Set X)) : (X.restrict U).IsNoetherian where
  toCompactSpace := isCompact_iff_compactSpace.mp hU

/-- Quasi-compact open formal subschemes of a locally noetherian formal scheme are noetherian. -/
instance [X.IsLocallyNoetherian] (U : Opens X) [CompactSpace U] : (X.restrict U).IsNoetherian :=
  isNoetherian_restrict (isCompact_iff_compactSpace.mpr ‹_›)

/-- `IsLocallyNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isLocallyNoetherian_iff_of_iso {X Y : FormalScheme.{u}} (e : X ≅ Y) :
    X.IsLocallyNoetherian ↔ Y.IsLocallyNoetherian := by
  have : IsIso (forgetToLocallyRingedSpace.map e.inv) := Functor.map_isIso _ _
  have : IsIso (forgetToLocallyRingedSpace.map e.hom) := Functor.map_isIso _ _
  exact ⟨fun _ ↦ IsLocallyNoetherian.of_isOpenImmersion e.inv,
    fun _ ↦ IsLocallyNoetherian.of_isOpenImmersion e.hom⟩

/-- `IsNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isNoetherian_iff_of_iso {X Y : FormalScheme.{u}} (e : X ≅ Y) :
    X.IsNoetherian ↔ Y.IsNoetherian := by
  let h := TopCat.homeoOfIso
    (LocallyRingedSpace.forgetToTop.mapIso (forgetToLocallyRingedSpace.mapIso e))
  refine ⟨fun hX ↦ ?_, fun hY ↦ ?_⟩
  · have : CompactSpace
        (LocallyRingedSpace.forgetToTop.obj (forgetToLocallyRingedSpace.obj X)) :=
      hX.toCompactSpace
    exact { toIsLocallyNoetherian :=
              (isLocallyNoetherian_iff_of_iso e).mp hX.toIsLocallyNoetherian
            toCompactSpace := h.compactSpace }
  · have : CompactSpace
        (LocallyRingedSpace.forgetToTop.obj (forgetToLocallyRingedSpace.obj Y)) :=
      hY.toCompactSpace
    exact { toIsLocallyNoetherian :=
              (isLocallyNoetherian_iff_of_iso e).mpr hY.toIsLocallyNoetherian
            toCompactSpace := h.symm.compactSpace }

/-- The stalks of a locally noetherian formal scheme are noetherian local rings
(EGA I, Ch. I, 10.1.6). -/
instance isNoetherianRing_stalk [X.IsLocallyNoetherian] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨A, _, _, _, _, _, f, hf, z, rfl⟩ := IsLocallyNoetherian.exists_isNoetherianRing x
  have := Spf.isNoetherianRing_stalk (A := A) z
  exact isNoetherianRing_of_ringEquiv _ (asIso (f.stalkMap z)).commRingCatIsoToRingEquiv.symm

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]

/-- For a noetherian adic ring `A`, `ofSpf A` has a noetherian underlying topological space. -/
instance noetherianSpace_ofSpf [IsNoetherianRing A] : NoetherianSpace (ofSpf A) :=
  inferInstanceAs (NoetherianSpace (Spf.carrier A))

/-- The formal spectrum of a noetherian adic ring is a noetherian formal scheme. -/
instance [IsNoetherianRing A] : (ofSpf A).IsNoetherian where
  exists_isNoetherianRing x := ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, 𝟙 _, inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A))), x, rfl⟩
  toCompactSpace := Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1

/-- `Spf A` is locally noetherian if and only if `A` is noetherian (EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem isLocallyNoetherian_ofSpf_iff : (ofSpf A).IsLocallyNoetherian ↔ IsNoetherianRing A :=
  ⟨fun _ ↦ isNoetherianRing_of_isOpenImmersion (X := ofSpf A) (𝟙 (Spf A))
    (hf := inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A)))), fun _ ↦ inferInstance⟩

/-- `Spf A` is a noetherian formal scheme if and only if `A` is noetherian
(EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem isNoetherian_ofSpf_iff : (ofSpf A).IsNoetherian ↔ IsNoetherianRing A :=
  ⟨fun _ ↦ (isLocallyNoetherian_ofSpf_iff A).mp inferInstance, fun _ ↦ inferInstance⟩

end Spf

section CoversAndNoetherianSpace

/-- On a locally noetherian formal scheme `X`, the topologized section ring `hU.Sections` over any
affine formal open `U` is a noetherian ring (EGA I, Ch. I, 10.6.5). -/
instance IsAffineOpen.isNoetherianRing_sections [X.IsLocallyNoetherian] {U : Opens X}
    (hU : X.IsAffineOpen U) : IsNoetherianRing hU.Sections :=
  (isLocallyNoetherian_ofSpf_iff hU.Sections).mp
    ((isLocallyNoetherian_iff_of_iso hU.isoSpf).mp inferInstance)

/-- An affine formal open `U` whose section ring `Γ(U, O_X)` is noetherian has a noetherian
underlying topological space. -/
theorem noetherianSpace_of_isAffineOpen (U : Opens X) (hU : X.IsAffineOpen U)
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
theorem IsAffineOpen.noetherianSpace [X.IsLocallyNoetherian] {U : Opens X}
    (hU : X.IsAffineOpen U) : NoetherianSpace U :=
  have := hU.isNoetherianRing
  noetherianSpace_of_isAffineOpen U hU

/-- Given an affine open cover `⨆ i, U i = ⊤` of `X`, `X` is locally noetherian if and only if
every section ring `Γ(U i, O_X)` is noetherian. -/
theorem isLocallyNoetherian_iff_of_iSup_eq_top {ι : Type*} {U : ι → Opens X}
    (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    X.IsLocallyNoetherian ↔ ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  refine ⟨fun _ i ↦ (hU i).isNoetherianRing, fun hnoeth ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcov ▸ Opens.mem_top x)
  have : IsNoetherianRing (hU i).Sections := hnoeth i
  exact ⟨(hU i).Sections, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, forgetToLocallyRingedSpace.map (hU i).fromSpf, (hU i).isOpenImmersion_fromSpf,
    ((hU i).range_fromSpf).ge hxi⟩

/-- Given a finite affine open cover `⨆ i, U i = ⊤` of `X`, `X` is noetherian if and only if every
section ring `Γ(U i, O_X)` is noetherian. -/
theorem isNoetherian_iff_of_finite_iSup_eq_top {ι : Type*} [Finite ι] {U : ι → Opens X}
    (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    X.IsNoetherian ↔ ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  have huniv : (Set.univ : Set X) = ⋃ i, (U i : Set X) :=
    Set.ext fun x ↦ by simp [← Opens.mem_iSup, hcov]
  have hc : CompactSpace X :=
    isCompact_univ_iff.mp (huniv ▸ isCompact_iUnion fun i ↦ (hU i).isCompact)
  exact ⟨fun h ↦ (isLocallyNoetherian_iff_of_iSup_eq_top hU hcov).mp h.toIsLocallyNoetherian,
    fun h ↦ { toIsLocallyNoetherian := (isLocallyNoetherian_iff_of_iSup_eq_top hU hcov).mpr h
              toCompactSpace := hc }⟩

/-- A formal scheme is noetherian if and only if it admits a finite affine open cover with
noetherian section rings. -/
theorem isNoetherian_iff_exists_finite_affine_cover_isNoetherianRing :
    X.IsNoetherian ↔
      ∃ (n : ℕ) (U : Fin n → Opens X), (∀ i, X.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ ∧
        ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨n, U, hU, hcov⟩ := X.exists_finite_affine_cover
    exact ⟨n, U, hU, hcov, (isNoetherian_iff_of_finite_iSup_eq_top hU hcov).mp inferInstance⟩
  · rintro ⟨n, U, hU, hcov, hnoeth⟩
    exact (isNoetherian_iff_of_finite_iSup_eq_top hU hcov).mpr hnoeth

/-- Every noetherian formal scheme has a noetherian underlying topological space. -/
instance IsNoetherian.noetherianSpace [X.IsNoetherian] : NoetherianSpace X := by
  obtain ⟨n, U, hU, hcov⟩ := X.exists_finite_affine_cover
  have huniv : (⋃ i, (U i : Set X)) = Set.univ :=
    Set.ext fun x ↦ by simp [← Opens.mem_iSup, hcov]
  have (i : Fin n) : NoetherianSpace (U i : Set X) := (hU i).noetherianSpace
  exact TopologicalSpace.noetherian_univ_iff.mp
    (huniv ▸ TopologicalSpace.NoetherianSpace.iUnion fun i ↦ (U i : Set X))

/-- A locally noetherian formal scheme with noetherian underlying space is noetherian. -/
theorem isNoetherian_of_noetherianSpace [X.IsLocallyNoetherian] [NoetherianSpace X] :
    X.IsNoetherian :=
  have : CompactSpace X := TopologicalSpace.NoetherianSpace.compactSpace X
  ⟨⟩

end CoversAndNoetherianSpace

section Scheme

/-! `X.toFormalScheme` has the locally ringed space of `X` as its underlying locally ringed space
(`Scheme.toFormalScheme_toLocallyRingedSpace`, which holds by `rfl`). So the points, opens, rings of
sections and compactness of `X` are used directly as those of `X.toFormalScheme` below. -/

/-- An ordinary scheme is a locally noetherian formal scheme if and only if it is a locally
noetherian scheme (EGA I, Ch. I, 10.4.2). -/
@[simp]
theorem isLocallyNoetherian_toFormalScheme_iff (X : Scheme.{u}) :
    X.toFormalScheme.IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian X := by
  refine ⟨fun _ ↦ ⟨fun U ↦ U.property.isAffineOpen_toFormalScheme.isNoetherianRing⟩,
    fun _ ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  obtain ⟨B, _, _, _, _, f, hf, hrange⟩ :=
    (isAffineOpen_def X.toFormalScheme U).mp hU.isAffineOpen_toFormalScheme
  -- the sections of `X.toFormalScheme` over `U` are `Γ(X, U)`, a noetherian ring
  have : IsNoetherianRing (X.toFormalScheme.presheaf.obj (op U)) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    (isNoetherianRing_sections_iff f hrange).mp this, f, hf, hrange ▸ hxU⟩

/-- A locally noetherian scheme is a locally noetherian formal scheme. -/
instance (X : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] :
    X.toFormalScheme.IsLocallyNoetherian :=
  (isLocallyNoetherian_toFormalScheme_iff X).mpr ‹_›

/-- An ordinary scheme is a noetherian formal scheme if and only if it is a noetherian scheme. -/
@[simp]
theorem isNoetherian_toFormalScheme_iff (X : Scheme.{u}) :
    X.toFormalScheme.IsNoetherian ↔ AlgebraicGeometry.IsNoetherian X :=
  ⟨fun h ↦
    { toIsLocallyNoetherian :=
        (isLocallyNoetherian_toFormalScheme_iff X).mp h.toIsLocallyNoetherian
      toCompactSpace := h.toCompactSpace },
   fun h ↦
    { toIsLocallyNoetherian :=
        (isLocallyNoetherian_toFormalScheme_iff X).mpr h.toIsLocallyNoetherian
      toCompactSpace := h.toCompactSpace }⟩

/-- A noetherian scheme is a noetherian formal scheme. -/
instance (X : Scheme.{u}) [AlgebraicGeometry.IsNoetherian X] : X.toFormalScheme.IsNoetherian :=
  (isNoetherian_toFormalScheme_iff X).mpr ‹_›

end Scheme

end TauCeti.FormalScheme
