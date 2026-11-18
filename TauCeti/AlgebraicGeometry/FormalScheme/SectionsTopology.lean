/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import TauCeti.AlgebraicGeometry.FormalScheme.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Morphism
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.SectionsTopology
public import TauCeti.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import TauCeti.RingTheory.Finiteness.Ideal
import TauCeti.Topology.Algebra.Ring.Basic
import TauCeti.Topology.Discrete

/-!
# The intrinsic topology on sections over affine formal opens

For an affine formal open `U` of a formal scheme `X`, the ring of sections `Γ(U, O_X)` carries a
canonical adic topology recovered from the locally ringed space `(U, O_X|_U)` without storing a
chart in the data of `X` (EGA I, Ch. I, 10.4.2): it is the `J`-adic topology for any finitely
generated ideal `J ⊆ Γ(U, O_X)` whose radical is the ideal `X.vanishingIdeal U`
(`AlgebraicGeometry.LocallyRingedSpace.vanishingIdeal`) of sections vanishing in every residue field
on `U`.

With this topology (bundled as a type synonym on `TauCeti.FormalScheme.IsAffineOpen.Sections`),
`Γ(U, O_X)` is a complete separated adic ring of finite ideal type, and the open restriction
`X.restrict U` is canonically isomorphic to `ofSpf hU.Sections` via
`TauCeti.FormalScheme.IsAffineOpen.isoSpf`. On a formal spectrum `ofSpf A` this recovers the
inverse-limit section topology `TauCeti.FormalScheme.Spf.sectionsTopology` on `⊤`, while on any
ordinary scheme `ofScheme.obj Y` every affine formal open carries the discrete section topology and
is an affine scheme open of `Y`.

## Main definitions

* `TauCeti.FormalScheme.sectionsTopology`: the intrinsic adic topology on `Γ(U, O_X)` for an
  affine formal open `U`.
* `TauCeti.FormalScheme.IsAffineOpen.Sections`: type synonym for `Γ(U, O_X)` carrying
  `X.sectionsTopology U hU` and its `IsTopologicalRing` and `IsAdicRing` instances.
* `TauCeti.FormalScheme.IsAffineOpen.isoSpf`, `TauCeti.FormalScheme.IsAffineOpen.fromSpf`: the
  canonical isomorphism `X.restrict U ≅ ofSpf hU.Sections` and open immersion
  `ofSpf hU.Sections ⟶ X`.

## Main results

* `TauCeti.FormalScheme.sectionsTopology_eq_adic`: `X.sectionsTopology U hU` equals `J.adicTopology`
  for every finitely generated ideal `J` with `J.radical = X.vanishingIdeal U`.
* `TauCeti.FormalScheme.sectionsTopology_isTopologicalRing`,
  `TauCeti.FormalScheme.sectionsTopology_isAdicRing`: equipped with `X.sectionsTopology U hU`,
  `Γ(U, O_X)` is a topological ring and an `IsAdicRing`.
* `TauCeti.FormalScheme.isHomeomorph_sectionsTopology_of_isAdic`,
  `TauCeti.FormalScheme.isHomeomorph_sectionsTopology_of_comap_vanishingIdeal`: general criteria
  identifying `sectionsTopology` along ring equivalences into adic rings or between affine opens.
* `TauCeti.FormalScheme.sectionsTopology_ofSpf_top`,
  `TauCeti.FormalScheme.isHomeomorph_ofSpfGlobalSectionsIso`: on `ofSpf A`, the intrinsic global
  section topology agrees with `Spf.sectionsTopology` and makes `ofSpfGlobalSectionsIso A` a
  homeomorphism onto `A`.
* `AlgebraicGeometry.Scheme.sectionsTopology_toFormalScheme_eq_bot`,
  `AlgebraicGeometry.Scheme.isAffineOpen_toFormalScheme_iff`: on `Y.toFormalScheme`, every affine
  formal open has discrete section topology, and the affine formal opens of `Y.toFormalScheme` are
  precisely the affine scheme opens of `Y`.
* `TauCeti.FormalScheme.isHomeomorph_globalSections_of_iso`,
  `TauCeti.FormalScheme.exists_ofSpf_iso_toFormalScheme_iff`: `sectionsTopology` on global sections
  is invariant under isomorphisms of affine formal schemes, and `ofSpf A` lies in the essential
  image of `Scheme.toFormalScheme` (`ofScheme`) if and only if `A` carries the discrete topology.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.1.3, 10.4.2,
  10.4.8.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

section VanishingIdeal

/-- Evaluating the restricted global section corresponding to `s ∈ Γ(U, O_X)` at `x ∈ X.restrict U`
vanishes if and only if evaluating `s` at `x` on `X` vanishes. -/
theorem Γevaluation_restrictTopSectionsIso_inv_eq_zero_iff (X : FormalScheme) (U : Opens X)
    (x : X.restrict U) (s : X.presheaf.obj (op U)) :
    (X.restrict U).toLocallyRingedSpace.Γevaluation x ((restrictTopSectionsIso X U).inv s) = 0 ↔
      X.toLocallyRingedSpace.evaluation ⟨x.1, x.2⟩ s = 0 := by
  rw [restrictTopSectionsIso_inv]
  exact LocallyRingedSpace.Γevaluation_restrict_eq_zero_iff X.toLocallyRingedSpace U x s

/-- An isomorphism `e : X ≅ Y` of formal schemes pulls `X.vanishingIdeal ⊤` back to
`Y.vanishingIdeal ⊤` along `globalSectionsIsoOfIso e`. -/
theorem comap_vanishingIdeal_top_globalSectionsIsoOfIso_hom {X Y : FormalScheme} (e : X ≅ Y) :
    (X.vanishingIdeal ⊤).comap (globalSectionsIsoOfIso e).hom.hom = Y.vanishingIdeal ⊤ := by
  rw [globalSectionsIsoOfIso_hom]
  exact LocallyRingedSpace.comap_vanishingIdeal_top_of_iso (forgetToLocallyRingedSpace.mapIso e)

/-- Under `restrictTopSectionsIso`, the vanishing ideal on `U` corresponds to the global vanishing
ideal on `X.restrict U`. -/
theorem comap_vanishingIdeal_restrictTopSectionsIso_hom (X : FormalScheme) (U : Opens X) :
    (X.vanishingIdeal U).comap (restrictTopSectionsIso X U).hom.hom =
      (X.restrict U).vanishingIdeal ⊤ := by
  rw [restrictTopSectionsIso_hom]
  exact LocallyRingedSpace.comap_vanishingIdeal_restrict_top X.toLocallyRingedSpace U

/-- On `ofSpf A`, the preimage of `vanishingIdeal ⊤` along `(ofSpfGlobalSectionsIso A).inv` is the
radical of every ideal of definition. -/
theorem comap_vanishingIdeal_ofSpf_ofSpfGlobalSectionsIso_inv {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] {I : Ideal A} (hI : IsAdic I) :
    ((ofSpf A).vanishingIdeal ⊤).comap (ofSpfGlobalSectionsIso A).inv.hom = I.radical := by
  have := (IsAdicRing.ideal_spec A).2.2
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I, ← Spf.carrier_eq_zeroLocus hI]
  ext a
  rw [Ideal.mem_comap, LocallyRingedSpace.mem_vanishingIdeal_top, PrimeSpectrum.mem_vanishingIdeal,
    ofSpfGlobalSectionsIso_inv]
  exact ⟨fun h p hp ↦ (Spf.Γevaluation_globalSectionsIso_inv_eq_zero_iff ⟨p, hp⟩ a).mp (h ⟨p, hp⟩),
    fun h p ↦ (Spf.Γevaluation_globalSectionsIso_inv_eq_zero_iff p a).mpr (h p.1 p.2)⟩

end VanishingIdeal

section SectionsTopology

/-- Bundled presentation of an affine formal open `U` of `X` as an isomorphism `X|_U ≅ Spf A`. -/
private structure ChartData (X : FormalScheme) (U : Opens X) where
  carrier : Type u
  [commRing : CommRing carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalRing : IsTopologicalRing carrier]
  [isAdicRing : IsAdicRing carrier]
  iso : (X.restrict U).toLocallyRingedSpace ≅ Spf carrier

attribute [instance] ChartData.commRing ChartData.topologicalSpace
  ChartData.isTopologicalRing ChartData.isAdicRing

private noncomputable def IsAffineOpen.chartData {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) : ChartData X U :=
  Classical.choice <| by
    obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := (isAffineOpen_iff X U).mp hU
    exact ⟨⟨A, e⟩⟩

/-- Given an affine chart `e : X|_U ≅ Spf A`, the induced ring isomorphism `Γ(U, O_X) ≅ A`. -/
private noncomputable def chartSectionsIso {X : FormalScheme} {U : Opens X} {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : (X.restrict U).toLocallyRingedSpace ≅ Spf A) :
    X.presheaf.obj (op U) ≅ CommRingCat.of A :=
  (restrictTopSectionsIso X U).symm ≪≫
    (LocallyRingedSpace.Γ.mapIso e.symm.op :
      (X.restrict U).presheaf.obj (op ⊤) ≅ (ofSpf A).presheaf.obj (op ⊤)) ≪≫
    ofSpfGlobalSectionsIso A

/-- Pulling back an ideal of definition of `A` along a chart isomorphism `X|_U ≅ Spf A` produces an
ideal of `Γ(U, O_X)` whose radical is `X.vanishingIdeal U`. -/
private theorem radical_comap_chartSectionsIso {X : FormalScheme} {U : Opens X} {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : (X.restrict U).toLocallyRingedSpace ≅ Spf A) {I : Ideal A} (hI : IsAdic I) :
    (I.comap (chartSectionsIso e).hom.hom).radical = X.vanishingIdeal U := by
  ext s
  have hrad : s ∈ (I.comap (chartSectionsIso e).hom.hom).radical ↔
      (chartSectionsIso e).hom s ∈ I.radical := by
    rw [← Ideal.comap_radical, Ideal.mem_comap]
  rw [hrad, ← comap_vanishingIdeal_ofSpf_ofSpfGlobalSectionsIso_inv hI, Ideal.mem_comap,
    LocallyRingedSpace.mem_vanishingIdeal_top, LocallyRingedSpace.mem_vanishingIdeal]
  have hiso : (ofSpfGlobalSectionsIso A).inv ((chartSectionsIso e).hom s) =
      e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s) :=
    (ofSpfGlobalSectionsIso A).hom_inv_id_apply
      (e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s))
  rw [hiso]
  have hsurj : Function.Surjective e.inv.base :=
    Function.LeftInverse.surjective (LocallyRingedSpace.iso_hom_base_inv_base_apply e)
  have hpt (p : Spf A) :
      (Spf A).Γevaluation p (e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s)) = 0 ↔
        X.toLocallyRingedSpace.evaluation ⟨(e.inv.base p).1, (e.inv.base p).2⟩ s = 0 := by
    rw [← LocallyRingedSpace.Γevaluation_naturality_apply e.inv p,
      LocallyRingedSpace.residueFieldMap_eq_zero_iff]
    let q : X.restrict U := e.inv.base p
    exact Γevaluation_restrictTopSectionsIso_inv_eq_zero_iff X U q s
  exact ⟨fun h x ↦ by
      let x' : (X.restrict U).toLocallyRingedSpace := x
      obtain ⟨p, hp⟩ := hsurj x'
      have hpx : (⟨(e.inv.base p).1, (e.inv.base p).2⟩ : U) = x :=
        Subtype.ext (congrArg Subtype.val hp)
      exact hpx ▸ (hpt p).mp (h p),
    fun h p ↦ (hpt p).mpr (h ⟨(e.inv.base p).1, (e.inv.base p).2⟩)⟩

/-- Any chart `e : X|_U ≅ Spf A` induces on `Γ(U, O_X)` the `J`-adic topology for every finitely
generated ideal `J` with `J.radical = X.vanishingIdeal U`. -/
private theorem induced_chartSectionsIso_eq_adic {X : FormalScheme} {U : Opens X} {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
    (e : (X.restrict U).toLocallyRingedSpace ≅ Spf A) {J : Ideal (X.presheaf.obj (op U))}
    (hJfg : J.FG) (hJrad : J.radical = X.vanishingIdeal U) :
    TopologicalSpace.induced ((chartSectionsIso e).commRingCatIsoToRingEquiv)
        ‹TopologicalSpace A› = J.adicTopology := by
  let φ := (chartSectionsIso e).commRingCatIsoToRingEquiv
  let I := IsAdicRing.ideal A
  have hIfg : I.FG := (IsAdicRing.ideal_spec A).1
  have hI : IsAdic I := (IsAdicRing.ideal_spec A).2.1
  let tR : TopologicalSpace (X.presheaf.obj (op U)) :=
    TopologicalSpace.induced φ ‹TopologicalSpace A›
  have hadic : @IsAdic (X.presheaf.obj (op U)) _ tR (I.comap φ) :=
    IsAdic.comap hI φ ⟨rfl⟩
  have hKfg : (I.comap φ).FG := hIfg.comap_of_equiv φ
  have hKrad : (I.comap φ).radical = J.radical :=
    (radical_comap_chartSectionsIso e hI).trans hJrad.symm
  exact hadic.trans (Ideal.adicTopology_eq_of_radical_eq hKfg hJfg hKrad)

/-- The intrinsic adic topology on `Γ(U, O_X)` for an affine formal open `U` of `X`
(EGA I, Ch. I, 10.4.2). By `sectionsTopology_eq_adic`, it depends only on `(U, O_X|_U)` and equals
`J.adicTopology` for any finitely generated ideal `J` with `J.radical = X.vanishingIdeal U`. -/
@[instance_reducible]
noncomputable def sectionsTopology (X : FormalScheme) (U : Opens X) (hU : X.IsAffineOpen U) :
    TopologicalSpace (X.presheaf.obj (op U)) :=
  TopologicalSpace.induced ((chartSectionsIso hU.chartData.iso).commRingCatIsoToRingEquiv)
    inferInstance

/-- On an affine formal open `U`, `X.sectionsTopology U hU` agrees with `J.adicTopology` for every
finitely generated ideal `J ⊆ Γ(U, O_X)` whose radical is `X.vanishingIdeal U`. -/
theorem sectionsTopology_eq_adic (X : FormalScheme) (U : Opens X) (hU : X.IsAffineOpen U)
    {J : Ideal (X.presheaf.obj (op U))} (hJfg : J.FG)
    (hJrad : J.radical = X.vanishingIdeal U) :
    X.sectionsTopology U hU = J.adicTopology :=
  induced_chartSectionsIso_eq_adic hU.chartData.iso hJfg hJrad

/-- If `φ : Γ(U, O_X) ≃+* R` pulls back a finitely generated ideal of definition `I` of `R` to an
ideal with radical `X.vanishingIdeal U`, then `X.sectionsTopology U hU` is induced by `φ`. -/
theorem sectionsTopology_eq_induced_of_isAdic {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) {R : Type*} [CommRing R] [TopologicalSpace R]
    (φ : X.presheaf.obj (op U) ≃+* R) {I : Ideal R} (hIfg : I.FG) (hI : IsAdic I)
    (hrad : (I.comap φ).radical = X.vanishingIdeal U) :
    X.sectionsTopology U hU = TopologicalSpace.induced φ ‹TopologicalSpace R› := by
  let tU : TopologicalSpace (X.presheaf.obj (op U)) :=
    TopologicalSpace.induced φ ‹TopologicalSpace R›
  have hadic : @IsAdic _ _ tU (I.comap φ) := IsAdic.comap hI φ ⟨rfl⟩
  rw [X.sectionsTopology_eq_adic U hU (hIfg.comap_of_equiv φ) hrad]
  exact hadic.symm

/-- If `φ : Γ(U, O_X) ≃+* R` pulls back a finitely generated ideal of definition `I` of `R` to an
ideal with radical `X.vanishingIdeal U`, then `φ` is a homeomorphism from `(Γ(U, O_X),
sectionsTopology)` onto `R`. -/
theorem isHomeomorph_sectionsTopology_of_isAdic {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) {R : Type*} [CommRing R] [TopologicalSpace R]
    (φ : X.presheaf.obj (op U) ≃+* R) {I : Ideal R} (hIfg : I.FG) (hI : IsAdic I)
    (hrad : (I.comap φ).radical = X.vanishingIdeal U) :
    @IsHomeomorph _ _ (X.sectionsTopology U hU) ‹TopologicalSpace R› φ := by
  have htop := sectionsTopology_eq_induced_of_isAdic hU φ hIfg hI hrad
  let := X.sectionsTopology U hU
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- Every affine chart `e : X|_U ≅ Spf A` induces `X.sectionsTopology U hU` on `Γ(U, O_X)`. -/
private theorem sectionsTopology_eq_induced_chart {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] (e : (X.restrict U).toLocallyRingedSpace ≅ Spf A) :
    X.sectionsTopology U hU =
      TopologicalSpace.induced ((chartSectionsIso e).commRingCatIsoToRingEquiv)
        ‹TopologicalSpace A› :=
  sectionsTopology_eq_induced_of_isAdic hU (chartSectionsIso e).commRingCatIsoToRingEquiv
    (IsAdicRing.ideal_spec A).1 (IsAdicRing.ideal_spec A).2.1
    (radical_comap_chartSectionsIso e (IsAdicRing.ideal_spec A).2.1)

/-- Every affine formal open `U` admits a finitely generated ideal `J ⊆ Γ(U, O_X)` with
`J.radical = X.vanishingIdeal U`. -/
theorem exists_fg_radical_eq_vanishingIdeal (X : FormalScheme) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    ∃ J : Ideal (X.presheaf.obj (op U)), J.FG ∧ J.radical = X.vanishingIdeal U := by
  let c := hU.chartData
  let φ := (chartSectionsIso c.iso).commRingCatIsoToRingEquiv
  exact ⟨(IsAdicRing.ideal c.carrier).comap φ,
    (IsAdicRing.ideal_spec c.carrier).1.comap_of_equiv φ,
    radical_comap_chartSectionsIso c.iso (IsAdicRing.ideal_spec c.carrier).2.1⟩

/-- Any ring equivalence `φ : Γ(V, O_Y) ≃+* Γ(U, O_X)` between sections over affine formal opens
that pulls `X.vanishingIdeal U` back to `Y.vanishingIdeal V` induces `Y.sectionsTopology V hV` from
`X.sectionsTopology U hU`. -/
theorem sectionsTopology_eq_induced_of_comap_vanishingIdeal {X Y : FormalScheme}
    {U : Opens X} {V : Opens Y} (hU : X.IsAffineOpen U) (hV : Y.IsAffineOpen V)
    (φ : Y.presheaf.obj (op V) ≃+* X.presheaf.obj (op U))
    (hvan : (X.vanishingIdeal U).comap φ = Y.vanishingIdeal V) :
    Y.sectionsTopology V hV = TopologicalSpace.induced φ (X.sectionsTopology U hU) := by
  obtain ⟨J, hJfg, hJrad⟩ := X.exists_fg_radical_eq_vanishingIdeal U hU
  let tU : TopologicalSpace (X.presheaf.obj (op U)) := X.sectionsTopology U hU
  have hJadic : @IsAdic _ _ tU J := X.sectionsTopology_eq_adic U hU hJfg hJrad
  have hKrad : (J.comap φ).radical = Y.vanishingIdeal V := by
    rw [← Ideal.comap_radical, hJrad, hvan]
  exact sectionsTopology_eq_induced_of_isAdic hV φ hJfg hJadic hKrad

/-- Any ring equivalence `φ : Γ(V, O_Y) ≃+* Γ(U, O_X)` between sections over affine formal opens
that pulls `X.vanishingIdeal U` back to `Y.vanishingIdeal V` is a homeomorphism for
`sectionsTopology`. -/
theorem isHomeomorph_sectionsTopology_of_comap_vanishingIdeal {X Y : FormalScheme}
    {U : Opens X} {V : Opens Y} (hU : X.IsAffineOpen U) (hV : Y.IsAffineOpen V)
    (φ : Y.presheaf.obj (op V) ≃+* X.presheaf.obj (op U))
    (hvan : (X.vanishingIdeal U).comap φ = Y.vanishingIdeal V) :
    @IsHomeomorph _ _ (Y.sectionsTopology V hV) (X.sectionsTopology U hU) φ := by
  have htop := sectionsTopology_eq_induced_of_comap_vanishingIdeal hU hV φ hvan
  let := Y.sectionsTopology V hV
  let := X.sectionsTopology U hU
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- Equipped with `X.sectionsTopology U hU`, `Γ(U, O_X)` is a topological ring. -/
theorem sectionsTopology_isTopologicalRing (X : FormalScheme) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (X.sectionsTopology U hU) _ :=
  TauCeti.isTopologicalRing_induced (chartSectionsIso hU.chartData.iso).commRingCatIsoToRingEquiv

/-- Equipped with `X.sectionsTopology U hU`, `Γ(U, O_X)` is a complete separated adic ring of
finite ideal type. -/
theorem sectionsTopology_isAdicRing (X : FormalScheme) (U : Opens X) (hU : X.IsAffineOpen U) :
    letI := X.sectionsTopology U hU
    haveI := X.sectionsTopology_isTopologicalRing U hU
    IsAdicRing (X.presheaf.obj (op U)) := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  exact IsAdicRing.of_isInducing_ringEquiv
    (chartSectionsIso hU.chartData.iso).commRingCatIsoToRingEquiv
    ⟨sectionsTopology_eq_induced_chart hU hU.chartData.iso⟩

/-- On the empty open `⊥`, `sectionsTopology` is the discrete topology `⊥`. -/
@[simp]
theorem sectionsTopology_bot (X : FormalScheme) (h : X.IsAffineOpen ⊥) :
    X.sectionsTopology ⊥ h = ⊥ := by
  have hsub : Subsingleton (X.presheaf.obj (op (⊥ : Opens X))) := inferInstance
  let := X.sectionsTopology ⊥ h
  exact (@Subsingleton.discreteTopology _ _ hsub).eq_bot

end SectionsTopology

section IsoSpf

/-- The ring of sections `Γ(U, O_X)` over an affine formal open `U` of `X`, equipped as a
1-field wrapper with `X.sectionsTopology U hU` and its `IsTopologicalRing` and `IsAdicRing`
instances. -/
@[ext]
structure IsAffineOpen.Sections {X : FormalScheme} {U : Opens X} (_ : X.IsAffineOpen U) :
    Type u where
  /-- The underlying section in `Γ(U, O_X)`. -/
  val : X.presheaf.obj (op U)

namespace IsAffineOpen

/-- Equivalence between `hU.Sections` and `Γ(U, O_X)`. -/
def sectionsEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.Sections ≃ X.presheaf.obj (op U) where
  toFun := Sections.val
  invFun := Sections.mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem sectionsEquiv_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : hU.Sections) : hU.sectionsEquiv s = s.val :=
  (rfl)

@[simp]
theorem sectionsEquiv_symm_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : X.presheaf.obj (op U)) : hU.sectionsEquiv.symm s = ⟨s⟩ :=
  (rfl)

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    CommRing hU.Sections :=
  hU.sectionsEquiv.commRing

namespace Sections

variable {X : FormalScheme} {U : Opens X} {hU : X.IsAffineOpen U}

@[simp] theorem val_zero : (0 : hU.Sections).val = 0 := (rfl)

@[simp] theorem val_one : (1 : hU.Sections).val = 1 := (rfl)

@[simp] theorem val_add (a b : hU.Sections) : (a + b).val = a.val + b.val := (rfl)

@[simp] theorem val_mul (a b : hU.Sections) : (a * b).val = a.val * b.val := (rfl)

@[simp] theorem val_neg (a : hU.Sections) : (-a).val = -a.val := (rfl)

@[simp] theorem val_sub (a b : hU.Sections) : (a - b).val = a.val - b.val := (rfl)

@[simp] theorem val_pow (a : hU.Sections) (n : ℕ) : (a ^ n).val = a.val ^ n := (rfl)

@[simp] theorem val_natCast (n : ℕ) : (n : hU.Sections).val = n := (rfl)

@[simp] theorem val_intCast (n : ℤ) : (n : hU.Sections).val = n := (rfl)

end Sections

/-- The underlying ring equivalence between `hU.Sections` and `Γ(U, O_X)`. -/
def sectionsRingEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.Sections ≃+* X.presheaf.obj (op U) :=
  hU.sectionsEquiv.ringEquiv

@[simp]
theorem sectionsRingEquiv_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : hU.Sections) : hU.sectionsRingEquiv s = s.val :=
  (rfl)

@[simp]
theorem sectionsRingEquiv_symm_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : X.presheaf.obj (op U)) : hU.sectionsRingEquiv.symm s = ⟨s⟩ :=
  (rfl)

/-- The `CommRingCat` isomorphism between `hU.Sections` and `Γ(U, O_X)`. -/
def sectionsIso {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    CommRingCat.of hU.Sections ≅ X.presheaf.obj (op U) :=
  hU.sectionsRingEquiv.toCommRingCatIso

-- Keep morphism-level `sectionsIso_hom` and `sectionsIso_inv` explicit so `@[simp]` lemmas such as
-- `isoSpf_inv_globalSections` and `fromSpf_globalSections` remain in simp normal form.
theorem sectionsIso_hom {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.sectionsIso.hom = CommRingCat.ofHom hU.sectionsRingEquiv.toRingHom :=
  (rfl)

theorem sectionsIso_inv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.sectionsIso.inv = CommRingCat.ofHom hU.sectionsRingEquiv.symm.toRingHom :=
  (rfl)

@[simp]
theorem sectionsIso_hom_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : hU.Sections) : hU.sectionsIso.hom s = s.val :=
  (rfl)

@[simp]
theorem sectionsIso_inv_apply {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U)
    (s : X.presheaf.obj (op U)) : hU.sectionsIso.inv s = ⟨s⟩ :=
  (rfl)

noncomputable instance instTopologicalSpaceSections {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) : TopologicalSpace hU.Sections :=
  TopologicalSpace.induced hU.sectionsEquiv (X.sectionsTopology U hU)

/-- The topology on `hU.Sections` is induced along `hU.sectionsEquiv` from
`X.sectionsTopology U hU`. -/
theorem topologicalSpace_sections {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.instTopologicalSpaceSections =
      TopologicalSpace.induced hU.sectionsEquiv (X.sectionsTopology U hU) :=
  (rfl)

/-- `hU.sectionsEquiv` is topologically inducing for `X.sectionsTopology U hU`. -/
theorem isInducing_sectionsEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    @Topology.IsInducing _ _ _ (X.sectionsTopology U hU) hU.sectionsEquiv := by
  let := X.sectionsTopology U hU
  exact ⟨hU.topologicalSpace_sections⟩

/-- `hU.sectionsRingEquiv` is topologically inducing for `X.sectionsTopology U hU`. -/
theorem isInducing_sectionsRingEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    @Topology.IsInducing _ _ _ (X.sectionsTopology U hU) hU.sectionsRingEquiv :=
  hU.isInducing_sectionsEquiv

/-- `hU.sectionsRingEquiv` is a homeomorphism from `hU.Sections` onto `(Γ(U, O_X),
sectionsTopology)`. -/
theorem isHomeomorph_sectionsRingEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    @IsHomeomorph _ _ _ (X.sectionsTopology U hU) hU.sectionsRingEquiv := by
  let := X.sectionsTopology U hU
  exact (hU.sectionsEquiv.toHomeomorphOfIsInducing hU.isInducing_sectionsEquiv).isHomeomorph

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsTopologicalRing hU.Sections := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  exact hU.isInducing_sectionsRingEquiv.isTopologicalRing hU.sectionsRingEquiv

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsAdicRing hU.Sections := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  exact IsAdicRing.of_isInducing_ringEquiv hU.sectionsRingEquiv hU.isInducing_sectionsRingEquiv

private noncomputable def chartRingEquiv {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) : hU.Sections ≃+* hU.chartData.carrier :=
  hU.sectionsRingEquiv.trans (chartSectionsIso hU.chartData.iso).commRingCatIsoToRingEquiv

private theorem isInducing_chartRingEquiv {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    Topology.IsInducing (chartRingEquiv hU) := by
  refine ⟨?_⟩
  rw [hU.topologicalSpace_sections, sectionsTopology_eq_induced_chart hU hU.chartData.iso,
    induced_compose]
  rfl

private theorem continuous_chartRingEquiv {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    Continuous (chartRingEquiv hU).toRingHom :=
  (isInducing_chartRingEquiv hU).continuous

private theorem continuous_chartRingEquiv_symm {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    Continuous (chartRingEquiv hU).symm.toRingHom :=
  ((chartRingEquiv hU).toEquiv.toHomeomorphOfIsInducing
    (isInducing_chartRingEquiv hU)).symm.continuous

private noncomputable def chartSpfIso {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) : Spf hU.chartData.carrier ≅ Spf hU.Sections :=
  { hom := Spf.map (chartRingEquiv hU).toRingHom (continuous_chartRingEquiv hU)
    inv := Spf.map (chartRingEquiv hU).symm.toRingHom (continuous_chartRingEquiv_symm hU)
    hom_inv_id := by
      rw [← Spf.map_comp]
      convert Spf.map_id (A := hU.chartData.carrier)
      exact (chartRingEquiv hU).toRingHom_comp_symm_toRingHom
    inv_hom_id := by
      rw [← Spf.map_comp]
      convert Spf.map_id (A := hU.Sections)
      exact (chartRingEquiv hU).symm_toRingHom_comp_toRingHom }

/-- An affine formal open `U` of `X` is canonically isomorphic as a formal scheme to the formal
spectrum of its topologized section ring `hU.Sections` (EGA I, Ch. I, 10.4.2). -/
noncomputable def isoSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    X.restrict U ≅ ofSpf hU.Sections :=
  InducedCategory.isoMk (hU.chartData.iso ≪≫ chartSpfIso hU)

/-- On global sections, `hU.isoSpf.inv` followed by `ofSpfGlobalSectionsIso` and `hU.sectionsIso`
is the canonical restriction identification `restrictTopSectionsIso X U` (independent of any
chart). -/
@[reassoc (attr := simp)]
theorem isoSpf_inv_globalSections {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    (forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) ≫
        (ofSpfGlobalSectionsIso hU.Sections).hom ≫ hU.sectionsIso.hom =
      (restrictTopSectionsIso X U).hom := by
  have := (IsAdicRing.ideal_spec hU.Sections).2.2
  have := (IsAdicRing.ideal_spec hU.chartData.carrier).2.2
  ext t
  let x : (Spf hU.chartData.carrier).presheaf.obj (op ⊤) := hU.chartData.iso.inv.c.app (op ⊤) t
  have h0 : (ofSpfGlobalSectionsIso hU.Sections).hom
      ((forgetToLocallyRingedSpace.map hU.isoSpf.inv).c.app (op ⊤) t) =
      (chartRingEquiv hU).symm ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom x) := by
    rw [ofSpfGlobalSectionsIso_hom hU.Sections, ofSpfGlobalSectionsIso_hom hU.chartData.carrier]
    exact ConcreteCategory.congr_hom
      (Spf.map_globalSections (chartRingEquiv hU).symm.toRingHom
        (continuous_chartRingEquiv_symm hU)) x
  have h1 := congrArg hU.sectionsIso.hom h0
  have h2 : hU.sectionsIso.hom
      ((chartRingEquiv hU).symm ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom x)) =
      (chartSectionsIso hU.chartData.iso).inv
        ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom x) :=
    hU.sectionsRingEquiv.apply_symm_apply _
  have h3 : (chartSectionsIso hU.chartData.iso).inv
      ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom x) =
      (restrictTopSectionsIso X U).hom t :=
    (congrArg (fun z ↦ (restrictTopSectionsIso X U).hom
        ((LocallyRingedSpace.Γ.mapIso hU.chartData.iso.symm.op).inv z))
      ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom_inv_id_apply x)).trans
      (congrArg (restrictTopSectionsIso X U).hom
        ((LocallyRingedSpace.Γ.mapIso hU.chartData.iso.symm.op).hom_inv_id_apply t))
  exact (h1.trans h2).trans h3

/-- The canonical open immersion `ofSpf hU.Sections ⟶ X` with image `U`. -/
noncomputable def fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    ofSpf hU.Sections ⟶ X :=
  hU.isoSpf.inv ≫ X.ofRestrict U

-- Keep `isoSpf_inv_ofRestrict` explicit so `@[simp]` lemmas on `fromSpf` remain in simp normal
-- form.
theorem isoSpf_inv_ofRestrict {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.isoSpf.inv ≫ X.ofRestrict U = hU.fromSpf :=
  (rfl)

/-- Composing `hU.isoSpf.hom` with `hU.fromSpf` recovers the open inclusion `X.ofRestrict U`. -/
@[reassoc (attr := simp)]
theorem isoSpf_hom_fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.isoSpf.hom ≫ hU.fromSpf = X.ofRestrict U :=
  Iso.hom_inv_id_assoc hU.isoSpf (X.ofRestrict U)

/-- On global sections, `hU.fromSpf` followed by `ofSpfGlobalSectionsIso` and `hU.sectionsIso` is
the presheaf restriction from `⊤` to `U`. -/
@[reassoc (attr := simp)]
theorem fromSpf_globalSections {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    (forgetToLocallyRingedSpace.map hU.fromSpf).c.app (op ⊤) ≫
        (ofSpfGlobalSectionsIso hU.Sections).hom ≫ hU.sectionsIso.hom =
      X.presheaf.map (homOfLE le_top).op := by
  ext s
  have h1 := ConcreteCategory.congr_hom hU.isoSpf_inv_globalSections
    ((forgetToLocallyRingedSpace.map (X.ofRestrict U)).c.app (op ⊤) s)
  have h2 := ConcreteCategory.congr_hom
    (X.ofRestrict_c_app_top_comp_restrictTopSectionsIso_hom U) s
  exact h1.trans h2

instance isOpenImmersion_fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map hU.fromSpf) := by
  rw [← isoSpf_inv_ofRestrict, Functor.map_comp]
  have : IsIso (forgetToLocallyRingedSpace.map hU.isoSpf.inv) :=
    Functor.map_isIso forgetToLocallyRingedSpace hU.isoSpf.inv
  infer_instance

@[simp]
theorem range_fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    Set.range (forgetToLocallyRingedSpace.map hU.fromSpf).base = (U : Set X) := by
  rw [← isoSpf_inv_ofRestrict, Functor.map_comp]
  exact (LocallyRingedSpace.range_iso_inv_comp
    (forgetToLocallyRingedSpace.mapIso hU.isoSpf)
    (forgetToLocallyRingedSpace.map (X.ofRestrict U))).trans (range_ofRestrict X U)

end IsAffineOpen

end IsoSpf

section Comparisons

/-- `restrictTopSectionsIso X U` is a homeomorphism between `(Γ(⊤, O_{X|_U}), sectionsTopology)`
and `(Γ(U, O_X), sectionsTopology)`. -/
theorem isHomeomorph_restrictTopSectionsIso {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    @IsHomeomorph _ _ ((X.restrict U).sectionsTopology ⊤ hU.top_restrict)
      (X.sectionsTopology U hU) ((restrictTopSectionsIso X U).hom) :=
  isHomeomorph_sectionsTopology_of_comap_vanishingIdeal hU hU.top_restrict
    (restrictTopSectionsIso X U).commRingCatIsoToRingEquiv
    (comap_vanishingIdeal_restrictTopSectionsIso_hom X U)

/-- On `ofSpf A`, `ofSpfGlobalSectionsIso A` is a homeomorphism from `(Γ(⊤, O_{ofSpf A}),
sectionsTopology)` onto `A`. -/
theorem isHomeomorph_ofSpfGlobalSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ ((ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A))
      ‹TopologicalSpace A› ((ofSpfGlobalSectionsIso A).hom) := by
  let φ := (ofSpfGlobalSectionsIso A).commRingCatIsoToRingEquiv
  have hrad : ((IsAdicRing.ideal A).comap φ).radical = (ofSpf A).vanishingIdeal ⊤ := by
    rw [← Ideal.comap_radical,
      ← comap_vanishingIdeal_ofSpf_ofSpfGlobalSectionsIso_inv (IsAdicRing.ideal_spec A).2.1]
    ext s
    have hs : (ofSpfGlobalSectionsIso A).inv (φ s) = s :=
      Iso.hom_inv_id_apply (ofSpfGlobalSectionsIso A) s
    simp only [Ideal.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ (ofSpf A).vanishingIdeal ⊤) hs)
  exact isHomeomorph_sectionsTopology_of_isAdic (isAffineOpen_top_ofSpf A) φ
    (IsAdicRing.ideal_spec A).1 (IsAdicRing.ideal_spec A).2.1 hrad

/-- On `ofSpf A`, the intrinsic topology on global sections equals `Spf.sectionsTopology`. -/
@[simp]
theorem sectionsTopology_ofSpf_top (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A) =
      Spf.sectionsTopology (IsAdicRing.ideal_spec A).2.1 ⊤ := by
  have hI := (IsAdicRing.ideal_spec A).2.1
  have := (IsAdicRing.ideal_spec A).2.2
  have h₁ := isHomeomorph_ofSpfGlobalSectionsIso A
  have h₂ := Spf.quotientSectionsTopology_top hI ▸ Spf.isHomeomorph_globalSectionsIso hI
  let t₁ := (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  have eq₁ : t₁ = TopologicalSpace.induced ((ofSpfGlobalSectionsIso A).hom)
      ‹TopologicalSpace A› :=
    h₁.isInducing.eq_induced
  rw [ofSpfGlobalSectionsIso_hom A] at eq₁
  let t₂ := Spf.sectionsTopology hI ⊤
  have eq₂ : t₂ = TopologicalSpace.induced ((Spf.globalSectionsIso hI).hom)
      ‹TopologicalSpace A› :=
    h₂.isInducing.eq_induced
  exact eq₁.trans eq₂.symm

end Comparisons

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- On an ordinary scheme `Y`, every affine formal open of `Y.toFormalScheme` carries the discrete
intrinsic section topology (`⊥`). -/
@[simp]
theorem sectionsTopology_toFormalScheme_eq_bot (Y : Scheme.{u})
    (U : TopologicalSpace.Opens Y.toFormalScheme)
    (hU : Y.toFormalScheme.IsAffineOpen U) :
    Y.toFormalScheme.sectionsTopology U hU = ⊥ := by
  have hrad : (⊥ : Ideal (Y.toFormalScheme.presheaf.obj (op U))).radical =
      Y.toFormalScheme.vanishingIdeal U := by
    ext s
    rw [Ideal.mem_radical_iff, LocallyRingedSpace.mem_vanishingIdeal]
    simp only [Ideal.mem_bot]
    exact (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact (X := Y) (U := U)
      hU.isCompact s).trans (Y.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s)
  rw [Y.toFormalScheme.sectionsTopology_eq_adic U hU Submodule.fg_bot hrad]
  let : TopologicalSpace (Y.toFormalScheme.presheaf.obj (op U)) :=
    (⊥ : Ideal (Y.toFormalScheme.presheaf.obj (op U))).adicTopology
  have : DiscreteTopology (Y.toFormalScheme.presheaf.obj (op U)) := is_bot_adic_iff.mp rfl
  exact DiscreteTopology.eq_bot

/-- On an ordinary scheme `Y`, the section ring over every affine formal open is discrete for
`sectionsTopology`. -/
theorem discreteTopology_sectionsTopology_toFormalScheme (Y : Scheme.{u})
    (U : TopologicalSpace.Opens Y.toFormalScheme) (hU : Y.toFormalScheme.IsAffineOpen U) :
    @DiscreteTopology _ (Y.toFormalScheme.sectionsTopology U hU) :=
  @DiscreteTopology.mk _ (Y.toFormalScheme.sectionsTopology U hU)
    (Y.sectionsTopology_toFormalScheme_eq_bot U hU)

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

instance IsAffineOpen.discreteTopology_sections_toFormalScheme {Y : Scheme.{u}}
    {U : Opens Y.toFormalScheme} (hU : Y.toFormalScheme.IsAffineOpen U) :
    DiscreteTopology hU.Sections := by
  refine ⟨?_⟩
  rw [hU.topologicalSpace_sections, Y.sectionsTopology_toFormalScheme_eq_bot U hU]
  exact TauCeti.induced_bot_of_injective hU.sectionsEquiv.injective

end TauCeti.FormalScheme

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.FormalScheme

/-- An open subset of an ordinary scheme `Y` is an affine formal open of `Y.toFormalScheme` if and
only if it is an affine open of `Y` as a scheme. -/
@[simp]
theorem isAffineOpen_toFormalScheme_iff (Y : Scheme.{u}) (U : Y.Opens) :
    Y.toFormalScheme.IsAffineOpen U ↔ AlgebraicGeometry.IsAffineOpen U := by
  constructor
  · intro hU
    let U' : TopologicalSpace.Opens Y.toFormalScheme := U
    have hU' : Y.toFormalScheme.IsAffineOpen U' := hU
    let eLRS : U.toScheme.toLocallyRingedSpace ≅
        (Spec (CommRingCat.of hU'.Sections)).toLocallyRingedSpace :=
      FormalScheme.forgetToLocallyRingedSpace.mapIso hU'.isoSpf ≪≫ Spf.discreteIsoSpec hU'.Sections
    let e : U.toScheme ≅ Spec (CommRingCat.of hU'.Sections) :=
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso eLRS
    exact AlgebraicGeometry.IsAffine.of_isIso e.hom
  · intro hU
    let R := (Y.presheaf.obj (op U) : Type u)
    let : TopologicalSpace R := ⊥
    have : DiscreteTopology R := ⟨rfl⟩
    exact (isAffineOpen_iff Y.toFormalScheme U).mpr
      ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
        ⟨Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec ≪≫ (Spf.discreteIsoSpec R).symm⟩⟩

end AlgebraicGeometry.Scheme

namespace TauCeti.FormalScheme

/-- For an isomorphism `e : X ≅ Y` between affine formal schemes, the induced global-sections map
`Γ(Y, O_Y) → Γ(X, O_X)` is a homeomorphism for `sectionsTopology`. -/
theorem isHomeomorph_globalSections_of_iso {X Y : FormalScheme} (e : X ≅ Y)
    (hX : X.IsAffineOpen ⊤) (hY : Y.IsAffineOpen ⊤) :
    @IsHomeomorph _ _ (Y.sectionsTopology ⊤ hY) (X.sectionsTopology ⊤ hX)
      (globalSectionsIsoOfIso e).hom :=
  isHomeomorph_sectionsTopology_of_comap_vanishingIdeal hX hY
    (globalSectionsIsoOfIso e).commRingCatIsoToRingEquiv
    (comap_vanishingIdeal_top_globalSectionsIsoOfIso_hom e)

/-- If an affine formal scheme `ofSpf A` is isomorphic in `FormalScheme` to `Y.toFormalScheme` for
an ordinary scheme `Y`, then `A` carries the discrete topology. -/
theorem discreteTopology_of_ofSpf_iso_toFormalScheme {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] {Y : Scheme.{u}} (e : ofSpf A ≅ Y.toFormalScheme) :
    DiscreteTopology A := by
  have hA : (ofSpf A).IsAffineOpen ⊤ := isAffineOpen_top_ofSpf A
  have hY : Y.toFormalScheme.IsAffineOpen ⊤ := isAffineOpen_top_of_iso e hA
  let := (ofSpf A).sectionsTopology ⊤ hA
  let := Y.toFormalScheme.sectionsTopology ⊤ hY
  have hdY : DiscreteTopology (Y.toFormalScheme.presheaf.obj (op ⊤)) :=
    Y.discreteTopology_sectionsTopology_toFormalScheme ⊤ hY
  have hdA : DiscreteTopology ((ofSpf A).presheaf.obj (op ⊤)) :=
    (isHomeomorph_globalSections_of_iso e hA hY).homeomorph.discreteTopology_iff.mp hdY
  exact (isHomeomorph_ofSpfGlobalSectionsIso A).homeomorph.discreteTopology_iff.mp hdA

/-- An affine formal scheme `ofSpf A` lies in the essential image of `Scheme.toFormalScheme`
(`ofScheme`) if and only if `A` carries the discrete topology. -/
@[simp]
theorem exists_ofSpf_iso_toFormalScheme_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (∃ Y : Scheme.{u}, Nonempty (ofSpf A ≅ Y.toFormalScheme)) ↔ DiscreteTopology A :=
  ⟨fun ⟨_, ⟨e⟩⟩ ↦ discreteTopology_of_ofSpf_iso_toFormalScheme e,
    fun _ ↦ ⟨Spec (CommRingCat.of A), ⟨(ofSchemeSpecIso A).symm⟩⟩⟩

end TauCeti.FormalScheme
