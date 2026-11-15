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

import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.AdicCompletion.Topology
import TauCeti.Topology.Discrete

/-!
# The intrinsic topology on sections over affine formal opens

For an affine formal open `U` of a formal scheme `X`, the ring of sections `Γ(U, O_X)` carries a
canonical adic topology recovered from the locally ringed space `(U, O_X|_U)` without storing a
chart in the data of `X` (EGA I, Ch. I, 10.4.2): it is the `J`-adic topology for any finitely
generated ideal `J ⊆ Γ(U, O_X)` whose radical is the ideal `X.vanishingIdeal U` of sections
vanishing in every residue field on `U`.

With this topology (bundled as a type synonym on `TauCeti.FormalScheme.IsAffineOpen.Sections`),
`Γ(U, O_X)` is a complete separated adic ring of finite ideal type, and the open restriction
`X.restrict U` is canonically isomorphic to `ofSpf hU.Sections` via
`TauCeti.FormalScheme.IsAffineOpen.isoSpf`. On a formal spectrum `ofSpf A` this recovers the
inverse-limit section topology `TauCeti.FormalScheme.Spf.sectionsTopology` on `⊤`, while on any
ordinary scheme `ofScheme.obj Y` every affine formal open carries the discrete section topology and
is an affine scheme open of `Y`.

## Main definitions

* `TauCeti.FormalScheme.restrictTopSectionsIso`: identification of `Γ(⊤, O_{X|_U})` with
  `Γ(U, O_X)`.
* `TauCeti.FormalScheme.ofSpfGlobalSectionsIso`: identification of `Γ(⊤, O_{ofSpf A})` with `A`.
* `TauCeti.FormalScheme.vanishingIdeal`: the radical ideal in `Γ(U, O_X)` of sections vanishing in
  the residue field at every point of `U`.
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
* `TauCeti.FormalScheme.sectionsTopology_ofSpf_top`,
  `TauCeti.FormalScheme.isHomeomorph_ofSpfGlobalSectionsIso`: on `ofSpf A`, the intrinsic global
  section topology agrees with `Spf.sectionsTopology` and makes `ofSpfGlobalSectionsIso A` a
  homeomorphism onto `A`.
* `TauCeti.FormalScheme.sectionsTopology_toFormalScheme_eq_bot`,
  `TauCeti.FormalScheme.isAffineOpen_toFormalScheme_iff`: on `Y.toFormalScheme`, every affine formal
  open has discrete section topology, and the affine formal opens of `Y.toFormalScheme` are
  precisely the affine scheme opens of `Y`.
* `TauCeti.FormalScheme.isHomeomorph_globalSections_of_iso`,
  `TauCeti.FormalScheme.exists_iso_toFormalScheme_iff`: `sectionsTopology` on global sections is
  invariant under isomorphisms of affine formal schemes, and `ofSpf A` lies in the essential image
  of `Scheme.toFormalScheme` (`ofScheme`) if and only if `A` carries the discrete topology.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.1.3, 10.4.2,
  10.4.8.
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY).
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TauCeti.FormalScheme

instance (X : FormalScheme) : Subsingleton (X.presheaf.obj (op (⊥ : Opens X))) :=
  CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty

namespace Spf

/-- On `Spf A`, the global section corresponding to `a ∈ A` vanishes in the residue field at an
open prime `p` if and only if `a ∈ p`. -/
theorem Γevaluation_globalSectionsIso_inv_eq_zero_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] (p : carrier A) (a : A) :
    have := (IsAdicRing.ideal_spec A).2.2
    (Spf A).Γevaluation p ((globalSectionsIso (IsAdicRing.ideal_spec A).2.1).inv a) = 0 ↔
      a ∈ (p : PrimeSpectrum A).asIdeal := by
  intro
  have hIfg := (IsAdicRing.ideal_spec A).1
  have hI := (IsAdicRing.ideal_spec A).2.1
  let pLRS : Spf A := p
  let f₁ : BasicNeighbourhood p := ⟨1, p.1.isPrime.one_notMem⟩
  let s := (globalSectionsIso hI).inv a
  have hmor : (globalSectionsIso hI).inv ≫
      (structureSheaf hI).obj.map (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap A (AdicRing.CompletedAway A 1)) ≫
        (basicOpenSectionsIso hI hIfg 1).inv := by
    rw [Iso.eq_comp_inv, Category.assoc]
    exact globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hI hIfg 1
  have hres : (basicOpenSectionsIso hI hIfg 1).inv (algebraMap A (AdicRing.CompletedAway A 1) a) =
      (structureSheaf hI).obj.map (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)).op s := by
    have h := (ConcreteCategory.congr_hom hmor a).symm
    rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  have hgerm : TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj (basicOpen 1) p
      (mem_basicOpen.mpr f₁.notMem)
      ((basicOpenSectionsIso hI hIfg 1).inv (algebraMap A (AdicRing.CompletedAway A 1) a)) =
      TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj ⊤ p trivial s := by
    rw [hres]
    exact TopCat.Presheaf.germ_res_apply (structureSheaf hI).obj
      (homOfLE (le_top : basicOpen (1 : A) ≤ ⊤)) p (mem_basicOpen.mpr f₁.notMem) s
  have heval : stalkResidueFieldEquiv p ((Spf A).Γevaluation pLRS s) =
      algebraMap (A ⧸ (p : PrimeSpectrum A).asIdeal)
        (FractionRing (A ⧸ (p : PrimeSpectrum A).asIdeal)) (Ideal.Quotient.mk _ a) := by
    -- Unfold `Γevaluation` on `Spf A` to `(Spf A).residue` of the germ on `structureSheaf`.
    change stalkResidueFieldEquiv p ((Spf A).residue pLRS
      (TopCat.Presheaf.germ (C := CommRingCat) (structureSheaf hI).obj ⊤ p trivial s)) = _
    rw [← hgerm]
    exact stalkResidueFieldEquiv_residue_germ f₁ a
  rw [← map_eq_zero_iff (stalkResidueFieldEquiv p) (RingEquiv.injective _), heval,
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end Spf

section VanishingIdeal

/-- Sections over `⊤` on the open restriction `X.restrict U` agree with sections of `X` over `U`. -/
noncomputable def restrictTopSectionsIso (X : FormalScheme) (U : Opens X) :
    (X.restrict U).presheaf.obj (op ⊤) ≅ X.presheaf.obj (op U) :=
  X.presheaf.mapIso (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U)))

/-- Global sections of `ofSpf A` are isomorphic to `A`. This wraps `Spf.globalSectionsIso` with
syntactic source `(ofSpf A).presheaf.obj (op ⊤)`. -/
noncomputable def ofSpfGlobalSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).presheaf.obj (op ⊤) ≅ CommRingCat.of A :=
  haveI := (IsAdicRing.ideal_spec A).2.2
  Spf.globalSectionsIso (IsAdicRing.ideal_spec A).2.1

/-- A residue-field map induced by a morphism of locally ringed spaces reflects zero. -/
private theorem residueFieldMap_eq_zero_iff {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
    (a : Y.residueField (f.base x)) :
    LocallyRingedSpace.residueFieldMap f x a = 0 ↔ a = 0 :=
  map_eq_zero_iff (IsLocalRing.ResidueField.map (f.stalkMap x).hom) (RingHom.injective _)

private theorem lrs_Γevaluation_restrictTop_eq_zero_iff (L : LocallyRingedSpace.{u})
    (U : Opens L) (x : L.restrict U.isOpenEmbedding) (s : L.presheaf.obj (op U)) :
    (L.restrict U.isOpenEmbedding).Γevaluation x
        (L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) s) = 0 ↔
      L.evaluation ⟨x.1, x.2⟩ s = 0 := by
  let j : L.restrict U.isOpenEmbedding ⟶ L := L.ofRestrict U.isOpenEmbedding
  have hU : (Opens.map j.base).obj U = (⊤ : Opens (L.restrict U.isOpenEmbedding)) :=
    Opens.inclusion'_map_eq_top U
  have hxU : x ∈ (Opens.map j.base).obj U := x.2
  let sTop := L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) s
  have hmap : L.presheaf.map (eqToHom (congrArg op (Opens.isOpenEmbedding_obj_top U)).symm) ≫
      (L.restrict U.isOpenEmbedding).presheaf.map (homOfLE hU.le).op = j.c.app (op U) := by
    have hjc : j.c.app (op U) = (L.toPresheafedSpace.ofRestrict U.isOpenEmbedding).c.app (op U) :=
      rfl
    rw [hjc, PresheafedSpace.ofRestrict_c_app]
    -- Merge restriction maps of `L.restrict` and `L` on the thin category `(Opens L)ᵒᵖ`.
    erw [← L.presheaf.map_comp]
    exact congrArg L.presheaf.map (Subsingleton.elim _ _)
  have hs : j.c.app (op U) s =
      (L.restrict U.isOpenEmbedding).presheaf.map (homOfLE hU.le).op sTop :=
    (ConcreteCategory.congr_hom hmap s).symm.trans (CommRingCat.comp_apply _ _ s)
  have hgerm : (L.restrict U.isOpenEmbedding).presheaf.germ ((Opens.map j.base).obj U) x hxU
      (j.c.app (op U) s) =
      (L.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial sTop := by
    rw [hs]
    exact TopCat.Presheaf.germ_res_apply (L.restrict U.isOpenEmbedding).presheaf
      (homOfLE hU.le) x hxU sTop
  have heval : (L.restrict U.isOpenEmbedding).evaluation ⟨x, hxU⟩ (j.c.app (op U) s) =
      (L.restrict U.isOpenEmbedding).Γevaluation x sTop := by
    -- Unfold `evaluation` and `Γevaluation` to `(L.restrict _).residue x` applied to the germ.
    change (L.restrict U.isOpenEmbedding).residue x
      ((L.restrict U.isOpenEmbedding).presheaf.germ ((Opens.map j.base).obj U) x hxU
        (j.c.app (op U) s)) =
      (L.restrict U.isOpenEmbedding).residue x
        ((L.restrict U.isOpenEmbedding).presheaf.germ ⊤ x trivial sTop)
    rw [hgerm]
  rw [← heval, ← LocallyRingedSpace.evaluation_naturality_apply j ⟨x, hxU⟩ s,
    residueFieldMap_eq_zero_iff]
  rfl

/-- Evaluating the restricted global section corresponding to `s ∈ Γ(U, O_X)` at `x ∈ X.restrict U`
vanishes if and only if evaluating `s` at `x` on `X` vanishes. -/
theorem Γevaluation_restrictTopSectionsIso_inv_eq_zero_iff (X : FormalScheme) (U : Opens X)
    (x : X.restrict U) (s : X.presheaf.obj (op U)) :
    (X.restrict U).toLocallyRingedSpace.Γevaluation x ((restrictTopSectionsIso X U).inv s) = 0 ↔
      X.toLocallyRingedSpace.evaluation ⟨x.1, x.2⟩ s = 0 :=
  lrs_Γevaluation_restrictTop_eq_zero_iff X.toLocallyRingedSpace U x s

/-- The ideal of sections over `U` vanishing in the residue field at every point of `U`. -/
noncomputable def vanishingIdeal (X : FormalScheme) (U : Opens X) :
    Ideal (X.presheaf.obj (op U)) :=
  ⨅ x : U, RingHom.ker (X.toLocallyRingedSpace.evaluation x).hom

@[simp]
theorem mem_vanishingIdeal {X : FormalScheme} {U : Opens X} {s : X.presheaf.obj (op U)} :
    s ∈ X.vanishingIdeal U ↔ ∀ x : U, X.toLocallyRingedSpace.evaluation x s = 0 := by
  simp [vanishingIdeal, RingHom.mem_ker]

theorem mem_vanishingIdeal_top {X : FormalScheme} {s : X.presheaf.obj (op ⊤)} :
    s ∈ X.vanishingIdeal ⊤ ↔ ∀ x : X, X.toLocallyRingedSpace.Γevaluation x s = 0 := by
  rw [mem_vanishingIdeal]
  exact ⟨fun h x ↦ h ⟨x, trivial⟩, fun h ⟨x, _⟩ ↦ h x⟩

/-- The vanishing ideal on any open is radical, being an intersection of prime ideals. -/
theorem isRadical_vanishingIdeal (X : FormalScheme) (U : Opens X) :
    (X.vanishingIdeal U).IsRadical := by
  intro s hs
  rw [mem_vanishingIdeal]
  intro x
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hs
  exact eq_zero_of_pow_eq_zero (by simpa only [map_pow] using mem_vanishingIdeal.mp hn x)

@[simp]
theorem radical_vanishingIdeal (X : FormalScheme) (U : Opens X) :
    (X.vanishingIdeal U).radical = X.vanishingIdeal U :=
  (X.isRadical_vanishingIdeal U).radical

/-- Under `restrictTopSectionsIso`, the vanishing ideal on `U` corresponds to the global vanishing
ideal on `X.restrict U`. -/
theorem vanishingIdeal_comap_restrictTopSectionsIso_hom (X : FormalScheme) (U : Opens X) :
    (X.vanishingIdeal U).comap (restrictTopSectionsIso X U).hom.hom =
      (X.restrict U).vanishingIdeal ⊤ := by
  ext s
  rw [Ideal.mem_comap, mem_vanishingIdeal, mem_vanishingIdeal_top]
  have hs : (restrictTopSectionsIso X U).inv ((restrictTopSectionsIso X U).hom s) = s :=
    Iso.hom_inv_id_apply (restrictTopSectionsIso X U) s
  exact ⟨fun h x ↦ by
      rw [← hs, Γevaluation_restrictTopSectionsIso_inv_eq_zero_iff]
      exact h ⟨x.1, x.2⟩,
    fun h x ↦ by
      let x' : X.restrict U := x
      exact (Γevaluation_restrictTopSectionsIso_inv_eq_zero_iff X U x' _).mp (hs.symm ▸ h x')⟩

/-- On `ofSpf A`, the preimage of `vanishingIdeal ⊤` along `(ofSpfGlobalSectionsIso A).inv` is the
radical of every ideal of definition. -/
theorem vanishingIdeal_ofSpf_comap_globalSectionsIso_inv {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] {I : Ideal A} (hI : IsAdic I) :
    ((ofSpf A).vanishingIdeal ⊤).comap (ofSpfGlobalSectionsIso A).inv.hom = I.radical := by
  have := (IsAdicRing.ideal_spec A).2.2
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I, ← Spf.carrier_eq_zeroLocus hI]
  ext a
  rw [Ideal.mem_comap, mem_vanishingIdeal_top, PrimeSpectrum.mem_vanishingIdeal]
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
  rw [hrad, ← vanishingIdeal_ofSpf_comap_globalSectionsIso_inv hI, Ideal.mem_comap,
    mem_vanishingIdeal_top, mem_vanishingIdeal]
  have hiso : (ofSpfGlobalSectionsIso A).inv ((chartSectionsIso e).hom s) =
      e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s) := by
    dsimp only [chartSectionsIso, Iso.trans_hom, Iso.symm_hom]
    -- Unfold `LocallyRingedSpace.Γ.mapIso` to `e.inv.c.app (op ⊤)` on elements.
    change (ofSpfGlobalSectionsIso A).inv ((ofSpfGlobalSectionsIso A).hom
      (e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s))) = _
    exact Iso.hom_inv_id_apply (ofSpfGlobalSectionsIso A) _
  rw [hiso]
  have hsurj : Function.Surjective e.inv.base :=
    Function.LeftInverse.surjective (LocallyRingedSpace.iso_hom_base_inv_base_apply e)
  have hpt (p : Spf A) :
      (Spf A).Γevaluation p (e.inv.c.app (op ⊤) ((restrictTopSectionsIso X U).inv s)) = 0 ↔
        X.toLocallyRingedSpace.evaluation ⟨(e.inv.base p).1, (e.inv.base p).2⟩ s = 0 := by
    rw [← LocallyRingedSpace.Γevaluation_naturality_apply e.inv p,
      residueFieldMap_eq_zero_iff e.inv p]
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
  have hKfg : (I.comap φ).FG := by
    rw [← Ideal.map_symm]
    exact hIfg.map φ.symm.toRingHom
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

/-- Every affine chart `e : X|_U ≅ Spf A` induces `X.sectionsTopology U hU` on `Γ(U, O_X)`. -/
private theorem sectionsTopology_eq_induced_chart {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsAdicRing A] (e : (X.restrict U).toLocallyRingedSpace ≅ Spf A) :
    X.sectionsTopology U hU =
      TopologicalSpace.induced ((chartSectionsIso e).commRingCatIsoToRingEquiv)
        ‹TopologicalSpace A› := by
  let φ := (chartSectionsIso e).commRingCatIsoToRingEquiv
  have hKfg : ((IsAdicRing.ideal A).comap φ).FG := by
    rw [← Ideal.map_symm]
    exact (IsAdicRing.ideal_spec A).1.map φ.symm.toRingHom
  have hKrad : ((IsAdicRing.ideal A).comap φ).radical = X.vanishingIdeal U :=
    radical_comap_chartSectionsIso e (IsAdicRing.ideal_spec A).2.1
  exact (X.sectionsTopology_eq_adic U hU hKfg hKrad).trans
    (induced_chartSectionsIso_eq_adic e hKfg hKrad).symm

/-- Every affine formal open `U` admits a finitely generated ideal `J ⊆ Γ(U, O_X)` with
`J.radical = X.vanishingIdeal U`. -/
theorem exists_fg_radical_eq_vanishingIdeal (X : FormalScheme) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    ∃ J : Ideal (X.presheaf.obj (op U)), J.FG ∧ J.radical = X.vanishingIdeal U := by
  let c := hU.chartData
  let φ := (chartSectionsIso c.iso).commRingCatIsoToRingEquiv
  refine ⟨(IsAdicRing.ideal c.carrier).comap φ, ?_,
    radical_comap_chartSectionsIso c.iso (IsAdicRing.ideal_spec c.carrier).2.1⟩
  rw [← Ideal.map_symm]
  exact (IsAdicRing.ideal_spec c.carrier).1.map φ.symm.toRingHom

/-- Equipped with `X.sectionsTopology U hU`, `Γ(U, O_X)` is a topological ring. -/
theorem sectionsTopology_isTopologicalRing (X : FormalScheme) (U : Opens X)
    (hU : X.IsAffineOpen U) :
    @IsTopologicalRing (X.presheaf.obj (op U)) (X.sectionsTopology U hU) _ := by
  obtain ⟨J, hJfg, hJrad⟩ := X.exists_fg_radical_eq_vanishingIdeal U hU
  rw [X.sectionsTopology_eq_adic U hU hJfg hJrad]
  exact J.nonarchimedean.toIsTopologicalRing

private theorem isAdicRing_of_isInducing_ringEquiv {R S : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsAdicRing S]
    (φ : R ≃+* S) (hind : Topology.IsInducing φ) : IsAdicRing R := by
  have hIfg := (IsAdicRing.ideal_spec S).1
  have hI := (IsAdicRing.ideal_spec S).2.1
  have hIc := (IsAdicRing.ideal_spec S).2.2
  have hKfg : ((IsAdicRing.ideal S).comap φ).FG := by
    rw [← Ideal.map_symm]
    exact hIfg.map φ.symm.toRingHom
  have hKadic : IsAdic ((IsAdicRing.ideal S).comap φ) := IsAdic.comap hI φ hind
  have hKcomp : IsAdicComplete ((IsAdicRing.ideal S).comap φ) R := by
    rw [← Ideal.map_symm]
    exact (IsAdicComplete.congr_ringEquiv (IsAdicRing.ideal S) φ.symm).mpr hIc
  exact ⟨⟨(IsAdicRing.ideal S).comap φ, hKfg, hKadic, hKcomp⟩⟩

/-- Equipped with `X.sectionsTopology U hU`, `Γ(U, O_X)` is a complete separated adic ring of
finite ideal type. -/
theorem sectionsTopology_isAdicRing (X : FormalScheme) (U : Opens X) (hU : X.IsAffineOpen U) :
    letI := X.sectionsTopology U hU
    haveI := X.sectionsTopology_isTopologicalRing U hU
    IsAdicRing (X.presheaf.obj (op U)) := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  exact isAdicRing_of_isInducing_ringEquiv
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

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    CommRing hU.Sections :=
  hU.sectionsEquiv.commRing

/-- The underlying ring equivalence between `hU.Sections` and `Γ(U, O_X)`. -/
def sectionsRingEquiv {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    hU.Sections ≃+* X.presheaf.obj (op U) :=
  hU.sectionsEquiv.ringEquiv

/-- The `CommRingCat` isomorphism between `hU.Sections` and `Γ(U, O_X)`. -/
def sectionsIso {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    CommRingCat.of hU.Sections ≅ X.presheaf.obj (op U) :=
  hU.sectionsRingEquiv.toCommRingCatIso

noncomputable instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    TopologicalSpace hU.Sections :=
  TopologicalSpace.induced hU.sectionsEquiv (X.sectionsTopology U hU)

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsTopologicalRing hU.Sections := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have hind : Topology.IsInducing hU.sectionsRingEquiv := ⟨rfl⟩
  exact
    { continuous_add := hind.continuous_iff.mpr <| by
        simpa [Function.comp_def] using
          continuous_add.comp (hind.continuous.prodMap hind.continuous)
      continuous_mul := hind.continuous_iff.mpr <| by
        simpa [Function.comp_def] using
          continuous_mul.comp (hind.continuous.prodMap hind.continuous)
      continuous_neg := hind.continuous_iff.mpr <| by
        simpa [Function.comp_def] using continuous_neg.comp hind.continuous }

instance {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsAdicRing hU.Sections := by
  let := X.sectionsTopology U hU
  have := X.sectionsTopology_isTopologicalRing U hU
  have := X.sectionsTopology_isAdicRing U hU
  exact isAdicRing_of_isInducing_ringEquiv hU.sectionsRingEquiv ⟨rfl⟩

private noncomputable def chartRingEquiv {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) : hU.Sections ≃+* hU.chartData.carrier :=
  hU.sectionsRingEquiv.trans (chartSectionsIso hU.chartData.iso).commRingCatIsoToRingEquiv

private theorem isInducing_chartRingEquiv {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    Topology.IsInducing (chartRingEquiv hU) := by
  refine ⟨?_⟩
  -- Unfold `instTopologicalSpaceSections` to `TopologicalSpace.induced hU.sectionsEquiv _`.
  change TopologicalSpace.induced hU.sectionsEquiv (X.sectionsTopology U hU) = _
  rw [sectionsTopology_eq_induced_chart hU hU.chartData.iso, induced_compose]
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
  refine CommRingCat.hom_ext (RingHom.ext fun t ↦ ?_)
  let t' : (X.restrict U).presheaf.obj (op ⊤) := t
  let u : (Spf hU.chartData.carrier).presheaf.obj (op ⊤) := hU.chartData.iso.inv.c.app (op ⊤) t'
  have h1 : (ofSpfGlobalSectionsIso hU.Sections).hom
      ((LocallyRingedSpace.Γ.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv).op) t) =
      (chartRingEquiv hU).symm ((ofSpfGlobalSectionsIso hU.chartData.carrier).hom u) :=
    ConcreteCategory.congr_hom
      (Spf.map_globalSections (chartRingEquiv hU).symm.toRingHom
        (continuous_chartRingEquiv_symm hU)) u
  have h2 (b : hU.chartData.carrier) :
      hU.sectionsIso.hom ((chartRingEquiv hU).symm b) =
        (chartSectionsIso hU.chartData.iso).inv b :=
    hU.sectionsRingEquiv.apply_symm_apply _
  have h3 : (chartSectionsIso hU.chartData.iso).hom ((restrictTopSectionsIso X U).hom t') =
      (ofSpfGlobalSectionsIso hU.chartData.carrier).hom u :=
    congrArg (ofSpfGlobalSectionsIso hU.chartData.carrier).hom
      (congrArg (hU.chartData.iso.inv.c.app (op ⊤))
        (Iso.hom_inv_id_apply (restrictTopSectionsIso X U) t'))
  -- Evaluate the composed `CommRingCat` morphism on `t` and rewrite step by step.
  change hU.sectionsIso.hom ((ofSpfGlobalSectionsIso hU.Sections).hom
    ((LocallyRingedSpace.Γ.map (forgetToLocallyRingedSpace.map hU.isoSpf.inv).op) t)) =
    (restrictTopSectionsIso X U).hom t'
  rw [h1, h2, ← h3]
  exact Iso.hom_inv_id_apply (chartSectionsIso hU.chartData.iso)
    ((restrictTopSectionsIso X U).hom t')

/-- The canonical open immersion `ofSpf hU.Sections ⟶ X` with image `U`. -/
noncomputable def fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    ofSpf hU.Sections ⟶ X :=
  hU.isoSpf.inv ≫ X.ofRestrict U

instance isOpenImmersion_fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map hU.fromSpf) := by
  dsimp only [fromSpf]
  rw [Functor.map_comp]
  have : IsIso (forgetToLocallyRingedSpace.map hU.isoSpf.inv) :=
    Functor.map_isIso forgetToLocallyRingedSpace hU.isoSpf.inv
  infer_instance

@[simp]
theorem range_fromSpf {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    Set.range (forgetToLocallyRingedSpace.map hU.fromSpf).base = (U : Set X) := by
  dsimp only [fromSpf]
  rw [Functor.map_comp]
  exact (LocallyRingedSpace.range_iso_inv_comp
    (forgetToLocallyRingedSpace.mapIso hU.isoSpf)
    (forgetToLocallyRingedSpace.map (X.ofRestrict U))).trans (range_ofRestrict X U)

end IsAffineOpen

end IsoSpf

section Comparisons

/-- An affine formal open `U` of `X` makes `⊤` an affine formal open of `X.restrict U`. -/
theorem IsAffineOpen.top_restrict {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    (X.restrict U).IsAffineOpen ⊤ := by
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := (isAffineOpen_iff X U).mp hU
  rw [isAffineOpen_iff]
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(X.restrict U).toLocallyRingedSpace.restrictTopIso ≪≫ e⟩⟩

/-- `restrictTopSectionsIso X U` is a homeomorphism between `(Γ(⊤, O_{X|_U}), sectionsTopology)`
and `(Γ(U, O_X), sectionsTopology)`. -/
theorem isHomeomorph_restrictTopSectionsIso {X : FormalScheme} {U : Opens X}
    (hU : X.IsAffineOpen U) :
    @IsHomeomorph _ _ ((X.restrict U).sectionsTopology ⊤ hU.top_restrict)
      (X.sectionsTopology U hU) ((restrictTopSectionsIso X U).hom) := by
  obtain ⟨J, hJfg, hJrad⟩ := X.exists_fg_radical_eq_vanishingIdeal U hU
  let φ := (restrictTopSectionsIso X U).commRingCatIsoToRingEquiv
  have hKfg : (J.comap φ).FG := by
    rw [← Ideal.map_symm]
    exact hJfg.map φ.symm.toRingHom
  have hKrad : (J.comap φ).radical = (X.restrict U).vanishingIdeal ⊤ := by
    rw [← Ideal.comap_radical, hJrad]
    exact vanishingIdeal_comap_restrictTopSectionsIso_hom X U
  have htop : (X.restrict U).sectionsTopology ⊤ hU.top_restrict =
      TopologicalSpace.induced φ (X.sectionsTopology U hU) := by
    let tU : TopologicalSpace (X.presheaf.obj (op U)) := J.adicTopology
    let tT : TopologicalSpace ((X.restrict U).presheaf.obj (op ⊤)) :=
      TopologicalSpace.induced φ tU
    have hadic : @IsAdic _ _ tT (J.comap φ) := IsAdic.comap (I := J) rfl φ ⟨rfl⟩
    rw [(X.restrict U).sectionsTopology_eq_adic ⊤ hU.top_restrict hKfg hKrad,
      X.sectionsTopology_eq_adic U hU hJfg hJrad]
    exact hadic.symm
  let := (X.restrict U).sectionsTopology ⊤ hU.top_restrict
  let := X.sectionsTopology U hU
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- On `ofSpf A`, `ofSpfGlobalSectionsIso A` is a homeomorphism from `(Γ(⊤, O_{ofSpf A}),
sectionsTopology)` onto `A`. -/
theorem isHomeomorph_ofSpfGlobalSectionsIso (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    @IsHomeomorph _ _ ((ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A))
      ‹TopologicalSpace A› ((ofSpfGlobalSectionsIso A).hom) := by
  have hIfg := (IsAdicRing.ideal_spec A).1
  have hI := (IsAdicRing.ideal_spec A).2.1
  let φ := (ofSpfGlobalSectionsIso A).commRingCatIsoToRingEquiv
  have hKfg : ((IsAdicRing.ideal A).comap φ).FG := by
    rw [← Ideal.map_symm]
    exact hIfg.map φ.symm.toRingHom
  have hKrad : ((IsAdicRing.ideal A).comap φ).radical = (ofSpf A).vanishingIdeal ⊤ := by
    rw [← Ideal.comap_radical, ← vanishingIdeal_ofSpf_comap_globalSectionsIso_inv hI]
    ext s
    have hs : (ofSpfGlobalSectionsIso A).inv.hom (φ s) = s :=
      Iso.hom_inv_id_apply (ofSpfGlobalSectionsIso A) s
    simp only [Ideal.mem_comap, hs]
  have htop : (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A) =
      TopologicalSpace.induced φ ‹TopologicalSpace A› := by
    let tG : TopologicalSpace ((ofSpf A).presheaf.obj (op ⊤)) :=
      TopologicalSpace.induced φ ‹TopologicalSpace A›
    have hadic : @IsAdic _ _ tG ((IsAdicRing.ideal A).comap φ) := IsAdic.comap hI φ ⟨rfl⟩
    rw [(ofSpf A).sectionsTopology_eq_adic ⊤ (isAffineOpen_top_ofSpf A) hKfg hKrad]
    exact hadic.symm
  let := (ofSpf A).sectionsTopology ⊤ (isAffineOpen_top_ofSpf A)
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

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
  let t₂ := Spf.sectionsTopology hI ⊤
  have eq₂ : t₂ = TopologicalSpace.induced ((Spf.globalSectionsIso hI).hom)
      ‹TopologicalSpace A› :=
    h₂.isInducing.eq_induced
  exact eq₁.trans eq₂.symm

/-- Every affine formal open of a formal scheme is quasi-compact. -/
theorem IsAffineOpen.isCompact {X : FormalScheme} {U : Opens X} (hU : X.IsAffineOpen U) :
    IsCompact (U : Set X) := by
  obtain ⟨A, _, _, _, _, ⟨e⟩⟩ := (isAffineOpen_iff X U).mp hU
  have : CompactSpace (LocallyRingedSpace.forgetToTop.obj (Spf A)) :=
    Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1
  have : CompactSpace U :=
    (TopCat.homeoOfIso (LocallyRingedSpace.forgetToTop.mapIso e)).symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

/-- On an ordinary scheme `Y`, every affine formal open of `Y.toFormalScheme` carries the discrete
intrinsic section topology (`⊥`). -/
@[simp]
theorem sectionsTopology_toFormalScheme_eq_bot (Y : Scheme.{u}) (U : Opens Y.toFormalScheme)
    (hU : Y.toFormalScheme.IsAffineOpen U) :
    Y.toFormalScheme.sectionsTopology U hU = ⊥ := by
  have hrad : (⊥ : Ideal (Y.toFormalScheme.presheaf.obj (op U))).radical =
      Y.toFormalScheme.vanishingIdeal U := by
    ext s
    rw [Ideal.mem_radical_iff, mem_vanishingIdeal]
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
    (U : Opens Y.toFormalScheme) (hU : Y.toFormalScheme.IsAffineOpen U) :
    @DiscreteTopology _ (Y.toFormalScheme.sectionsTopology U hU) :=
  @DiscreteTopology.mk _ (Y.toFormalScheme.sectionsTopology U hU)
    (sectionsTopology_toFormalScheme_eq_bot Y U hU)

instance IsAffineOpen.discreteTopology_sections_toFormalScheme {Y : Scheme.{u}}
    {U : Opens Y.toFormalScheme} (hU : Y.toFormalScheme.IsAffineOpen U) :
    DiscreteTopology hU.Sections := by
  refine ⟨?_⟩
  -- Unfold the induced `TopologicalSpace hU.Sections` instance to rewrite `sectionsTopology`.
  change TopologicalSpace.induced hU.sectionsEquiv (Y.toFormalScheme.sectionsTopology U hU) = ⊥
  rw [sectionsTopology_toFormalScheme_eq_bot Y U hU]
  exact TauCeti.induced_bot_of_injective hU.sectionsEquiv.injective

/-- An open subset of an ordinary scheme `Y` is an affine formal open of `Y.toFormalScheme` if and
only if it is an affine open of `Y` as a scheme. -/
@[simp]
theorem isAffineOpen_toFormalScheme_iff (Y : Scheme.{u}) (U : Y.Opens) :
    Y.toFormalScheme.IsAffineOpen U ↔ AlgebraicGeometry.IsAffineOpen U := by
  constructor
  · intro hU
    let U' : Opens Y.toFormalScheme := U
    have hU' : Y.toFormalScheme.IsAffineOpen U' := hU
    let eLRS : U.toScheme.toLocallyRingedSpace ≅
        (Spec (CommRingCat.of hU'.Sections)).toLocallyRingedSpace :=
      forgetToLocallyRingedSpace.mapIso hU'.isoSpf ≪≫ Spf.discreteIsoSpec hU'.Sections
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

/-- Being an affine formal scheme (`IsAffineOpen ⊤`) is preserved under isomorphism. -/
theorem isAffineOpen_top_of_iso {X Y : FormalScheme} (e : X ≅ Y) (hX : X.IsAffineOpen ⊤) :
    Y.IsAffineOpen ⊤ := by
  obtain ⟨A, _, _, _, _, ⟨eA⟩⟩ := (isAffineOpen_iff X ⊤).mp hX
  let eRestr : Y.restrict ⊤ ≅ X.restrict ⊤ := Y.restrictTopIso ≪≫ e.symm ≪≫ X.restrictTopIso.symm
  exact (isAffineOpen_iff Y ⊤).mpr
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨forgetToLocallyRingedSpace.mapIso eRestr ≪≫ eA⟩⟩

/-- Two isomorphic formal schemes have `⊤` affine simultaneously. -/
theorem isAffineOpen_top_iff_of_iso {X Y : FormalScheme} (e : X ≅ Y) :
    X.IsAffineOpen ⊤ ↔ Y.IsAffineOpen ⊤ :=
  ⟨isAffineOpen_top_of_iso e, isAffineOpen_top_of_iso e.symm⟩

/-- The isomorphism on global sections `Γ(Y, O_Y) ≅ Γ(X, O_X)` induced by an isomorphism
`e : X ≅ Y` of formal schemes. -/
noncomputable def globalSectionsIsoOfIso {X Y : FormalScheme} (e : X ≅ Y) :
    Y.presheaf.obj (op ⊤) ≅ X.presheaf.obj (op ⊤) where
  hom := (forgetToLocallyRingedSpace.map e.hom).c.app (op ⊤)
  inv := (forgetToLocallyRingedSpace.map e.inv).c.app (op ⊤)
  hom_inv_id := (LocallyRingedSpace.Γ.mapIso (forgetToLocallyRingedSpace.mapIso e).op).hom_inv_id
  inv_hom_id := (LocallyRingedSpace.Γ.mapIso (forgetToLocallyRingedSpace.mapIso e).op).inv_hom_id

/-- An isomorphism `e : X ≅ Y` of formal schemes pulls `X.vanishingIdeal ⊤` back to
`Y.vanishingIdeal ⊤` along global sections. -/
theorem vanishingIdeal_top_comap_of_iso {X Y : FormalScheme} (e : X ≅ Y) :
    (X.vanishingIdeal ⊤).comap (globalSectionsIsoOfIso e).hom.hom = Y.vanishingIdeal ⊤ := by
  let f := forgetToLocallyRingedSpace.map e.hom
  have hsurj : Function.Surjective f.base :=
    (TopCat.homeoOfIso
      (LocallyRingedSpace.forgetToTop.mapIso (forgetToLocallyRingedSpace.mapIso e))).surjective
  ext s
  rw [Ideal.mem_comap, mem_vanishingIdeal_top, mem_vanishingIdeal_top]
  have hpt (x : X) :
      X.toLocallyRingedSpace.Γevaluation x ((globalSectionsIsoOfIso e).hom s) = 0 ↔
        Y.toLocallyRingedSpace.Γevaluation (f.base x) s = 0 :=
    (Iff.of_eq (congrArg (· = 0)
      (LocallyRingedSpace.Γevaluation_naturality_apply f x s).symm)).trans
      (residueFieldMap_eq_zero_iff f x _)
  exact ⟨fun h y ↦ by obtain ⟨x, rfl⟩ := hsurj y; exact (hpt x).mp (h x),
    fun h x ↦ (hpt x).mpr (h (f.base x))⟩

/-- For an isomorphism `e : X ≅ Y` between affine formal schemes, the induced global-sections map
`Γ(Y, O_Y) → Γ(X, O_X)` is a homeomorphism for `sectionsTopology`. -/
theorem isHomeomorph_globalSections_of_iso {X Y : FormalScheme} (e : X ≅ Y)
    (hX : X.IsAffineOpen ⊤) (hY : Y.IsAffineOpen ⊤) :
    @IsHomeomorph _ _ (Y.sectionsTopology ⊤ hY) (X.sectionsTopology ⊤ hX)
      (globalSectionsIsoOfIso e).hom := by
  let φ : Y.presheaf.obj (op ⊤) ≃+* X.presheaf.obj (op ⊤) :=
    (globalSectionsIsoOfIso e).commRingCatIsoToRingEquiv
  obtain ⟨J, hJfg, hJrad⟩ := X.exists_fg_radical_eq_vanishingIdeal ⊤ hX
  have hKfg : (J.comap φ).FG := by
    rw [← Ideal.map_symm]
    exact hJfg.map φ.symm.toRingHom
  have hKrad : (J.comap φ).radical = Y.vanishingIdeal ⊤ := by
    rw [← Ideal.comap_radical, hJrad]
    exact vanishingIdeal_top_comap_of_iso e
  have htop : Y.sectionsTopology ⊤ hY =
      TopologicalSpace.induced φ (X.sectionsTopology ⊤ hX) := by
    let tX : TopologicalSpace (X.presheaf.obj (op ⊤)) := J.adicTopology
    let tY : TopologicalSpace (Y.presheaf.obj (op ⊤)) := TopologicalSpace.induced φ tX
    have hadic : @IsAdic _ _ tY (J.comap φ) :=
      IsAdic.comap (rfl : @IsAdic _ _ tX J) φ ⟨rfl⟩
    rw [X.sectionsTopology_eq_adic ⊤ hX hJfg hJrad, Y.sectionsTopology_eq_adic ⊤ hY hKfg hKrad]
    exact hadic.symm
  let := Y.sectionsTopology ⊤ hY
  let := X.sectionsTopology ⊤ hX
  exact (φ.toEquiv.toHomeomorphOfIsInducing ⟨htop⟩).isHomeomorph

/-- If an affine formal scheme `ofSpf A` is isomorphic in `FormalScheme` to `Y.toFormalScheme` for
an ordinary scheme `Y`, then `A` carries the discrete topology. -/
theorem discreteTopology_of_iso_toFormalScheme {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] {Y : Scheme.{u}} (e : ofSpf A ≅ Y.toFormalScheme) :
    DiscreteTopology A := by
  have hA : (ofSpf A).IsAffineOpen ⊤ := isAffineOpen_top_ofSpf A
  have hY : Y.toFormalScheme.IsAffineOpen ⊤ := isAffineOpen_top_of_iso e hA
  let := (ofSpf A).sectionsTopology ⊤ hA
  let := Y.toFormalScheme.sectionsTopology ⊤ hY
  have hdY : DiscreteTopology (Y.toFormalScheme.presheaf.obj (op ⊤)) :=
    discreteTopology_sectionsTopology_toFormalScheme Y ⊤ hY
  have hdA : DiscreteTopology ((ofSpf A).presheaf.obj (op ⊤)) :=
    (isHomeomorph_globalSections_of_iso e hA hY).homeomorph.discreteTopology_iff.mp hdY
  exact (isHomeomorph_ofSpfGlobalSectionsIso A).homeomorph.discreteTopology_iff.mp hdA

/-- An affine formal scheme `ofSpf A` lies in the essential image of `Scheme.toFormalScheme`
(`ofScheme`) if and only if `A` carries the discrete topology. -/
@[simp]
theorem exists_iso_toFormalScheme_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (∃ Y : Scheme.{u}, Nonempty (ofSpf A ≅ Y.toFormalScheme)) ↔ DiscreteTopology A :=
  ⟨fun ⟨_, ⟨e⟩⟩ ↦ discreteTopology_of_iso_toFormalScheme e,
    fun _ ↦ ⟨Spec (CommRingCat.of A), ⟨(ofSchemeSpecIso A).symm⟩⟩⟩

end Comparisons

end TauCeti.FormalScheme
