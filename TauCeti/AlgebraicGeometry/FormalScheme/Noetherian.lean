/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.FormalScheme.SectionsTopology
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedNeighbourhood.Noetherian

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Locally noetherian and noetherian formal schemes

A formal scheme `X` is locally noetherian (`TauCeti.FormalScheme.IsLocallyNoetherian`) if every
point has an open neighbourhood admitting an open immersion from `Spf A` for a noetherian adic
ring `A` (EGA I, Ch. I, 10.4.2), and noetherian (`TauCeti.FormalScheme.IsNoetherian`) if it is
locally noetherian and quasi-compact.

The nontrivial foundational theorem is the converse on affine formal opens (EGA I, Ch. I, 10.6.5):
if `ofSpf B` is locally noetherian for an adic ring `B`, then `B` itself is a noetherian ring
(`TauCeti.FormalScheme.ofSpf_isLocallyNoetherian_iff`), and consequently on any locally noetherian
formal scheme `X`, the section ring `Γ(U, O_X)` over *every* affine formal open `U` is noetherian
(`TauCeti.FormalScheme.IsAffineOpen.isNoetherianRing`).

To prove EGA I, Ch. I, 10.6.5 without assuming any general morphism correspondence into `Spf`:
for an ideal of definition `J` of `B`, the thickening `Spec (B ⧸ J) ⟶ Spf B` is a homeomorphism
that is surjective on stalks (`TauCeti.FormalScheme.Spf.fromSpecQuotient`). Around every prime of
`B ⧸ J`, shrinking to a principal open `D(g) ≅ Spec ((B ⧸ J)_g)` lands inside a noetherian chart
`Spf C ⟶ Spf B`. Lifting `Spec ((B ⧸ J)_g) ⟶ Spf B` into `Spf C` yields an open embedding on
underlying spaces that is surjective on stalks; its global-section homomorphism
`ψ : C →+* (B ⧸ J)_g` annihilates a power `K = I ^ (m + 1)` of an ideal of definition of `C`, and
by the quotient localisation equivalence `CompletedAway.quotientPowEquiv` the factored map
`C ⧸ K →+* (B ⧸ J)_g` induces an open-range preimmersion of affine schemes, hence a closed
immersion onto an open subscheme of the noetherian scheme `Spec (C ⧸ K)`. Thus `(B ⧸ J)_g` is
noetherian for `g` spanning the unit ideal of `B ⧸ J`, so `B ⧸ J` is noetherian, and
`Ideal.isNoetherianRing_of_isAdicComplete` concludes that `B` is noetherian.

## Main definitions

* `TauCeti.FormalScheme.IsLocallyNoetherian`: locally noetherian formal schemes.
* `TauCeti.FormalScheme.IsNoetherian`: noetherian formal schemes (locally noetherian and
  quasi-compact).

## Main results

* `TauCeti.FormalScheme.Spf.stalk_isNoetherianRing`: the stalks of `Spf A` are noetherian for a
  noetherian adic ring `A`.
* `TauCeti.FormalScheme.stalk_isNoetherianRing`: the stalks of a locally noetherian formal scheme
  are noetherian local rings.
* `TauCeti.FormalScheme.ofSpf_isLocallyNoetherian_iff`,
  `TauCeti.FormalScheme.ofSpf_isNoetherian_iff`: `ofSpf A` is (locally) noetherian if and only if
  `A` is a noetherian ring (EGA I, Ch. I, 10.6.5).
* `TauCeti.FormalScheme.IsAffineOpen.isNoetherianRing`,
  `TauCeti.FormalScheme.isLocallyNoetherian_iff_forall_isAffineOpen`: `X` is locally noetherian if
  and only if `Γ(U, O_X)` is noetherian for every affine formal open `U`.
* `TauCeti.FormalScheme.IsNoetherian.noetherianSpace`: every noetherian formal scheme has a
  noetherian underlying topological space.
* `TauCeti.FormalScheme.toFormalScheme_isLocallyNoetherian_iff`,
  `TauCeti.FormalScheme.toFormalScheme_isNoetherian_iff`: `Scheme.toFormalScheme` (`ofScheme`)
  preserves and reflects both `IsLocallyNoetherian` and `IsNoetherian`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. I, 10.4.2 and
  10.6.5.
* [Stacks Project, Tag 01YC](https://stacks.math.columbia.edu/tag/01YC).
-/

public section

universe u

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry

namespace TauCeti.FormalScheme

namespace Spf

/-- The stalks of `Spf A` for a noetherian adic ring `A` are noetherian local rings. -/
instance stalk_isNoetherianRing {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [IsNoetherianRing A] (p : Spf A) :
    IsNoetherianRing ((Spf A).presheaf.stalk p) := by
  let p' : carrier A := p
  let e : Limits.colimit (completedNeighbourhoodDiagram p') ≅ (Spf A).presheaf.stalk p :=
    completedNeighbourhoodColimitIso p' (IsAdicRing.ideal_spec A).2.1 (IsAdicRing.ideal_spec A).1
  exact isNoetherianRing_of_ringEquiv _ e.commRingCatIsoToRingEquiv

/-- The underlying space of `Spf A` for a noetherian topological ring `A` is a noetherian
topological space. -/
instance noetherianSpace_carrier {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsNoetherianRing A] : NoetherianSpace (carrier A) :=
  have : NoetherianSpace (PrimeSpectrum A) := PrimeSpectrum.instNoetherianSpace A
  TopologicalSpace.NoetherianSpace.set (carrier A)

end Spf

/-- Every affine formal scheme `ofSpf A` has a quasi-compact underlying space. -/
instance compactSpace_ofSpf (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] : CompactSpace (ofSpf A) :=
  Spf.compactSpace_carrier (IsAdicRing.ideal_spec A).2.1

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
instance ofSpf_isLocallyNoetherian (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] [IsNoetherianRing A] :
    (ofSpf A).IsLocallyNoetherian where
  exists_noetherian_spf x :=
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      𝟙 (Spf A), inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (𝟙 (Spf A))), ⟨x, rfl⟩⟩

/-- For a noetherian adic ring `A`, `ofSpf A` is noetherian. -/
instance ofSpf_isNoetherian (A : Type u) [CommRing A] [TopologicalSpace A]
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
  obtain ⟨V, ⟨a, rfl⟩, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen)
    (show y ∈ (Opens.map i.base).obj U from (congrArg (fun z ↦ z ∈ U) hy).mpr hx)
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
instance restrict_isLocallyNoetherian (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X) :
    (X.restrict U).IsLocallyNoetherian :=
  isLocallyNoetherian_of_isOpenImmersion (X.ofRestrict U)

/-- Every quasi-compact open formal subscheme of a locally noetherian formal scheme is
noetherian. -/
instance restrict_isNoetherian (X : FormalScheme) [X.IsLocallyNoetherian] (U : Opens X)
    [CompactSpace U] : (X.restrict U).IsNoetherian where
  toCompactSpace := ‹CompactSpace U›

/-- `IsLocallyNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isLocallyNoetherian_congr {X Y : FormalScheme} (e : X ≅ Y) :
    X.IsLocallyNoetherian ↔ Y.IsLocallyNoetherian :=
  ⟨fun _ ↦ isLocallyNoetherian_of_isOpenImmersion e.inv,
    fun _ ↦ isLocallyNoetherian_of_isOpenImmersion e.hom⟩

/-- `IsNoetherian` is invariant under isomorphism of formal schemes. -/
theorem isNoetherian_congr {X Y : FormalScheme} (e : X ≅ Y) :
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
  rw [isNoetherian_iff, isNoetherian_iff, isLocallyNoetherian_congr e, hcomp]

/-- Every stalk of a locally noetherian formal scheme is a noetherian ring. -/
instance stalk_isNoetherianRing (X : FormalScheme) [X.IsLocallyNoetherian] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨A, _, _, _, _, _, f, hf, y, rfl⟩ := IsLocallyNoetherian.exists_noetherian_spf x
  have := hf
  let e := asIso (f.stalkMap y)
  exact isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv

end BasicProperties

section ConverseAffine

private noncomputable def homSpfGlobalMap {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) : C →+* R :=
  have := (IsAdicRing.ideal_spec C).2.2
  ((Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv ≫
    LocallyRingedSpace.Γ.map α.op ≫
    (asIso (toSpecΓ (CommRingCat.of R))).inv).hom

private theorem homSpfGlobalMap_toSpecΓ {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (c : C) :
    have := (IsAdicRing.ideal_spec C).2.2
    toSpecΓ (CommRingCat.of R) (homSpfGlobalMap α c) =
      LocallyRingedSpace.Γ.map α.op
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c) := by
  intro
  exact Iso.inv_hom_id_apply (asIso (toSpecΓ (CommRingCat.of R)))
    (LocallyRingedSpace.Γ.map α.op
      ((Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c))

private theorem residueFieldMap_eq_zero_iff' {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X)
    (a : Y.residueField (f.base x)) :
    LocallyRingedSpace.residueFieldMap f x a = 0 ↔ a = 0 :=
  map_eq_zero_iff (IsLocalRing.ResidueField.map (f.stalkMap x).hom) (RingHom.injective _)

private theorem asIdeal_base_eq_comap_homSpfGlobalMap {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (q : PrimeSpectrum R) :
    (α.base q).1.asIdeal = q.asIdeal.comap (homSpfGlobalMap α) := by
  have := (IsAdicRing.ideal_spec C).2.2
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have := (IsAdicRing.ideal_spec R).2.2
  let d := Spf.discreteIsoSpec R
  let q₀ : Spec.locallyRingedSpaceObj (CommRingCat.of R) := q
  let x : Spf R := d.inv.base q₀
  have hx_base : (d.hom ≫ α).base x = α.base q₀ :=
    congrArg α.base (LocallyRingedSpace.iso_inv_base_hom_base_apply d q₀)
  have hx_val : x.1 = q := Spf.discreteIsoSpec_inv_base_apply R q
  have hsec (c : C) : LocallyRingedSpace.Γ.map (d.hom ≫ α).op
      ((Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c) =
      (Spf.globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv
        (homSpfGlobalMap α c) := by
    have hd_comp : LocallyRingedSpace.Γ.map (d.hom ≫ α).op ≫
        LocallyRingedSpace.Γ.map d.inv.op = LocallyRingedSpace.Γ.map α.op := by
      rw [← LocallyRingedSpace.Γ.map_comp, ← op_comp, Iso.inv_hom_id_assoc]
    apply (ConcreteCategory.bijective_of_isIso (LocallyRingedSpace.Γ.map d.inv.op)).1
    have h1 := ConcreteCategory.congr_hom hd_comp
      ((Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c)
    have h2 : LocallyRingedSpace.Γ.map d.inv.op
        ((Spf.globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv
          (homSpfGlobalMap α c)) = toSpecΓ (CommRingCat.of R) (homSpfGlobalMap α c) :=
      ConcreteCategory.congr_hom (Spf.discreteIsoSpec_inv_globalSections R) (homSpfGlobalMap α c)
    exact h1.trans ((homSpfGlobalMap_toSpecΓ α c).symm.trans h2.symm)
  ext c
  let sC : (Spf C).presheaf.obj (op ⊤) :=
    (Spf.globalSectionsIso (IsAdicRing.ideal_spec C).2.1).inv c
  have h1 : c ∈ (α.base q₀).1.asIdeal ↔
      (Spf C).Γevaluation ((d.hom ≫ α).base x) sC = 0 :=
    (Spf.Γevaluation_globalSectionsIso_inv_eq_zero_iff (α.base q₀) c).symm.trans
      (Iff.of_eq (congrArg (fun p ↦ (Spf C).Γevaluation p sC = 0) hx_base.symm))
  have hnat : (Spf C).Γevaluation ((d.hom ≫ α).base x) sC = 0 ↔
      (Spf R).Γevaluation x (LocallyRingedSpace.Γ.map (d.hom ≫ α).op sC) = 0 :=
    (residueFieldMap_eq_zero_iff' (d.hom ≫ α) x _).symm.trans
      (Iff.of_eq (congrArg (· = 0)
        (LocallyRingedSpace.Γevaluation_naturality_apply (d.hom ≫ α) x sC)))
  have hevR : (Spf R).Γevaluation x
      ((Spf.globalSectionsIso (IsAdicRing.ideal_spec R).2.1).inv (homSpfGlobalMap α c)) = 0 ↔
      homSpfGlobalMap α c ∈ x.1.asIdeal :=
    Spf.Γevaluation_globalSectionsIso_inv_eq_zero_iff x (homSpfGlobalMap α c)
  have h2 : (Spf R).Γevaluation x (LocallyRingedSpace.Γ.map (d.hom ≫ α).op sC) = 0 ↔
      c ∈ q.asIdeal.comap (homSpfGlobalMap α) :=
    (Iff.of_eq (congrArg (fun t ↦ (Spf R).Γevaluation x t = 0) (hsec c))).trans
      (hevR.trans (by rw [hx_val, Ideal.mem_comap]))
  exact (h1.trans hnat).trans h2

private noncomputable def homSpfQuotientLift {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (homSpfGlobalMap α)) :
    C ⧸ IsAdicRing.ideal C ^ (m + 1) →+* R :=
  Ideal.Quotient.lift (IsAdicRing.ideal C ^ (m + 1)) (homSpfGlobalMap α)
    fun _ ha ↦ RingHom.mem_ker.mp (hm ha)

private theorem exists_ideal_pow_le_ker_homSpfGlobalMap {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) :
    ∃ m : ℕ, IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (homSpfGlobalMap α) := by
  let ψ := homSpfGlobalMap α
  let I := IsAdicRing.ideal C
  have hIfg : I.FG := (IsAdicRing.ideal_spec C).1
  have hI : IsAdic I := (IsAdicRing.ideal_spec C).2.1
  have hle_rad : I.map ψ ≤ (⊥ : Ideal R).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_sInf]
    rintro P ⟨_, hP⟩
    let q : PrimeSpectrum R := ⟨P, hP⟩
    have hc' : c ∈ (α.base q).1.asIdeal :=
      (Spf.mem_carrier_iff_le hI).mp (α.base q).2 hc
    rwa [asIdeal_base_eq_comap_homSpfGlobalMap α q, Ideal.mem_comap] at hc'
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle_rad (hIfg.map ψ)
  refine ⟨n, ?_⟩
  have hpow : (I.map ψ) ^ (n + 1) = ⊥ :=
    le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn)
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker] at hpow
  exact hpow

private theorem isOpenEmbedding_comap_quotientLift {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα : Topology.IsOpenEmbedding α.base) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (homSpfGlobalMap α)) :
    Topology.IsOpenEmbedding (PrimeSpectrum.comap (homSpfQuotientLift α hm)) := by
  let K := IsAdicRing.ideal C ^ (m + 1)
  have hK : IsAdic K := is_ideal_adic_pow (IsAdicRing.ideal_spec C).2.1 m.succ_pos
  let ψbar := homSpfQuotientLift α hm
  let qK := Spf.fromSpecQuotient hK
  let fSpec : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (C ⧸ K)) :=
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom ψbar)
  have hcomp : qK.base ∘ fSpec.base = α.base := by
    ext q : 1
    let q' : PrimeSpectrum R := q
    apply Subtype.ext
    apply PrimeSpectrum.ext
    have hpts : (qK.base (fSpec.base q)).1 =
        PrimeSpectrum.comap (Ideal.Quotient.mk K) (PrimeSpectrum.comap ψbar q') :=
      (congrArg Subtype.val (Spf.fromSpecQuotient_points hK _)).trans
        (Spf.coe_homeomorphSpecQuotient_symm_apply hK _)
    refine (congrArg PrimeSpectrum.asIdeal hpts).trans ?_
    refine Eq.trans ?_ (asIdeal_base_eq_comap_homSpfGlobalMap α q').symm
    ext c
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ q'.asIdeal) (Ideal.Quotient.lift_mk K _ _))
  have hhomeo : IsHomeomorph qK.base := Spf.fromSpecQuotient_isHomeomorph hK
  have hemb : Topology.IsEmbedding fSpec.base :=
    hhomeo.isOpenEmbedding.isEmbedding.of_comp_iff.mp (hcomp ▸ hα.isEmbedding)
  have hrange : Set.range fSpec.base = qK.base ⁻¹' Set.range α.base := by
    rw [← hcomp, Set.range_comp, Set.preimage_image_eq _ hhomeo.bijective.1]
  exact (Topology.isOpenEmbedding_iff _).mpr
    ⟨hemb, hrange ▸ hα.isOpen_range.preimage qK.base.hom.continuous⟩

private theorem germ_basicOpen_toStalk {C R : Type u} [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) (q : PrimeSpectrum R)
    (a : C) (hqa : α.base q ∈ Spf.basicOpen a) (c : C) :
    let Ua : Opens (Spf C) := Spf.basicOpen a
    (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj Ua) q hqa
      (α.c.app (op Ua)
        ((Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
          (IsAdicRing.ideal_spec C).1 a).inv
          (algebraMap C (AdicRing.CompletedAway C a) c))) =
      StructureSheaf.toStalk R q (homSpfGlobalMap α c) := by
  intro Ua
  have := (IsAdicRing.ideal_spec C).2.2
  let hIC := (IsAdicRing.ideal_spec C).2.1
  let hICfg := (IsAdicRing.ideal_spec C).1
  have hres : (Spf.basicOpenSectionsIso hIC hICfg a).inv
      (algebraMap C (AdicRing.CompletedAway C a) c) =
      (Spf C).presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op
        ((Spf.globalSectionsIso hIC).inv c) := by
    apply (Spf.basicOpenSectionsIso hIC hICfg a).commRingCatIsoToRingEquiv.injective
    have h1 := ConcreteCategory.congr_hom
      (Spf.globalSectionsIso_inv_comp_basicOpenSectionsIso_hom hIC hICfg a) c
    exact (Iso.inv_hom_id_apply (Spf.basicOpenSectionsIso hIC hICfg a) _).trans h1.symm
  have hnat := ConcreteCategory.congr_hom
    (α.c.naturality (homOfLE (le_top : Ua ≤ ⊤)).op)
    ((Spf.globalSectionsIso hIC).inv c)
  rw [hres]
  have hnat' : α.c.app (op Ua)
      ((Spf C).presheaf.map (homOfLE (le_top : Ua ≤ ⊤)).op
        ((Spf.globalSectionsIso hIC).inv c)) =
      (Spec.structureSheaf R).presheaf.map
        (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)).op
        (LocallyRingedSpace.Γ.map α.op ((Spf.globalSectionsIso hIC).inv c)) := hnat
  have hgerm : (Spec.structureSheaf R).presheaf.germ
      ((Opens.map α.base).obj Ua) q hqa
      ((Spec.structureSheaf R).presheaf.map
        (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)).op
        (LocallyRingedSpace.Γ.map α.op ((Spf.globalSectionsIso hIC).inv c))) =
      (Spec.structureSheaf R).presheaf.germ ⊤ q trivial
        (LocallyRingedSpace.Γ.map α.op ((Spf.globalSectionsIso hIC).inv c)) :=
    TopCat.Presheaf.germ_res_apply (Spec.structureSheaf R).presheaf
      (homOfLE (le_top : (Opens.map α.base).obj Ua ≤ ⊤)) q hqa _
  rw [hnat']
  exact hgerm.trans (congrArg ((Spec.structureSheaf R).presheaf.germ ⊤ q trivial)
    (homSpfGlobalMap_toSpecΓ α c).symm)

private theorem exists_stalk_preimage_completedAway {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (homSpfGlobalMap α))
    (q : PrimeSpectrum R) (a : C) (hqa : α.base q ∈ Spf.basicOpen a)
    (w : AdicRing.CompletedAway C a) :
    ∃ z, (Spec.map (CommRingCat.ofHom (homSpfQuotientLift α hm))).stalkMap q z =
      (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj (Spf.basicOpen a)) q hqa
        (α.c.app (op (Spf.basicOpen a))
          ((Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
            (IsAdicRing.ideal_spec C).1 a).inv w)) := by
  let K := IsAdicRing.ideal C ^ (m + 1)
  let ψbar := homSpfQuotientLift α hm
  let φ := CommRingCat.ofHom ψbar
  let g₁ : AdicRing.CompletedAway C a →+* (Spec.structureSheaf R).presheaf.stalk q :=
    ((Spf.basicOpenSectionsIso (IsAdicRing.ideal_spec C).2.1
      (IsAdicRing.ideal_spec C).1 a).inv ≫ α.c.app (op (Spf.basicOpen a)) ≫
      (Spec.structureSheaf R).presheaf.germ ((Opens.map α.base).obj (Spf.basicOpen a)) q hqa).hom
  have hg₁_alg (c : C) : g₁ (algebraMap C (AdicRing.CompletedAway C a) c) =
      StructureSheaf.toStalk R q (homSpfGlobalMap α c) :=
    germ_basicOpen_toStalk α q a hqa c
  have hker : ∀ x ∈ (IsAdicRing.ideal C).map (algebraMap C (AdicRing.CompletedAway C a)) ^ (m + 1),
      g₁ x = 0 := by
    suffices (IsAdicRing.ideal C).map (algebraMap C (AdicRing.CompletedAway C a)) ^ (m + 1) ≤
        RingHom.ker g₁ from fun x hx ↦ RingHom.mem_ker.mp (this hx)
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro c hc
    rw [Ideal.mem_comap, RingHom.mem_ker, hg₁_alg c, RingHom.mem_ker.mp (hm hc), map_zero]
    rfl
  let abar : C ⧸ K := Ideal.Quotient.mk K a
  let liftG₁ := Ideal.Quotient.lift _ g₁ hker
  let eqv := AdicRing.CompletedAway.quotientPowEquiv C a (m + 1)
  let h₁ : Localization.Away abar →+* (Spec.structureSheaf R).presheaf.stalk q :=
    liftG₁.comp eqv.symm.toRingHom
  let p : PrimeSpectrum (C ⧸ K) := PrimeSpectrum.comap ψbar q
  have hp_mem : abar ∈ p.asIdeal.primeCompl := by
    have ha_notMem : a ∉ (α.base q).1.asIdeal := Spf.mem_basicOpen.mp hqa
    rwa [asIdeal_base_eq_comap_homSpfGlobalMap] at ha_notMem
  let ιLoc : Localization.Away abar →+* (Spec.structureSheaf (C ⧸ K)).presheaf.stalk p :=
    IsLocalization.Away.lift abar
      (IsLocalization.map_units ((Spec.structureSheaf (C ⧸ K)).presheaf.stalk p) ⟨abar, hp_mem⟩)
  have heq : (((Spec.map φ).stalkMap q).hom).comp ιLoc = h₁ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers abar)
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_))
    let cbar := Ideal.Quotient.mk K c
    have hq_eq : eqv.symm (algebraMap (C ⧸ K) (Localization.Away abar) cbar) =
        Ideal.Quotient.mk _ (algebraMap C (AdicRing.CompletedAway C a) c) :=
      eqv.injective ((eqv.apply_symm_apply _).trans (eqv.commutes c).symm)
    have he₁ : ((Spec.map φ).stalkMap q).hom
        (ιLoc (algebraMap (C ⧸ K) (Localization.Away abar) cbar)) =
        ((Spec.map φ).stalkMap q).hom (StructureSheaf.toStalk (C ⧸ K) p cbar) :=
      congrArg ((Spec.map φ).stalkMap q).hom (IsLocalization.Away.lift_eq _ _ cbar)
    have he₂ : ((Spec.map φ).stalkMap q).hom (StructureSheaf.toStalk (C ⧸ K) p cbar) =
        StructureSheaf.toStalk R q (homSpfGlobalMap α c) := stalkMap_toStalk_apply φ q cbar
    have he₃ : g₁ (algebraMap C (AdicRing.CompletedAway C a) c) =
        h₁ (algebraMap (C ⧸ K) (Localization.Away abar) cbar) :=
      (Ideal.Quotient.lift_mk _ g₁ hker).symm.trans (congrArg liftG₁ hq_eq.symm)
    exact he₁.trans (he₂.trans ((hg₁_alg c).symm.trans he₃))
  exact ⟨ιLoc (eqv (Ideal.Quotient.mk _ w)), (RingHom.congr_fun heq _).trans
    ((congrArg liftG₁ (eqv.symm_apply_apply _)).trans (Ideal.Quotient.lift_mk _ g₁ hker))⟩

private theorem surjective_specMap_stalkMap_quotientLift {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα_stalk : ∀ q, Function.Surjective (α.stalkMap q)) {m : ℕ}
    (hm : IsAdicRing.ideal C ^ (m + 1) ≤ RingHom.ker (homSpfGlobalMap α))
    (q : PrimeSpectrum R) :
    Function.Surjective
      ((Spec.map (CommRingCat.ofHom (homSpfQuotientLift α hm))).stalkMap q) := by
  intro t
  obtain ⟨s, rfl⟩ := hα_stalk q t
  obtain ⟨U, hxU, u, rfl⟩ := (Spf C).presheaf.exists_germ_eq s
  obtain ⟨_, ⟨a, rfl⟩, hqa, haU⟩ :=
    (Opens.isBasis_iff_nbhd.mp Spf.isBasis_basicOpen) hxU
  let hIC := (IsAdicRing.ideal_spec C).2.1
  let hICfg := (IsAdicRing.ideal_spec C).1
  let w : AdicRing.CompletedAway C a :=
    (Spf.basicOpenSectionsIso hIC hICfg a).hom ((Spf C).presheaf.map (homOfLE haU).op u)
  obtain ⟨z, hz⟩ := exists_stalk_preimage_completedAway α hm q a hqa w
  refine ⟨z, hz.trans ?_⟩
  have hgerm : (Spf C).presheaf.germ (Spf.basicOpen a) (α.base q) hqa
      ((Spf.basicOpenSectionsIso hIC hICfg a).inv w) =
      (Spf C).presheaf.germ U (α.base q) hxU u :=
    (congrArg ((Spf C).presheaf.germ (Spf.basicOpen a) (α.base q) hqa)
      (Iso.hom_inv_id_apply (Spf.basicOpenSectionsIso hIC hICfg a) _)).trans
      (TopCat.Presheaf.germ_res_apply (Spf C).presheaf (homOfLE haU) (α.base q) hqa u)
  exact (PresheafedSpace.stalkMap_germ_apply α.toHom (Spf.basicOpen a) q hqa _).symm.trans
    (congrArg (α.stalkMap q) hgerm)

private theorem isNoetherianRing_of_openEmbedding_hom_spf {C R : Type u} [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C] [IsNoetherianRing C] [CommRing R]
    (α : Spec.locallyRingedSpaceObj (CommRingCat.of R) ⟶ Spf C)
    (hα_open : Topology.IsOpenEmbedding α.base)
    (hα_stalk : ∀ q, Function.Surjective (α.stalkMap q)) :
    IsNoetherianRing R := by
  obtain ⟨m, hm⟩ := exists_ideal_pow_le_ker_homSpfGlobalMap α
  let K := IsAdicRing.ideal C ^ (m + 1)
  let ψbar := homSpfQuotientLift α hm
  let φ : CommRingCat.of (C ⧸ K) ⟶ CommRingCat.of R := CommRingCat.ofHom ψbar
  let g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (C ⧸ K)) := Spec.map φ
  have hopen : Topology.IsOpenEmbedding (PrimeSpectrum.comap ψbar) :=
    isOpenEmbedding_comap_quotientLift α hα_open hm
  have hpre : IsPreimmersion g :=
    { isEmbedding := hopen.isEmbedding
      stalkMap_surjective := surjective_specMap_stalkMap_quotientLift α hα_stalk hm }
  let W : (Spec (CommRingCat.of (C ⧸ K))).Opens := ⟨Set.range g, hopen.isOpen_range⟩
  let g' : Spec (CommRingCat.of R) ⟶ (W : Scheme) :=
    AlgebraicGeometry.IsOpenImmersion.lift W.ι g (by rw [W.range_ι]; exact Set.Subset.rfl)
  have hfac : g' ≫ W.ι = g := AlgebraicGeometry.IsOpenImmersion.lift_fac W.ι g _
  have : IsPreimmersion (g' ≫ W.ι) := hfac.symm ▸ hpre
  have : IsPreimmersion g' := IsPreimmersion.of_comp g' W.ι
  have hsurj : Set.range g' = Set.univ := by
    ext y
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, W.ι.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun t : Spec (CommRingCat.of R) ⟶ _ ↦ t x) hfac).trans hx
  have : IsClosedImmersion g' := IsClosedImmersion.of_isPreimmersion g' (hsurj ▸ isClosed_univ)
  have : AlgebraicGeometry.IsLocallyNoetherian (Spec (CommRingCat.of R)) :=
    LocallyOfFiniteType.isLocallyNoetherian g'
  exact (isLocallyNoetherian_Spec (R := CommRingCat.of R)).mp inferInstance

private theorem isOpenEmbedding_and_stalkMap_surjective_lift {X Y Z : LocallyRingedSpace.{u}}
    (j : Y ⟶ Z) [hj : LocallyRingedSpace.IsOpenImmersion j] (β : X ⟶ Z)
    (hβ_open : Topology.IsOpenEmbedding β.base)
    (hβ_stalk : ∀ x, Function.Surjective (β.stalkMap x))
    (hrange : Set.range β.base ⊆ Set.range j.base) :
    Topology.IsOpenEmbedding (LocallyRingedSpace.IsOpenImmersion.lift j β hrange).base ∧
      ∀ x, Function.Surjective
        ((LocallyRingedSpace.IsOpenImmersion.lift j β hrange).stalkMap x) := by
  let α := LocallyRingedSpace.IsOpenImmersion.lift j β hrange
  have hfac : α ≫ j = β := LocallyRingedSpace.IsOpenImmersion.lift_fac j β hrange
  have hcomp_base : j.base ∘ α.base = β.base := funext fun x ↦ congrArg (fun t ↦ t.base x) hfac
  have hα_emb : Topology.IsEmbedding α.base :=
    hj.base_open.isEmbedding.of_comp_iff.mp (hcomp_base.symm ▸ hβ_open.isEmbedding)
  have hα_range : Set.range α.base = j.base ⁻¹' Set.range β.base :=
    LocallyRingedSpace.IsOpenImmersion.lift_range j β hrange
  refine ⟨(Topology.isOpenEmbedding_iff _).mpr
    ⟨hα_emb, hα_range ▸ hβ_open.isOpen_range.preimage j.base.hom.continuous⟩, fun x z ↦ ?_⟩
  have hfac_surj : Function.Surjective ((α ≫ j).stalkMap x) := hfac.symm ▸ hβ_stalk x
  obtain ⟨w, hw⟩ := hfac_surj z
  exact ⟨j.stalkMap (α.base x) w,
    (ConcreteCategory.congr_hom (PresheafedSpace.stalkMap.comp α.toHom j.toHom x) w).symm.trans hw⟩

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
    (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) (show y ∈ V from hqy)
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
  have hβ_stalk (x : PrimeSpectrum R) : Function.Surjective (β.stalkMap x) := by
    have hcomp := PresheafedSpace.stalkMap.comp
      (Scheme.forgetToLocallyRingedSpace.map ιg).toHom qJ.toHom x
    intro z
    obtain ⟨w, hw⟩ := ((ιg.stalkMap_surjective x).comp
      (Spf.fromSpecQuotient_stalk_surjective hJ (ιg x))) z
    exact ⟨w, (ConcreteCategory.congr_hom hcomp w).trans hw⟩
  obtain ⟨hα_open, hα_stalk⟩ :=
    isOpenEmbedding_and_stalkMap_surjective_lift j β hβ_open hβ_stalk hrange
  exact ⟨g, hyg, isNoetherianRing_of_openEmbedding_hom_spf _ hα_open hα_stalk⟩

/-- For an adic ring `A`, the affine formal scheme `ofSpf A` is locally noetherian if and only if
`A` is a noetherian ring (EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem ofSpf_isLocallyNoetherian_iff (A : Type u) [CommRing A] [TopologicalSpace A]
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
    obtain ⟨y, hy⟩ := hSsub s.2
    exact hy ▸ hnoeth y
  exact Ideal.isNoetherianRing_of_isAdicComplete J hJfg

/-- For an adic ring `A`, `ofSpf A` is noetherian if and only if `A` is a noetherian ring
(EGA I, Ch. I, 10.6.5). -/
@[simp]
theorem ofSpf_isNoetherian_iff (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsAdicRing A] :
    (ofSpf A).IsNoetherian ↔ IsNoetherianRing A := by
  have hc : CompactSpace (ofSpf A) := inferInstance
  rw [isNoetherian_iff, ofSpf_isLocallyNoetherian_iff, and_iff_left hc]

end ConverseAffine

section AffineOpensAndTopology

/-- On a locally noetherian formal scheme `X`, the topologized section ring `hU.Sections` over any
affine formal open `U` is a noetherian ring (EGA I, Ch. I, 10.6.5). -/
instance IsAffineOpen.isNoetherianRing_sections {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : IsNoetherianRing hU.Sections :=
  (ofSpf_isLocallyNoetherian_iff hU.Sections).mp
    ((isLocallyNoetherian_congr hU.isoSpf).mp inferInstance)

/-- On a locally noetherian formal scheme `X`, `Γ(U, O_X)` is a noetherian ring for every affine
formal open `U` (EGA I, Ch. I, 10.6.5). -/
theorem IsAffineOpen.isNoetherianRing {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : IsNoetherianRing (X.presheaf.obj (op U)) :=
  isNoetherianRing_of_ringEquiv hU.Sections hU.sectionsRingEquiv

/-- On a locally noetherian formal scheme `X`, every affine formal open is a noetherian topological
space. -/
theorem IsAffineOpen.noetherianSpace {X : FormalScheme} [X.IsLocallyNoetherian]
    {U : Opens X} (hU : X.IsAffineOpen U) : NoetherianSpace U := by
  have : NoetherianSpace
      (LocallyRingedSpace.forgetToTop.obj
        (forgetToLocallyRingedSpace.obj (ofSpf hU.Sections))) :=
    noetherianSpace_ofSpf hU.Sections
  let h := TopCat.homeoOfIso
    (LocallyRingedSpace.forgetToTop.mapIso (forgetToLocallyRingedSpace.mapIso hU.isoSpf))
  exact (noetherianSpace_iff_of_homeomorph h).mpr inferInstance

/-- A formal scheme `X` is locally noetherian if and only if `Γ(U, O_X)` is a noetherian ring for
every affine formal open `U` of `X`. -/
theorem isLocallyNoetherian_iff_forall_isAffineOpen (X : FormalScheme) :
    X.IsLocallyNoetherian ↔
      ∀ (U : Opens X), X.IsAffineOpen U → IsNoetherianRing (X.presheaf.obj (op U)) := by
  refine ⟨fun _ U hU ↦ hU.isNoetherianRing, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨U, hU, hx, _⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : Opens X) from trivial)
  have hU' : X.IsAffineOpen U := hU
  have : IsNoetherianRing (X.presheaf.obj (op U)) := h U hU'
  have : IsNoetherianRing hU'.Sections :=
    isNoetherianRing_of_ringEquiv _ hU'.sectionsRingEquiv.symm
  let f : Spf hU'.Sections ⟶ X.toLocallyRingedSpace := forgetToLocallyRingedSpace.map hU'.fromSpf
  have hf : LocallyRingedSpace.IsOpenImmersion f := hU'.isOpenImmersion_fromSpf
  refine ⟨hU'.Sections, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    f, hf, ?_⟩
  -- `f` is definitionally `forgetToLocallyRingedSpace.map hU'.fromSpf`.
  change x ∈ Set.range (forgetToLocallyRingedSpace.map hU'.fromSpf).base
  rwa [hU'.range_fromSpf]

/-- If `X` is covered by affine formal opens with noetherian section rings, then `X` is locally
noetherian. -/
theorem isLocallyNoetherian_of_iSup_eq_top {X : FormalScheme} {ι : Type*} {U : ι → Opens X}
    (hU : ∀ i, X.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (hnoeth : ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i)))) :
    X.IsLocallyNoetherian where
  exists_noetherian_spf x := by
    have hxtop : x ∈ ⨆ i, U i := by
      rw [hcov]
      trivial
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxtop
    have : IsNoetherianRing (X.presheaf.obj (op (U i))) := hnoeth i
    have : IsNoetherianRing (hU i).Sections :=
      isNoetherianRing_of_ringEquiv _ (hU i).sectionsRingEquiv.symm
    let f : Spf (hU i).Sections ⟶ X.toLocallyRingedSpace :=
      forgetToLocallyRingedSpace.map (hU i).fromSpf
    have hf : LocallyRingedSpace.IsOpenImmersion f := (hU i).isOpenImmersion_fromSpf
    refine ⟨(hU i).Sections, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, f, hf, ?_⟩
    -- `f` is definitionally `forgetToLocallyRingedSpace.map (hU i).fromSpf`.
    change x ∈ Set.range (forgetToLocallyRingedSpace.map (hU i).fromSpf).base
    rwa [(hU i).range_fromSpf]

/-- Every noetherian formal scheme has a noetherian underlying topological space. -/
instance IsNoetherian.noetherianSpace (X : FormalScheme) [X.IsNoetherian] :
    NoetherianSpace X := by
  have hcov : (⋃ (U : {V : Opens X // X.IsAffineOpen V}), (U.1 : Set X)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨U, hU, hx, _⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : Opens X) from trivial)
    exact ⟨⟨U, hU⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun (U : {V : Opens X // X.IsAffineOpen V}) ↦ (U.1 : Set X))
    (fun U ↦ U.1.isOpen) (hcov.symm ▸ Set.Subset.rfl)
  have hU_eq : (⋃ i : s, (i.1.1 : Set X)) = Set.univ := by
    refine Set.Subset.antisymm (Set.subset_univ _) (hs.trans fun z hz ↦ ?_)
    obtain ⟨i, his, hzi⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion.mpr ⟨⟨i, his⟩, hzi⟩
  have hnoeth (i : s) : NoetherianSpace (i.1.1 : Set X) := i.1.2.noetherianSpace
  exact TopologicalSpace.noetherian_univ_iff.mp
    (hU_eq ▸ TopologicalSpace.NoetherianSpace.iUnion (fun i : s ↦ (i.1.1 : Set X)))

/-- A locally noetherian formal scheme with noetherian underlying space is noetherian. -/
theorem isNoetherian_of_noetherianSpace (X : FormalScheme) [X.IsLocallyNoetherian]
    [NoetherianSpace X] : X.IsNoetherian :=
  have : CompactSpace X := TopologicalSpace.NoetherianSpace.compactSpace X
  ⟨⟩

/-- A formal scheme is noetherian if and only if it is covered by finitely many affine formal
opens with noetherian section rings. -/
theorem isNoetherian_iff_exists_finite_affine_cover (X : FormalScheme) :
    X.IsNoetherian ↔
      ∃ (n : ℕ) (U : Fin n → Opens X), (∀ i, X.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ ∧
        ∀ i, IsNoetherianRing (X.presheaf.obj (op (U i))) := by
  constructor
  · intro _
    have hcov : (⋃ (U : {V : Opens X // X.IsAffineOpen V}), (U.1 : Set X)) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      obtain ⟨U, hU, hx, _⟩ :=
        (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : Opens X) from trivial)
      exact ⟨⟨U, hU⟩, hx⟩
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun (U : {V : Opens X // X.IsAffineOpen V}) ↦ (U.1 : Set X))
      (fun U ↦ U.1.isOpen) (hcov.symm ▸ Set.Subset.rfl)
    let e := s.equivFin
    refine ⟨s.card, fun i ↦ (e.symm i).1.1, fun i ↦ (e.symm i).1.2, ?_,
      fun i ↦ (e.symm i).1.2.isNoetherianRing⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨e ⟨U, hUs⟩, by simpa using hxU⟩
  · rintro ⟨n, U, hU, hcov, hnoeth⟩
    have : X.IsLocallyNoetherian := isLocallyNoetherian_of_iSup_eq_top hU hcov hnoeth
    have hcomp : IsCompact (Set.univ : Set X) := by
      have huniv : (Set.univ : Set X) = ⋃ i, (U i : Set X) := by
        ext x
        simp [← Opens.mem_iSup, hcov]
      rw [huniv]
      exact isCompact_iUnion fun i ↦ (hU i).isCompact
    have : CompactSpace X := isCompact_univ_iff.mp hcomp
    exact ⟨⟩

end AffineOpensAndTopology

section OfScheme

/-- An ordinary scheme `Y` is locally noetherian as a formal scheme if and only if it is locally
noetherian as a scheme. -/
@[simp]
theorem toFormalScheme_isLocallyNoetherian_iff (Y : Scheme.{u}) :
    Y.toFormalScheme.IsLocallyNoetherian ↔ AlgebraicGeometry.IsLocallyNoetherian Y := by
  rw [isLocallyNoetherian_iff_forall_isAffineOpen]
  constructor
  · intro h
    refine ⟨fun U ↦ ?_⟩
    exact h U.1 ((isAffineOpen_toFormalScheme_iff Y U.1).mpr U.2)
  · intro h U hU
    exact AlgebraicGeometry.IsLocallyNoetherian.component_noetherian
      ⟨U, (isAffineOpen_toFormalScheme_iff Y U).mp hU⟩

instance toFormalScheme_isLocallyNoetherian (Y : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian Y] : Y.toFormalScheme.IsLocallyNoetherian :=
  (toFormalScheme_isLocallyNoetherian_iff Y).mpr inferInstance

/-- An ordinary scheme `Y` is noetherian as a formal scheme if and only if it is noetherian as a
scheme. -/
@[simp]
theorem toFormalScheme_isNoetherian_iff (Y : Scheme.{u}) :
    Y.toFormalScheme.IsNoetherian ↔ AlgebraicGeometry.IsNoetherian Y := by
  rw [isNoetherian_iff, AlgebraicGeometry.isNoetherian_iff, toFormalScheme_isLocallyNoetherian_iff]
  rfl

instance toFormalScheme_isNoetherian (Y : Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y] :
    Y.toFormalScheme.IsNoetherian :=
  (toFormalScheme_isNoetherian_iff Y).mpr inferInstance

end OfScheme

end TauCeti.FormalScheme
