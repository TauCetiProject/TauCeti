/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.MorphismSpectral
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Spectral
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.VerticalGeneralization
public import TauCeti.Topology.Spectral.ProConstructible
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Morphisms of adic spectra out of a Tate pair are generalizing

Let `f : (A, A⁺) → (B, B⁺)` be a morphism of Huber pairs with `A` a Tate ring. This file shows that
`Spa(B, B⁺) → Spa(A, A⁺)` lifts generizations
(`TauCeti.Huber.Pair.Hom.generalizingMap_spaComap_of_isTateRing`). Since the map is spectral, it is
then a quotient map as soon as it is surjective
(`TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`).

Over a Tate ring every generization in `Spa(A, A⁺)` is vertical: a continuous point that
specializes to an analytic point has the same support
(`TauCeti.ValuationSpectrum.IsContinuous.supp_eq_of_specializes`). Vertical generizations lift
along any ring map to coarsenings
(`TauCeti.ValuationSpectrum.comap_ofValuation_coarsenByUnits_eq`). The coarsening is by a proper
convex subgroup of the value group, because the generization is again analytic, so it is again
continuous (`Valuation.IsContinuous.coarsenByUnits_restrict`), and it stays bounded by `1` on
`B⁺`.

## Main results

* `TauCeti.ValuationSpectrum.IsContinuous.supp_eq_of_specializes`: a continuous point that
  specializes to an analytic point has the same support.
* `TauCeti.Huber.Pair.Hom.generalizingMap_spaComap_of_isTateRing`: a morphism of Huber pairs out
  of a Tate pair induces a generalizing map of adic spectra.
* `TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`: if it is moreover surjective, it
  is a quotient map.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.11 (coarsenings of
  continuous valuations) and Remark 7.40 (analytic points).
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **Generizations of analytic points are vertical.** A continuous point `x` of `Spv A` that
specializes to an analytic point `x'` has the same support. -/
theorem IsContinuous.supp_eq_of_specializes {x x' : Spv A} (hx : x.IsContinuous)
    (hx' : IsAnalyticPoint x') (h : x ⤳ x') : x.supp = x'.supp := by
  obtain ⟨t, ht, htx'⟩ :=
    (isAnalyticPoint_iff_exists_isTopologicallyNilpotent_notMem_supp x').mp hx'
  refine le_antisymm (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · -- an element vanishing at `x` vanishes at its specialization
    rw [mem_supp_iff] at ha ⊢
    by_contra hax'
    exact ((mem_basicOpen_iff _ _ _).mp (h.mem_open (isOpen_basicOpen a a)
      ((mem_basicOpen_iff _ _ _).mpr ⟨x'.toValuativeRel.vle_refl a, hax'⟩))).2 ha
  · -- `x'(a) = 0 ≤ x'(tⁿ) ≠ 0` gives `x(a) ≤ x(t)ⁿ` for all `n`, so `x(a) = 0` by continuity
    rw [mem_supp_iff] at ha ⊢
    by_contra hax
    have hpos : x.valuation 0 < x.valuation a := by
      rwa [valuation_lt_iff]
    obtain ⟨n, hn⟩ := exists_pow_lt_of_isTopologicallyNilpotent (v := x.valuation)
      ((Valuation.isContinuous_def.mp ((ValuationSpectrum.isContinuous_def x).mp hx) a).mem_nhds
        hpos) ht
    have htn : ¬ x'.toValuativeRel.vle (t ^ n) 0 := fun htn ↦
      htx' ((inferInstance : x'.supp.IsPrime).mem_of_pow_mem n ((mem_supp_iff _ _).mpr htn))
    have hle := ((mem_basicOpen_iff _ _ _).mp (h.mem_open (isOpen_basicOpen a (t ^ n))
      ((mem_basicOpen_iff _ _ _).mpr
        ⟨x'.toValuativeRel.vle_trans ha (@ValuativeRel.zero_vle A _ x'.toValuativeRel _), htn⟩))).1
    rw [← valuation_le_iff, map_pow] at hle
    exact hle.not_gt hn

end TauCeti.ValuationSpectrum

namespace TauCeti.Huber.Pair.Hom

open ValuationSpectrum Valuation

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A}
  {T : Pair B}

/-- **Morphisms out of a Tate pair lift generizations.** For a morphism of Huber pairs
`f : (A, A⁺) → (B, B⁺)` with `A` a Tate ring, every generization of the image of a point `y` of
`Spa(B, B⁺)` is the image of a generization of `y`. -/
theorem generalizingMap_spaComap_of_isTateRing (f : Hom S T) : GeneralizingMap f.spaComap := by
  intro y x h
  have hxy : x.1 ⤳ comap f.toRingHom y.1 := by
    rw [← spaComap_val]
    exact h.map continuous_subtype_val
  have hxc : x.1.IsContinuous := ((mem_spa_iff _ _).mp x.2).1
  have hsupp := hxc.supp_eq_of_specializes (isAnalyticPoint_of_isTateRing _) hxy
  set v := y.1.valuation
  have hy : ofValuation v.restrict = y.1 :=
    (ofValuation_eq_of_isEquiv v.isEquiv_restrict.symm).trans (ofValuation_valuation y.1)
  rw [← hy] at hxy hsupp
  obtain ⟨H, hH⟩ := comap_ofValuation_coarsenByUnits_eq hxy hsupp
  -- the convex subgroup is proper, since `x` takes a value strictly between `0` and `1`
  have hHtop : H ≠ ⊤ := by
    rintro rfl
    obtain ⟨t, ht, htx⟩ := (isAnalyticPoint_iff_exists_isTopologicallyNilpotent_notMem_supp
      x.1).mp (isAnalyticPoint_of_isTateRing _)
    have hlt : x.1.valuation t < 1 :=
      ((ValuationSpectrum.isContinuous_def _).mp hxc).lt_one_of_isTopologicallyNilpotent ht
    rw [hsupp, supp_comap, supp_ofValuation, Ideal.mem_comap, Valuation.mem_supp_iff] at htx
    have hle := (coarsenMapOfValueGroup_le_iff ⊤ 1 (Units.mk0 _ htx)).mpr
      (Or.inr ConvexSubgroup.mem_top)
    rw [Units.val_one, Units.val_mk0, ← map_one v.restrict, ← map_one f.toRingHom,
      ← coarsenByUnits_apply, ← coarsenByUnits_apply, ← vle_ofValuation, ← comap_vle, hH,
      ← valuation_le_iff, map_one] at hle
    exact hle.not_gt hlt
  have hvc : v.IsContinuous :=
    (ValuationSpectrum.isContinuous_def _).mp ((mem_spa_iff _ _).mp y.2).1
  have hmem : ofValuation (v.restrict.coarsenByUnits H) ∈ spa T.plus := by
    refine (mem_spa_iff _ _).mpr ⟨(isContinuous_ofValuation_iff _).mpr
      (hvc.coarsenByUnits_restrict hHtop), fun b hb ↦ ?_⟩
    rw [vle_ofValuation, coarsenByUnits_apply, coarsenByUnits_apply]
    exact coarsenMapOfValueGroup_monotone H
      (v.restrict_le_iff.mpr (by rw [map_one]; exact valuation_le_one_of_mem_spa y.2 hb))
  refine ⟨⟨_, hmem⟩, Topology.IsInducing.subtypeVal.specializes_iff.mp ?_, Subtype.ext ?_⟩
  · have hsp := ofValuation_coarsenByUnits_specializes v.restrict H
    rwa [hy] at hsp
  · rw [spaComap_val]
    exact hH

/-- **Surjective morphisms out of a Tate pair are quotient maps on adic spectra.** If
`f : (A, A⁺) → (B, B⁺)` is a morphism of Huber pairs with `A` a Tate ring and `Spa(f)` is
surjective, then `Spa(A, A⁺)` carries the quotient topology of `Spa(B, B⁺)`. -/
theorem isQuotientMap_spaComap_of_isTateRing (f : Hom S T)
    (hf : Function.Surjective f.spaComap) : Topology.IsQuotientMap f.spaComap :=
  f.isSpectralMap_spaComap_of_isTateRing.isQuotientMap_of_generalizingMap
    f.generalizingMap_spaComap_of_isTateRing hf

end TauCeti.Huber.Pair.Hom
