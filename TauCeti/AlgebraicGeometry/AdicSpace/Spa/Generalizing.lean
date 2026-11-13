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
(`TauCeti.ValuationSpectrum.IsContinuous.supp_eq_of_specializes`, in `Spa/Analytic.lean`).
Vertical generizations lift along any ring map to coarsenings
(`TauCeti.ValuationSpectrum.comap_ofValuation_coarsenByUnits_eq`). The coarsening is by a proper
convex subgroup of the value group, because the generization is again analytic, so it is again
continuous (`Valuation.IsContinuous.coarsenByUnits_restrict`), and it stays bounded by `1` on
`B⁺`.

## Main results

* `TauCeti.Huber.Pair.Hom.generalizingMap_spaComap_of_isTateRing`: a morphism of Huber pairs out
  of a Tate pair induces a generalizing map of adic spectra.
* `TauCeti.Huber.Pair.Hom.isQuotientMap_spaComap_of_isTateRing`: if it is moreover surjective, it
  is a quotient map.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 7.11 (coarsenings of
  continuous valuations) and Remark 7.40 (analytic points).
-/

public section

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
    -- coarsening by `⊤` collapses every nonzero value to `1`, so `x(1) ≤ x(t)`
    have hle : x.1.valuation 1 ≤ x.1.valuation t := by
      rw [← hH, valuation_le_iff, comap_vle, vle_ofValuation, coarsenByUnits_apply,
        coarsenByUnits_apply]
      simpa using (coarsenMapOfValueGroup_le_iff ⊤ one_ne_zero htx).mpr
        (Or.inr ConvexSubgroup.mem_top)
    exact (map_one x.1.valuation ▸ hle).not_gt hlt
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
