/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Away localizations of absolutely integrally closed subrings

This file characterizes the localization away from an element x of an absolutely integrally
closed subring S of a commutative ring K as the smallest absolutely integrally closed subring
containing S and an inverse y of x.

## Main results

* TauCeti.IsAbsolutelyIntegrallyClosed.isLocalization_away_of_minimal: if S and T are
  subrings of a commutative ring K with S absolutely integrally closed, T an S-algebra
  compatible with the inclusion into K, x : S and y ∈ T with (x : K) * y = 1, and T is
  contained in every absolutely integrally closed subring of K containing S and y, then T
  is the localization of S away from x.
* TauCeti.IsAbsolutelyIntegrallyClosed.isLocalization_away_integralClosure: when K is an
  integral domain and S : Subring K is absolutely integrally closed, the integral closure of
  S ⊔ Subring.closure {y} in K is the localization of S away from x whenever
  (x : K) * y = 1.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean
(New.Variety.IsAbsIntegrallyClosed.isLocalization_away), generalized from subrings of a field
with a Fact (S ≤ T) instance to arbitrary commutative rings and compatible S-algebra
structures.
-/

@[expose] public section

namespace TauCeti.IsAbsolutelyIntegrallyClosed

/-- Let S and T be subrings of a commutative ring K, with S absolutely integrally closed
and T an S-algebra whose structure map agrees with the inclusion into K. If x : S has an
inverse y ∈ T in K and T lies in every absolutely integrally closed subring of K
containing S and y, then T is the localization of S away from x. -/
theorem isLocalization_away_of_minimal {K : Type*} [CommRing K] {S T : Subring K} [Algebra S T]
    (hST : ∀ r : S, (algebraMap S T r : K) = r) [IsAbsolutelyIntegrallyClosed S] (x : S)
    {y : K} (hy : y ∈ T) (hxy : (x : K) * y = 1)
    (hmin : ∀ U : Subring K, IsAbsolutelyIntegrallyClosed U → S ≤ U → y ∈ U → T ≤ U) :
    IsLocalization.Away x T := by
  let φ := Localization.awayLift S.subtype x (.of_mul_eq_one y hxy)
  have hφ (r : S) : φ (algebraMap S _ r) = r := IsLocalization.Away.lift_eq x _ r
  have hy_mem : y ∈ φ.range := by
    refine ⟨IsLocalization.Away.invSelf x, ?_⟩
    calc φ (IsLocalization.Away.invSelf x)
        = φ (IsLocalization.Away.invSelf x) * ((x : K) * y) := by rw [hxy, mul_one]
      _ = φ (algebraMap S _ x * IsLocalization.Away.invSelf x) * y := by
          rw [map_mul, hφ, mul_left_comm, mul_assoc]
      _ = y := by rw [IsLocalization.Away.mul_invSelf, map_one, one_mul]
  have hS_le : S ≤ φ.range := fun r hr ↦ ⟨algebraMap S _ ⟨r, hr⟩, hφ ⟨r, hr⟩⟩
  have hT_le : T ≤ φ.range :=
    hmin φ.range (.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective) hS_le hy_mem
  refine IsLocalization.Away.mk x (.of_mul_eq_one ⟨y, hy⟩ (Subtype.ext ?_)) (fun z ↦ ?_)
    fun a b hab ↦ ⟨0, ?_⟩
  · simpa only [Subring.coe_mul, hST, Subring.coe_one] using hxy
  · obtain ⟨u, hu⟩ := hT_le z.property
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj x u
    refine ⟨n, r, Subtype.ext ?_⟩
    simp only [Subring.coe_mul, Subring.coe_pow, hST]
    rw [← hu, ← hφ x, ← map_pow, ← map_mul, hr, hφ]
  · simpa only [pow_zero, one_mul] using
      Subtype.ext (by simpa only [hST] using congrArg Subtype.val hab)

/-- If K is an integral domain, S is an absolutely integrally closed subring of K, and
(x : K) * y = 1 for x : S and y : K, then the integral closure of S ⊔ Subring.closure {y}
in K is the localization of S away from x. -/
theorem isLocalization_away_integralClosure {K : Type*} [CommRing K] [IsDomain K]
    {S : Subring K} [IsAbsolutelyIntegrallyClosed S] (x : S) {y : K} (hxy : (x : K) * y = 1)
    [Algebra S (_root_.integralClosure ↥(S ⊔ Subring.closure {y}) K).toSubring]
    (hST : ∀ r : S,
      (algebraMap S (_root_.integralClosure ↥(S ⊔ Subring.closure {y}) K).toSubring r : K) = r) :
    IsLocalization.Away x (_root_.integralClosure ↥(S ⊔ Subring.closure {y}) K).toSubring := by
  refine isLocalization_away_of_minimal hST x
    (algebraMap_mem (_root_.integralClosure ↥(S ⊔ Subring.closure {y}) K)
      ⟨y, (le_sup_right : Subring.closure {y} ≤ _) (Subring.subset_closure rfl)⟩)
    hxy fun U hU hSU hyU z hz ↦ ?_
  have hsub : S ⊔ Subring.closure {y} ≤ U :=
    sup_le hSU (Subring.closure_le.mpr (Set.singleton_subset_iff.mpr hyU))
  obtain ⟨p, hp, hpeval⟩ := hz
  have hsplit : (p.map (Subring.inclusion hsub)).Splits := hU.splits (hp.map _)
  have hroot : (p.map (Subring.inclusion hsub)).eval₂ U.subtype z = 0 := by
    rw [Polynomial.eval₂_map]
    exact hpeval
  obtain ⟨s, hs⟩ := Polynomial.splits_iff_exists_multiset.mp hsplit
  rw [hs, Polynomial.eval₂_mul, Polynomial.eval₂_C, (hp.map _).leadingCoeff, map_one, one_mul,
    Polynomial.eval₂_multiset_prod, Multiset.prod_eq_zero_iff] at hroot
  obtain ⟨q, hq, hqz⟩ := Multiset.mem_map.mp hroot
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hq
  have hza : z = a := by simpa [sub_eq_zero] using hqz
  exact hza ▸ a.property

end TauCeti.IsAbsolutelyIntegrallyClosed
