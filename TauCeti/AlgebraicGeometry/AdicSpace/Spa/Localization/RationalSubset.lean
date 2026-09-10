/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Homeomorph

/-!
# Rational subsets under a localization homeomorphism

Let `S` be a localization of `A` at a submonoid `M`. Every finite family of elements of `S` has a
common denominator in `M`. Multiplying all the numerators and the denominator of a rational subset
by that common denominator does not change the subset, because the multiplier is a unit. Thus
every rational subset of `Spa(S, S⁺)` is cut out by elements coming from `A`.

This is the algebraic denominator-clearing part of Wedhorn Proposition 8.2(2), that a rational
subset of a rational subset is rational in the original adic spectrum. Combined with the
homeomorphism

```text
Spa(A(T/s), A(T/s)⁺) ≃ R(T/s),
```

it says that any rational subset on the left is the inverse image of a basic rational locus in
`Spa(A, A⁺)`. To obtain Proposition 8.2(2) in full, one must still prove that this basic locus has
an admissible finite presentation in `A` and pass from `A(T/s)` to the completed localization
`A⟨T/s⟩`.

## Main results

* `TauCeti.ValuationSpectrum.exists_comap_preimage_basicOpenFinset_eq`: a rational open over a
  localization is the pullback of one presented by elements of the source ring.
* `TauCeti.ValuationSpectrum.exists_comap_preimage_rationalSubset_inter_spa_eq`: the same for
  rational subsets, after cutting the pullback down to the target adic spectrum.
* `TauCeti.ValuationSpectrum.exists_spaLocalizationHomeomorph_preimage_rationalSubset_eq`: the
  same statement through the localization homeomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], arXiv:1910.05934v1, Proposition 8.2(2).
* For simultaneous denominator clearing in a localization, see Mathlib's
  `IsLocalization.commonDenomOfFinset`, `IsLocalization.finsetIntegerMultiple`, and
  `IsLocalization.finsetIntegerMultiple_image`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- **Clear denominators in a rational open of a localization.** If `S` is a localization of `A`
at a submonoid `M`, then every rational open `Spv(S)(U/q)` is the pullback of one presented by a
finite family in `A`.

No topological admissibility is asserted for the resulting numerator family in `A`. Establishing
that extra property is the remaining topological-algebra step in Wedhorn Proposition 8.2(2). -/
theorem exists_comap_preimage_basicOpenFinset_eq (M : Submonoid A) [IsLocalization M S]
    (U : Finset S) (q : S) :
    ∃ (V : Finset A) (r : A),
      comap (algebraMap A S) ⁻¹' basicOpenFinset V r = basicOpenFinset U q := by
  classical
  set d : S := algebraMap A S (IsLocalization.commonDenomOfFinset M (insert q U) : A) with hd
  have hnum (x : ↥(insert q U)) :
      algebraMap A S (IsLocalization.integerMultiple M (insert q U) id x) = (x : S) * d := by
    rw [IsLocalization.map_integerMultiple, Submonoid.smul_def, Algebra.smul_def, hd]
    exact mul_comm _ _
  have hV : (IsLocalization.finsetIntegerMultiple M (insert q U)).image (algebraMap A S)
      = (insert q U).image fun x ↦ x * d := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_image, IsLocalization.finsetIntegerMultiple_image,
      ← Set.image_smul]
    exact Set.image_congr' fun x ↦ by rw [Submonoid.smul_def, Algebra.smul_def, hd]; ring
  refine ⟨IsLocalization.finsetIntegerMultiple M (insert q U),
    IsLocalization.integerMultiple M (insert q U) id ⟨q, Finset.mem_insert_self q U⟩, ?_⟩
  rw [comap_preimage_basicOpenFinset, hV, hnum ⟨q, Finset.mem_insert_self q U⟩,
    basicOpenFinset_image_mul_right _ _ _ (IsLocalization.map_units S _),
    basicOpenFinset_insert_self]

/-- **Clear denominators in a rational subset of a localization.** If `S` is a localization of
`A` at a submonoid `M`, then every rational subset of `Spa(S, S⁺)` is the trace on `Spa(S, S⁺)`
of the pullback of a basic rational locus presented by a finite family in `A`. -/
theorem exists_comap_preimage_rationalSubset_inter_spa_eq [TopologicalSpace A]
    [TopologicalSpace S] (M : Submonoid A) [IsLocalization M S] (Aplus : Subring A)
    (Bplus : Subring S) (hcont : Continuous (algebraMap A S))
    (hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus) (U : Finset S) (q : S) :
    ∃ (V : Finset A) (r : A),
      comap (algebraMap A S) ⁻¹' rationalSubset Aplus V r ∩ spa Bplus =
        rationalSubset Bplus U q := by
  obtain ⟨V, r, hVr⟩ := exists_comap_preimage_basicOpenFinset_eq M U q
  refine ⟨V, r, ?_⟩
  rw [comap_preimage_basicOpenFinset] at hVr
  rw [comap_preimage_rationalSubset_inter_spa _ hcont hplus,
    rationalSubset_def, rationalSubset_def, hVr]

/-- **Rational subsets through the topological-localization homeomorphism.** Every rational
subset of `Spa(A(T/s), A(T/s)⁺)` is the inverse image, under the canonical homeomorphism with
`R(T/s)`, of the restriction of a basic rational locus from `Spa(A, A⁺)`.

This is the denominator-clearing part of Wedhorn Proposition 8.2(2). The statement deliberately
does not call the locus on the right a rational *subset* of `Spa(A, A⁺)`: that additionally asks
that its numerator ideal be open, which is a separate input not proved here. -/
theorem exists_spaLocalizationHomeomorph_preimage_rationalSubset_eq
    [TopologicalSpace A] [IsTopologicalRing A]
    (P : PairOfDefinition A) (Aplus : Subring A) (hP : P.ringOfDefinition ≤ Aplus)
    (T : Finset A) (s : A) [IsLocalization.Away s S]
    (hden : HasDenominatorPower P T s S)
    (U : Finset S) (q : S) :
    letI := locTopology P T s S hden
    ∃ (V : Finset A) (r : A),
      spaLocalizationHomeomorph P Aplus hP T s S hden ⁻¹'
          ((fun v ↦ (v.1 : spa Aplus).1) ⁻¹' rationalSubset Aplus V r) =
        Subtype.val ⁻¹' rationalSubset
          (integralClosure ↥(Algebra.adjoin Aplus
            (Set.range fun t : T ↦
              (TauCeti.Localization.divBy (t : A) s : S))) S).toSubring U q := by
  classical
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  let Bplus := (integralClosure ↥(Algebra.adjoin Aplus
    (Set.range fun t : T ↦ (TauCeti.Localization.divBy (t : A) s : S))) S).toSubring
  have hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus := fun a ha ↦
    Subalgebra.algebraMap_mem (integralClosure _ S)
      (⟨_, Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus)⟩ :
        ↥(Algebra.adjoin Aplus
          (Set.range fun t : T ↦ (TauCeti.Localization.divBy (t : A) s : S))))
  obtain ⟨V, r, hVr⟩ := exists_comap_preimage_rationalSubset_inter_spa_eq (Submonoid.powers s)
    Aplus Bplus (continuous_algebraMap_locTopology P T s S hden) hplus U q
  have himage : rationalSubset Bplus (V.image (algebraMap A S)) (algebraMap A S r) =
      rationalSubset Bplus U q := by
    rw [← comap_preimage_rationalSubset_inter_spa (algebraMap A S)
      (continuous_algebraMap_locTopology P T s S hden) hplus]
    exact hVr
  refine ⟨V, r, Set.ext fun v ↦ ?_⟩
  rw [Set.mem_preimage, Set.mem_preimage, spaLocalizationHomeomorph_apply_val, ← himage]
  simpa only [Set.mem_preimage, spaComap_val] using
    Set.ext_iff.mp (spaComap_preimage_rationalSubset (algebraMap A S)
      (continuous_algebraMap_locTopology P T s S hden) Aplus Bplus hplus V r) v

end TauCeti.ValuationSpectrum

end
