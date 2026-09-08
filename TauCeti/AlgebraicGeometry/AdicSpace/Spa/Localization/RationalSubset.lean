/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Localization.Homeomorph

/-!
# Rational subsets under a localization homeomorphism

Let `S` be a localization of `A` away from `s`. Every finite family of elements of `S` has a
common denominator which is a power of `s`. Multiplying all the numerators and the denominator of
a rational subset by that common denominator does not change the subset, because the multiplier is
a unit. Thus every rational subset of `Spa(S, S⁺)` is cut out by elements coming from `A`.

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

* `TauCeti.ValuationSpectrum.exists_comap_preimage_rationalSubset_eq`: a rational subset over a
  localization is the pullback of one presented by elements of the source ring.
* `TauCeti.ValuationSpectrum.exists_spaLocalizationHomeomorph_preimage_rationalSubset_eq`: the
  same statement through the localization homeomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], arXiv:1910.05934v1, Proposition 8.2(2).

## Provenance

The proof uses Mathlib's `IsLocalization.Away.sec`, which chooses a numerator and denominator
exponent for each element of a localization. No external formalization was used.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- **Clear denominators in a rational subset of a localization.** If `S` is a localization of
`A` away from `s`, then every rational subset of `Spa(S, S⁺)` is the pullback of a basic rational
locus presented by a finite family in `A`.

No topological admissibility is asserted for the resulting numerator family in `A`. Establishing
that extra property is the remaining topological-algebra step in Wedhorn Proposition 8.2(2). -/
theorem exists_comap_preimage_rationalSubset_eq [TopologicalSpace A] [TopologicalSpace S]
    (s : A) [IsLocalization.Away s S] (Aplus : Subring A) (Bplus : Subring S)
    (hcont : Continuous (algebraMap A S))
    (hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus) (U : Finset S) (q : S) :
    ∃ (V : Finset A) (r : A),
      comap (algebraMap A S) ⁻¹' rationalSubset Aplus V r ∩ spa Bplus =
        rationalSubset Bplus U q := by
  classical
  obtain ⟨n, a, hclear⟩ := exists_finset_mul_pow_eq_algebraMap s (insert q U)
  let d : S := algebraMap A S s ^ n
  let V : Finset A := U.image a
  let r : A := a q
  have hq : q * d = algebraMap A S r := hclear q (Finset.mem_insert_self q U)
  have hV : V.image (algebraMap A S) = U.image fun u ↦ u * d := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨u, hu, by
        simpa only [d] using hclear u (Finset.mem_insert_of_mem hu)⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨a u, Finset.mem_image_of_mem a hu,
        by simpa only [d] using (hclear u (Finset.mem_insert_of_mem hu)).symm⟩
  refine ⟨V, r, ?_⟩
  rw [comap_preimage_rationalSubset_inter_spa (algebraMap A S) hcont hplus]
  rw [hV, ← hq, rationalSubset_image_mul_right Bplus U q d
    (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit s))]

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
  let _ := locTopology P T s S hden
  have _ := isTopologicalRing_locTopology P T s S hden
  let Bplus := (integralClosure ↥(Algebra.adjoin Aplus
    (Set.range fun t : T ↦ (TauCeti.Localization.divBy (t : A) s : S))) S).toSubring
  have hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus := fun a ha ↦
    Subalgebra.algebraMap_mem (integralClosure _ S)
      (⟨_, Subalgebra.algebraMap_mem _ (⟨a, ha⟩ : Aplus)⟩ :
        ↥(Algebra.adjoin Aplus
          (Set.range fun t : T ↦ (TauCeti.Localization.divBy (t : A) s : S))))
  obtain ⟨V, r, hVr⟩ := exists_comap_preimage_rationalSubset_eq s Aplus Bplus
    (continuous_algebraMap_locTopology P T s S hden) hplus U q
  refine ⟨V, r, Set.ext fun v ↦ ?_⟩
  have hpoint := Set.ext_iff.mp hVr v.1
  rw [Set.mem_preimage, Set.mem_preimage, spaLocalizationHomeomorph_apply_val]
  change comap (algebraMap A S) v.1 ∈ rationalSubset Aplus V r ↔
    v.1 ∈ rationalSubset Bplus U q
  exact ⟨fun hv ↦ hpoint.mp ⟨hv, v.2⟩, fun hv ↦ (hpoint.mpr hv).1⟩

end TauCeti.ValuationSpectrum

end
