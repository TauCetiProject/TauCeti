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

* `TauCeti.ValuationSpectrum.exists_comap_preimage_rationalSubset_eq`: a rational subset over a
  localization is the pullback of one presented by elements of the source ring.
* `TauCeti.ValuationSpectrum.exists_spaLocalizationHomeomorph_preimage_rationalSubset_eq`: the
  same statement through the localization homeomorphism.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], arXiv:1910.05934v1, Proposition 8.2(2).

## Provenance

The proof uses Mathlib's `IsLocalization.commonDenomOfFinset` and
`IsLocalization.integerMultiple` to clear a finite family of denominators. No external
formalization was used.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber TauCeti.Huber.PairOfDefinition TauCeti.Localization

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

/-- **Clear denominators in a rational subset of a localization.** If `S` is a localization of
`A` at a submonoid `M`, then every rational subset of `Spa(S, S⁺)` is the pullback of a basic
rational locus presented by a finite family in `A`.

No topological admissibility is asserted for the resulting numerator family in `A`. Establishing
that extra property is the remaining topological-algebra step in Wedhorn Proposition 8.2(2). -/
theorem exists_comap_preimage_rationalSubset_eq [TopologicalSpace A] [TopologicalSpace S]
    (M : Submonoid A) [IsLocalization M S] (Aplus : Subring A) (Bplus : Subring S)
    (hcont : Continuous (algebraMap A S))
    (hplus : ∀ a ∈ Aplus, algebraMap A S a ∈ Bplus) (U : Finset S) (q : S) :
    ∃ (V : Finset A) (r : A),
      comap (algebraMap A S) ⁻¹' rationalSubset Aplus V r ∩ spa Bplus =
        rationalSubset Bplus U q := by
  classical
  -- Mathlib's `IsLocalization.commonDenom`/`integerMultiple` clear the finitely many
  -- denominators of `insert q U` simultaneously; only the packaged data is used below.
  obtain ⟨d, hd, num, hnum⟩ :
      ∃ d : S, IsUnit d ∧ ∃ num : ∀ x ∈ insert q U, A,
        ∀ (x : S) (hx : x ∈ insert q U), algebraMap A S (num x hx) = x * d :=
    ⟨algebraMap A S (IsLocalization.commonDenom M (insert q U) id : A),
      IsLocalization.map_units S _,
      fun x hx ↦ IsLocalization.integerMultiple M (insert q U) id ⟨x, hx⟩, fun x hx ↦ by
        rw [IsLocalization.map_integerMultiple, Submonoid.smul_def, Algebra.smul_def]
        exact mul_comm _ _⟩
  refine ⟨U.attach.image fun u ↦ num u.1 (Finset.mem_insert_of_mem u.2),
    num q (Finset.mem_insert_self q U), ?_⟩
  have hV : (U.attach.image fun u ↦ num u.1 (Finset.mem_insert_of_mem u.2)).image (algebraMap A S)
      = U.image fun u ↦ u * d :=
    calc (U.attach.image fun u ↦ num u.1 (Finset.mem_insert_of_mem u.2)).image (algebraMap A S)
        = U.attach.image fun u : {x // x ∈ U} ↦ u.1 * d :=
          Finset.image_image.trans
            (Finset.image_congr fun u _ ↦ hnum u.1 (Finset.mem_insert_of_mem u.2))
      _ = (U.attach.image Subtype.val).image fun x ↦ x * d :=
          (Finset.image_image (f := Subtype.val) (g := fun x : S ↦ x * d)).symm
      _ = U.image fun u ↦ u * d := by rw [Finset.attach_image_val]
  rw [comap_preimage_rationalSubset_inter_spa (algebraMap A S) hcont hplus, hV,
    hnum q (Finset.mem_insert_self q U),
    rationalSubset_image_mul_right Bplus U q d hd]

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
  obtain ⟨V, r, hVr⟩ := exists_comap_preimage_rationalSubset_eq (Submonoid.powers s) Aplus Bplus
    (continuous_algebraMap_locTopology P T s S hden) hplus U q
  refine ⟨V, r, Set.ext fun v ↦ ?_⟩
  have hpoint := Set.ext_iff.mp hVr v.1
  rw [Set.mem_preimage, Set.mem_preimage, spaLocalizationHomeomorph_apply_val]
  -- The remaining definitional change only unfolds the two subtype preimages: `v` carries its
  -- membership in `spa Bplus`, while `hVr` is stated for the underlying point `v.1 : Spv S`.
  change comap (algebraMap A S) v.1 ∈ rationalSubset Aplus V r ↔
    v.1 ∈ rationalSubset Bplus U q
  exact ⟨fun hv ↦ hpoint.mp ⟨hv, v.2⟩, fun hv ↦ (hpoint.mpr hv).1⟩

end TauCeti.ValuationSpectrum

end
