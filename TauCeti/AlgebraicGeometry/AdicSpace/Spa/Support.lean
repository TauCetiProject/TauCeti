/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.RingTheory.Huber.Pair
public import TauCeti.RingTheory.Huber.UnitGroup

/-!
# Proper ideals of a complete Huber pair are supports

Over a complete Hausdorff Huber pair `(A, A⁺)` every proper ideal `J` of `A` is contained in the
support of some point of `Spa (A, A⁺)`:

```text
J ≠ ⊤  ↔  ∃ v ∈ Spa (A, A⁺), J ⊆ supp v.
```

This is Wedhorn's Proposition 7.51 in the form his §8 uses. Its two standard consequences follow
at once: an element on which no point vanishes is a unit (Proposition 7.52(2)), and a finite set
whose standard rational family covers the spectrum generates the unit ideal (the half of Corollary
7.53 that the covering direction does not supply).

## Why this is not the statement already on `main`

`TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq` produces a point with prescribed support from an
*open* prime ideal, using the trivial valuation there, and the derived
`isUnit_of_forall_not_vle_zero` and `span_eq_top_of_forall_mem_spa_exists_not_vle_zero` inherit an
openness hypothesis on the maximal ideals of `A`. That hypothesis is **unsatisfiable over a nonzero
Tate ring**, where an ideal is open exactly when it is `⊤`
(`TauCeti.Huber.IsTateRing.isOpen_iff_eq_top`), so those statements are vacuous on the affinoid
rings Wedhorn's §8 is about. The route taken here never mentions an open ideal:

* the quotient Huber pair `(A/J, (A/J)⁺)` is again a Huber pair (`TauCeti.Huber.Pair.quotient`),
  and its spectrum is empty exactly when `1` lies in the closure of zero
  (`TauCeti.ValuationSpectrum.spa_eq_empty_iff_one_mem_closure_zero`, Wedhorn Proposition 7.49(1));
* completeness keeps a proper ideal from being dense, upstairs and downstairs alike
  (`TauCeti.Huber.one_notMem_closure_zero_quotient_of_ne_top`), because the unit group of a
  complete Huber ring is open;
* a point of the quotient spectrum is a point of `Spa (A, A⁺)` whose support contains `J`, which
  is the range computation `TauCeti.ValuationSpectrum.range_spaComap_quotientMk`.

Completeness replaces openness of the maximal ideals, and is exactly the hypothesis Wedhorn carries.

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spa_le_supp_of_ne_top` : **Wedhorn Proposition 7.51** — a
  proper ideal of a complete Hausdorff Huber pair is contained in the support of a point, with
  `TauCeti.ValuationSpectrum.ne_top_iff_exists_mem_spa_le_supp` the resulting criterion.
* `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_of_isMaximal` : a maximal ideal *is* the
  support of a point.
* `TauCeti.ValuationSpectrum.span_eq_top_iff_forall_mem_spa_exists_notMem_supp` : a set generates
  the unit ideal exactly when no point of the spectrum kills all of it.
* `TauCeti.ValuationSpectrum.isUnit_iff_forall_mem_spa_notMem_supp` : **Wedhorn Proposition
  7.52(2)**, as a criterion, together with the packaging
  `TauCeti.ValuationSpectrum.iUnion_supp_eq_nonunits`.
* `TauCeti.ValuationSpectrum.span_eq_top_of_spa_eq_biUnion_rationalSubset` : **the converse half of
  Wedhorn Corollary 7.53** — if the standard family `(R(T/t))_{t ∈ T}` covers the spectrum then `T`
  generates the unit ideal. The other half is
  `TauCeti.ValuationSpectrum.spa_eq_biUnion_rationalSubset_of_span_eq_top`, which asks nothing of
  `A`, so the two together are Corollary 7.53 with no hypothesis on maximal ideals.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 7.49, 7.51, 7.52
  and Corollary 7.53.

## Provenance

Developed here. AINTLIB reaches Propositions 7.51 and 7.52(2) through an open maximal ideal, which
is the route `TauCeti/AlgebraicGeometry/AdicSpace/Spa/Points.lean` carries over; the argument
below shares nothing with it beyond the statements.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [IsHuberRing A]

/-- **Wedhorn Proposition 7.51.** Every proper ideal of a complete Hausdorff Huber pair is
contained in the support of a point of `Spa (A, A⁺)`.

Wedhorn states it for a maximal ideal, where the containment is an equality; that form is
`exists_mem_spa_supp_eq_of_isMaximal`. The proof runs through the quotient Huber pair: the
spectrum of `(A/J, (A/J)⁺)` is nonempty because `1` avoids the closure of zero there, and a point
of it is a point of `Spa (A, A⁺)` whose support contains `J`. -/
theorem exists_mem_spa_le_supp_of_ne_top (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {J : Ideal A} (hJ : J ≠ ⊤) :
    ∃ v ∈ spa Aplus, J ≤ supp v := by
  have hmapmem : ∀ a ∈ Aplus, Ideal.Quotient.mk J a ∈ Aplus.map (Ideal.Quotient.mk J) :=
    fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩
  have hne : (spa (Aplus.map (Ideal.Quotient.mk J))).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    refine one_notMem_closure_zero_quotient_of_ne_top hJ ?_
    refine (spa_eq_empty_iff_one_mem_closure_zero (Pair.quotient ⟨Aplus, hplus⟩ J).plus
      (Pair.quotient ⟨Aplus, hplus⟩ J).isRingOfIntegralElements).mp ?_
    rwa [Pair.quotient_plus, spa_integralClosure]
  obtain ⟨w, hw⟩ := hne
  set v := spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus _ hmapmem ⟨w, hw⟩
  have hsupp : v ∈ Subtype.val ⁻¹' {u : Spv A | J ≤ u.supp} :=
    range_spaComap_quotientMk J Aplus ▸ Set.mem_range_self (⟨w, hw⟩ : spa _)
  exact ⟨v.1, v.2, hsupp⟩

/-- A proper ideal of a complete Hausdorff Huber pair is exactly one that some point of
`Spa (A, A⁺)` kills. The reverse implication needs nothing: a support is prime, hence proper. -/
theorem ne_top_iff_exists_mem_spa_le_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (J : Ideal A) :
    J ≠ ⊤ ↔ ∃ v ∈ spa Aplus, J ≤ supp v := by
  refine ⟨exists_mem_spa_le_supp_of_ne_top Aplus hplus, ?_⟩
  rintro ⟨v, -, hle⟩ rfl
  exact (Ideal.IsPrime.ne_top inferInstance) (top_le_iff.mp hle)

/-- **Wedhorn Proposition 7.51, for a maximal ideal.** A maximal ideal of a complete Hausdorff
Huber pair is the support of a point of `Spa (A, A⁺)`: it is contained in one by
`exists_mem_spa_le_supp_of_ne_top`, and that support is proper because it is prime. -/
theorem exists_mem_spa_supp_eq_of_isMaximal (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ v ∈ spa Aplus, supp v = 𝔪 := by
  obtain ⟨v, hv, hle⟩ :=
    exists_mem_spa_le_supp_of_ne_top Aplus hplus (Ideal.IsMaximal.ne_top ‹𝔪.IsMaximal›)
  exact ⟨v, hv, (Ideal.IsMaximal.eq_of_le ‹𝔪.IsMaximal›
    (Ideal.IsPrime.ne_top inferInstance) hle).symm⟩

/-- A subset of a complete Hausdorff Huber pair generates the unit ideal exactly when no point of
`Spa (A, A⁺)` kills all of it. The forward implication holds over any commutative ring, since a
support is a proper ideal; the converse is `exists_mem_spa_le_supp_of_ne_top`. -/
theorem span_eq_top_iff_forall_mem_spa_exists_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Set A} :
    Ideal.span T = ⊤ ↔ ∀ v ∈ spa Aplus, ∃ t ∈ T, t ∉ supp v := by
  constructor
  · intro hT v _
    by_contra hcon
    have hle : Ideal.span T ≤ supp v :=
      Ideal.span_le.mpr fun t ht ↦ by
        by_contra hts
        exact hcon ⟨t, ht, hts⟩
    rw [hT] at hle
    exact (Ideal.IsPrime.ne_top inferInstance) (top_le_iff.mp hle)
  · intro h
    by_contra hne
    obtain ⟨v, hv, hle⟩ := exists_mem_spa_le_supp_of_ne_top Aplus hplus hne
    obtain ⟨t, ht, hts⟩ := h v hv
    exact hts (hle (Ideal.subset_span ht))

/-- **Wedhorn Proposition 7.52(2)**, as a criterion: an element of a complete Hausdorff Huber pair
is a unit exactly when no point of `Spa (A, A⁺)` vanishes on it.

Unlike `isUnit_of_forall_not_vle_zero`, this asks nothing of the maximal ideals of `A`, so it is
available over a Tate ring, where that hypothesis cannot be met. -/
theorem isUnit_iff_forall_mem_spa_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (f : A) :
    IsUnit f ↔ ∀ v ∈ spa Aplus, f ∉ supp v := by
  rw [← Ideal.span_singleton_eq_top,
    span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus]
  simp

/-- The supports of the points of `Spa (A, A⁺)` sweep out exactly the nonunits of a complete
Hausdorff Huber ring. This is `isUnit_iff_forall_mem_spa_notMem_supp` read as a set equality. -/
theorem iUnion_supp_eq_nonunits (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) :
    ⋃ v ∈ spa Aplus, (supp v : Set A) = nonunits A := by
  ext f
  rw [Set.mem_iUnion₂, mem_nonunits_iff, isUnit_iff_forall_mem_spa_notMem_supp Aplus hplus f]
  push Not
  simp only [SetLike.mem_coe, exists_prop]

/-- **The converse half of Wedhorn Corollary 7.53.** If the standard rational family
`(R(T/t))_{t ∈ T}` covers `Spa (A, A⁺)` for a complete Hausdorff Huber pair, then `T` generates
the unit ideal.

The other half, `spa_eq_biUnion_rationalSubset_of_span_eq_top`, holds over an arbitrary
commutative ring, so the two together are Corollary 7.53 with completeness as the only hypothesis
— in particular with none on the maximal ideals of `A`, which a nonzero Tate ring cannot supply. -/
theorem span_eq_top_of_spa_eq_biUnion_rationalSubset (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Finset A}
    (hcov : spa Aplus = ⋃ t ∈ T, rationalSubset Aplus T t) :
    Ideal.span (T : Set A) = ⊤ := by
  refine (span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus).mpr fun v hv ↦ ?_
  obtain ⟨t, ht, hmem⟩ := Set.mem_iUnion₂.mp (hcov ▸ hv)
  exact ⟨t, ht, fun hsupp ↦
    ((mem_rationalSubset_iff Aplus T t v).mp hmem).2.2 ((mem_supp_iff v t).mp hsupp)⟩

end TauCeti.ValuationSpectrum

end
