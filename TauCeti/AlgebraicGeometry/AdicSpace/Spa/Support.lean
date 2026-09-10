/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.RingTheory.Huber.UnitGroup

/-!
# Proper ideals of a complete Huber pair are contained in supports

Over a complete Hausdorff Huber pair `(A, A⁺)` every proper ideal `J` of `A` is contained in the
support of some point of `Spa (A, A⁺)`:

```text
J ≠ ⊤  ↔  ∃ v ∈ Spa (A, A⁺), J ⊆ supp v.
```

This is Wedhorn's Proposition 7.51 in the form his §8 uses; for a maximal ideal the containment is
an equality. Its standard consequence proved here is the unit criterion of Proposition 7.52(2).
Corollary 7.53, which characterizes when a finite set's standard rational family covers the
spectrum, is read off from it in
`TauCeti/AlgebraicGeometry/AdicSpace/Spa/RationalSubset/Cover.lean`.

## Comparison with the open-prime approach

`TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq` produces a point with prescribed support from an
*open* prime ideal, using the trivial valuation there, and the derived
`isUnit_of_forall_not_vle_zero` and `span_eq_top_of_forall_mem_spa_exists_not_vle_zero` inherit an
openness hypothesis on the maximal ideals of `A`. That hypothesis is **unsatisfiable over a nonzero
Tate ring**, where an ideal is open exactly when it is `⊤`
(`TauCeti.Huber.IsTateRing.isOpen_iff_eq_top`), so those statements are vacuous on the affinoid
rings Wedhorn's §8 is about. The quotient-spectrum approach instead uses the following facts:

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
  7.52(2)**, as a criterion.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Propositions 7.49, 7.51
  and 7.52.

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
contained in the support of a point of `Spa (A, A⁺)`. Wedhorn states the maximal-ideal case, where
the containment is an equality. -/
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

/-- A proper ideal of a complete Hausdorff Huber pair is exactly one contained in the support of
some point of `Spa (A, A⁺)`. -/
theorem ne_top_iff_exists_mem_spa_le_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (J : Ideal A) :
    J ≠ ⊤ ↔ ∃ v ∈ spa Aplus, J ≤ supp v := by
  refine ⟨exists_mem_spa_le_supp_of_ne_top Aplus hplus, ?_⟩
  rintro ⟨v, -, hle⟩ rfl
  exact (Ideal.IsPrime.ne_top inferInstance) (top_le_iff.mp hle)

/-- **Wedhorn Proposition 7.51, for a maximal ideal.** A maximal ideal of a complete Hausdorff
Huber pair is the support of a point of `Spa (A, A⁺)`. -/
theorem exists_mem_spa_supp_eq_of_isMaximal (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ v ∈ spa Aplus, supp v = 𝔪 := by
  obtain ⟨v, hv, hle⟩ :=
    exists_mem_spa_le_supp_of_ne_top Aplus hplus (Ideal.IsMaximal.ne_top ‹𝔪.IsMaximal›)
  exact ⟨v, hv, (Ideal.IsMaximal.eq_of_le ‹𝔪.IsMaximal›
    (Ideal.IsPrime.ne_top inferInstance) hle).symm⟩

/-- A subset of a complete Hausdorff Huber pair generates the unit ideal exactly when no point of
`Spa (A, A⁺)` kills all of it. -/
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

/-- **Wedhorn Proposition 7.52(2).** An element of a complete Hausdorff Huber pair is a unit
exactly when no point of `Spa (A, A⁺)` vanishes on it. -/
theorem isUnit_iff_forall_mem_spa_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (f : A) :
    IsUnit f ↔ ∀ v ∈ spa Aplus, f ∉ supp v := by
  rw [← Ideal.span_singleton_eq_top,
    span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus]
  simp

end TauCeti.ValuationSpectrum

end
