/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.RingTheory.Huber.UnitGroup

import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Ideals contained in supports of points of the adic spectrum

Over a Huber pair `(A, A⁺)` an ideal `J` of `A` is contained in the support of some point of
`Spa (A, A⁺)` exactly when its closure is proper:

```text
closure J ≠ ⊤  ↔  ∃ v ∈ Spa (A, A⁺), J ⊆ supp v.
```

For `J = 0` this is the emptiness criterion of Wedhorn's Proposition 7.49(1). Over a complete
Hausdorff Huber pair no proper ideal is dense, so every proper ideal lies in a support: this is
Wedhorn's Proposition 7.51 in the form his §8 uses, and for a maximal ideal the containment is an
equality. Its standard consequence proved here is the unit criterion of Proposition 7.52(2).
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
* `1` lies in the closure of zero in `A/J` exactly when it lies in the closure of `J`
  (`Ideal.Quotient.mk_mem_closure_zero_iff`), because the quotient map is open;
* a point of the quotient spectrum is a point of `Spa (A, A⁺)` whose support contains `J`, which
  is the range computation `TauCeti.ValuationSpectrum.range_spaComap_quotientMk`.

Conversely the support of a continuous valuation is closed
(`TauCeti.ValuationSpectrum.IsContinuous.isClosed_supp`), so it contains the closure of every
ideal it contains. Over a complete Hausdorff Huber ring the unit group is open
(`TauCeti.Huber.isOpen_setOf_isUnit`), so the closure of a proper ideal is proper. Completeness
replaces openness of the maximal ideals, and is exactly the hypothesis Wedhorn carries; closedness
of the maximal ideal is all the argument uses.

## Main results

* `TauCeti.ValuationSpectrum.exists_mem_spa_le_supp_iff_closure_ne_top` : over a Huber pair, an
  ideal is contained in the support of a point exactly when its closure is proper.
* `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_iff_isClosed` : over a Huber pair, a maximal
  ideal is the support of a point exactly when it is closed.
* `TauCeti.ValuationSpectrum.closure_span_eq_top_iff_forall_mem_spa_exists_notMem_supp` : over a
  Huber pair, a set generates a dense ideal exactly when no point of the spectrum kills all of it.
* `TauCeti.ValuationSpectrum.exists_mem_spa_le_supp_of_ne_top` : **Wedhorn Proposition 7.51** — a
  proper ideal of a complete Hausdorff Huber pair is contained in the support of a point, with
  `TauCeti.ValuationSpectrum.ne_top_iff_exists_mem_spa_le_supp` the resulting criterion.
* `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_of_isMaximal` : over a complete Hausdorff Huber
  pair, a maximal ideal *is* the support of a point.
* `TauCeti.ValuationSpectrum.span_eq_top_iff_forall_mem_spa_exists_notMem_supp` : over a complete
  Hausdorff Huber pair, a set generates the unit ideal exactly when no point of the spectrum kills
  all of it.
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

section HuberPair

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

/-- **Ideals contained in supports.** An ideal of a Huber pair is contained in the support of a
point of `Spa (A, A⁺)` exactly when its closure is proper. For `J = 0` this is Wedhorn's
Proposition 7.49(1); over a complete Hausdorff Huber pair it gives Wedhorn's Proposition 7.51,
`exists_mem_spa_le_supp_of_ne_top`. -/
theorem exists_mem_spa_le_supp_iff_closure_ne_top (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (J : Ideal A) :
    (∃ v ∈ spa Aplus, J ≤ supp v) ↔ J.closure ≠ ⊤ := by
  constructor
  · -- the support of a continuous valuation is a closed proper ideal
    rintro ⟨v, hv, hle⟩ htop
    refine (inferInstance : v.supp.IsPrime).ne_top (top_le_iff.mp ?_)
    rw [← htop, ← SetLike.coe_subset_coe, Ideal.coe_closure]
    exact closure_minimal hle ((mem_spa_iff Aplus v).mp hv).1.isClosed_supp
  · -- a point of the quotient spectrum, which is nonempty, pulls back to such a point
    intro hJ
    have hmapmem : ∀ a ∈ Aplus, Ideal.Quotient.mk J a ∈ Aplus.map (Ideal.Quotient.mk J) :=
      fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩
    have hne : (spa (Aplus.map (Ideal.Quotient.mk J))).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hempty
      refine hJ ((Ideal.eq_top_iff_one _).mpr ?_)
      rw [← SetLike.mem_coe, Ideal.coe_closure, ← Ideal.Quotient.mk_mem_closure_zero_iff, map_one]
      refine (spa_eq_empty_iff_one_mem_closure_zero (Pair.quotient ⟨Aplus, hplus⟩ J).plus
        (Pair.quotient ⟨Aplus, hplus⟩ J).isRingOfIntegralElements).mp ?_
      rwa [Pair.quotient_plus, spa_integralClosure]
    obtain ⟨w, hw⟩ := hne
    set v := spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus _ hmapmem ⟨w, hw⟩
    have hsupp : v ∈ Subtype.val ⁻¹' {u : Spv A | J ≤ u.supp} :=
      range_spaComap_quotientMk J Aplus ▸ Set.mem_range_self (⟨w, hw⟩ : spa _)
    exact ⟨v.1, v.2, hsupp⟩

/-- A maximal ideal of a Huber pair is the support of a point of `Spa (A, A⁺)` exactly when it is
closed. -/
theorem exists_mem_spa_supp_eq_iff_isClosed (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    (∃ v ∈ spa Aplus, supp v = 𝔪) ↔ IsClosed (𝔪 : Set A) := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ((mem_spa_iff Aplus v).mp hv).1.isClosed_supp
  · intro hclosed
    obtain ⟨v, hv, hle⟩ := (exists_mem_spa_le_supp_iff_closure_ne_top Aplus hplus 𝔪).mpr <| by
      rw [Ideal.closure_eq_of_isClosed 𝔪 hclosed]
      exact Ideal.IsMaximal.ne_top ‹_›
    exact ⟨v, hv, (Ideal.IsMaximal.eq_of_le ‹_› (Ideal.IsPrime.ne_top inferInstance) hle).symm⟩

/-- A subset of a Huber pair generates a dense ideal exactly when no point of `Spa (A, A⁺)` kills
all of it. -/
theorem closure_span_eq_top_iff_forall_mem_spa_exists_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Set A} :
    (Ideal.span T).closure = ⊤ ↔ ∀ v ∈ spa Aplus, ∃ t ∈ T, t ∉ supp v := by
  rw [← not_iff_not, ← ne_eq, ← exists_mem_spa_le_supp_iff_closure_ne_top Aplus hplus]
  push Not
  simp only [Ideal.span_le, Set.subset_def, SetLike.mem_coe]

end HuberPair

section Complete

variable {A : Type*} [CommRing A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [IsHuberRing A]

/-- **Wedhorn Proposition 7.51.** Every proper ideal of a complete Hausdorff Huber pair is
contained in the support of a point of `Spa (A, A⁺)`. Wedhorn states the maximal-ideal case, where
the containment is an equality. -/
theorem exists_mem_spa_le_supp_of_ne_top (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {J : Ideal A} (hJ : J ≠ ⊤) :
    ∃ v ∈ spa Aplus, J ≤ supp v :=
  (exists_mem_spa_le_supp_iff_closure_ne_top Aplus hplus J).mpr
    (Ideal.closure_ne_top_of_isOpen_isUnit isOpen_setOf_isUnit hJ)

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
    ∃ v ∈ spa Aplus, supp v = 𝔪 :=
  (exists_mem_spa_supp_eq_iff_isClosed Aplus hplus 𝔪).mpr (isClosed_of_isMaximal 𝔪)

/-- A subset of a complete Hausdorff Huber pair generates the unit ideal exactly when no point of
`Spa (A, A⁺)` kills all of it. -/
theorem span_eq_top_iff_forall_mem_spa_exists_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) {T : Set A} :
    Ideal.span T = ⊤ ↔ ∀ v ∈ spa Aplus, ∃ t ∈ T, t ∉ supp v := by
  rw [← closure_span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus]
  refine ⟨fun h ↦ by rw [h]; exact Ideal.closure_eq_of_isClosed ⊤ isClosed_univ, fun h ↦ ?_⟩
  by_contra hne
  exact Ideal.closure_ne_top_of_isOpen_isUnit isOpen_setOf_isUnit hne h

/-- **Wedhorn Proposition 7.52(2).** An element of a complete Hausdorff Huber pair is a unit
exactly when no point of `Spa (A, A⁺)` vanishes on it. -/
theorem isUnit_iff_forall_mem_spa_notMem_supp (Aplus : Subring A)
    (hplus : IsRingOfIntegralElements Aplus) (f : A) :
    IsUnit f ↔ ∀ v ∈ spa Aplus, f ∉ supp v := by
  rw [← Ideal.span_singleton_eq_top,
    span_eq_top_iff_forall_mem_spa_exists_notMem_supp Aplus hplus]
  simp

end Complete

end TauCeti.ValuationSpectrum

end
