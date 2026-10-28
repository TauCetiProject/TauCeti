/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Termination of remainder adjunction

Adjoining a nonzero remainder of an element of the generated ideal leaves that ideal unchanged
but strictly enlarges the ideal of leading terms. Consequently these adjunctions form a
well-founded relation whenever the polynomial ring is Noetherian. This is the termination
argument for completion by reduced S-polynomials; it does not require any particular selection
of pairs, or Buchberger's criterion.

`MonomialOrder.RemainderStep H G` means that `H` is obtained from `G` by one such adjunction.
The new family comes first, so that well-founded recursion follows successive enlargements.
Over a field in finitely many variables, every finite family admits a finite sequence of these
steps ending at a Gröbner basis of the same ideal. This is an existence result using arbitrary
elements of the ideal, not an executable S-polynomial completion algorithm.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §7,
  the termination argument for Buchberger's algorithm.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ}

section CommSemiring

variable [CommSemiring R] {f r : MvPolynomial σ R} {G : Set (MvPolynomial σ R)}

/-- The leading term of a nonzero remainder is outside the ideal of leading terms of the
current divisors. No invertibility assumption on their leading coefficients is needed. -/
theorem IsRemainder.leadingTerm_notMem_span (h : m.IsRemainder f G r) (hr : r ≠ 0) :
    m.leadingTerm r ∉ Ideal.span (m.leadingTerm '' G) := by
  intro hmem
  have hc : m.degree r ∈ (m.leadingTerm r).support := by
    rw [m.support_leadingTerm' hr]
    exact Finset.mem_singleton_self _
  obtain ⟨g, hg, hg0, hgr⟩ := exists_degree_le_of_mem_span_leadingTerm hmem hc
  exact h.not_degree_le (m.degree_mem_support hr) hg hg0 hgr

/-- Adjoining a nonzero remainder strictly enlarges the leading-term ideal, even if the
polynomial being divided does not belong to the ideal of the divisors. -/
theorem IsRemainder.span_leadingTerm_lt (h : m.IsRemainder f G r) (hr : r ≠ 0) :
    Ideal.span (m.leadingTerm '' G) < Ideal.span (m.leadingTerm '' insert r G) := by
  refine lt_of_le_not_ge (Ideal.span_mono (Set.image_mono (Set.subset_insert r G))) ?_
  intro hle
  exact h.leadingTerm_notMem_span hr (hle (Ideal.subset_span ⟨r, Set.mem_insert r G, rfl⟩))

variable (m) in
/-- A completion step adjoins a nonzero remainder of an element of the current ideal.
The enlarged finite family is the first argument, as for a well-founded reduction relation. -/
def RemainderStep (H G : Finset (MvPolynomial σ R)) : Prop :=
  ∃ f r : MvPolynomial σ R, f ∈ Ideal.span (G : Set (MvPolynomial σ R)) ∧
    m.IsRemainder f (G : Set (MvPolynomial σ R)) r ∧ r ≠ 0 ∧
    (H : Set (MvPolynomial σ R)) = insert r (G : Set (MvPolynomial σ R))

/-- The polynomial, remainder and adjunction certificate of a completion step. -/
theorem remainderStep_iff {H G : Finset (MvPolynomial σ R)} :
    m.RemainderStep H G ↔
      ∃ f r : MvPolynomial σ R, f ∈ Ideal.span (G : Set (MvPolynomial σ R)) ∧
        m.IsRemainder f (G : Set (MvPolynomial σ R)) r ∧ r ≠ 0 ∧
        (H : Set (MvPolynomial σ R)) = insert r (G : Set (MvPolynomial σ R)) :=
  Iff.rfl

namespace RemainderStep

variable {G H : Finset (MvPolynomial σ R)}

/-- Construct a step from its remainder certificate. -/
theorem of_isRemainder [DecidableEq (MvPolynomial σ R)]
    (h : m.IsRemainder f G r) (hf : f ∈ Ideal.span (G : Set _)) (hr : r ≠ 0) :
    m.RemainderStep (insert r G) G :=
  ⟨f, r, hf, h, hr, Finset.coe_insert _ _⟩

/-- A step retains every previous divisor. -/
theorem subset (h : m.RemainderStep H G) : G ⊆ H := by
  obtain ⟨f, r, hf, hrem, hr, hH⟩ := remainderStep_iff.mp h
  apply Finset.coe_subset.mp
  rw [hH]
  exact Set.subset_insert r (G : Set (MvPolynomial σ R))

/-- A step strictly enlarges the leading-term ideal. -/
theorem span_leadingTerm_lt (h : m.RemainderStep H G) :
    Ideal.span (m.leadingTerm '' (G : Set (MvPolynomial σ R))) <
      Ideal.span (m.leadingTerm '' (H : Set (MvPolynomial σ R))) := by
  obtain ⟨f, r, hf, hrem, hr, hH⟩ := remainderStep_iff.mp h
  rw [hH]
  exact hrem.span_leadingTerm_lt hr

end RemainderStep

/-- Remainder adjunction terminates whenever the ambient polynomial semiring is Noetherian.
In particular this applies to finitely many variables over a Noetherian coefficient ring. -/
theorem wellFounded_remainderStep (m : MonomialOrder σ)
    [IsNoetherianRing (MvPolynomial σ R)] : WellFounded (m.RemainderStep (R := R)) := by
  exact (wellFounded_gt.onFun (f := fun G : Finset (MvPolynomial σ R) ↦
    Ideal.span (m.leadingTerm '' (G : Set (MvPolynomial σ R))))).mono
      (fun _ _ h ↦ h.span_leadingTerm_lt)

end CommSemiring

section CommRing

variable [CommRing R]

/-- A step preserves the generated ideal. -/
theorem RemainderStep.span_eq {G H : Finset (MvPolynomial σ R)} (h : m.RemainderStep H G) :
    Ideal.span (H : Set (MvPolynomial σ R)) = Ideal.span (G : Set (MvPolynomial σ R)) := by
  obtain ⟨f, r, hf, hrem, hr, hH⟩ := remainderStep_iff.mp h
  rw [hH]
  apply Submodule.span_insert_eq_span
  simpa using sub_mem hf hrem.sub_mem_span

/-- A finite family with unit leading coefficients on its nonzero members is terminal for
remainder adjunction exactly when it is a Gröbner basis of its generated ideal. -/
theorem isGroebnerBasis_iff_no_remainderStep (m : MonomialOrder σ)
    {G : Finset (MvPolynomial σ R)} (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (G : Set (MvPolynomial σ R))
      (Ideal.span (G : Set (MvPolynomial σ R))) ↔ ∀ H, ¬ m.RemainderStep H G := by
  classical
  refine ⟨?_, ?_⟩
  · intro h H hstep
    obtain ⟨f, r, hf, hrem, hr, hH⟩ := remainderStep_iff.mp hstep
    exact hr ((h.remainder_eq_zero_iff_mem hrem).2 hf)
  · intro h
    apply (m.isGroebnerBasis_iff_isRemainder_zero hG).2
    refine ⟨Ideal.subset_span, fun f hf ↦ ?_⟩
    obtain ⟨r, hr⟩ := exists_isRemainder hG f
    have hr0 : r = 0 := by
      by_contra hne
      exact h (insert r G) (RemainderStep.of_isRemainder hr hf hne)
    rwa [hr0] at hr

end CommRing

section Field

variable {k : Type*} [Field k] [IsNoetherianRing (MvPolynomial σ k)]

/-- Any finite family over a field with Noetherian polynomial ring has a finite completion by
certified remainder adjunctions. The endpoint contains the original family and is a Gröbner
basis of the original ideal. `ReflTransGen` records the finite path with the endpoint first,
matching `RemainderStep`. In particular this applies to any finite variable type. -/
theorem exists_remainderStep_completion (m : MonomialOrder σ) (G : Finset (MvPolynomial σ k)) :
    ∃ H : Finset (MvPolynomial σ k), Relation.ReflTransGen m.RemainderStep H G ∧
      G ⊆ H ∧ m.IsGroebnerBasis (H : Set (MvPolynomial σ k))
        (Ideal.span (G : Set (MvPolynomial σ k))) := by
  classical
  induction G using (m.wellFounded_remainderStep (R := k)).induction with
  | h G ih =>
    by_cases ht : ∀ H, ¬ m.RemainderStep H G
    · exact ⟨G, .refl, Finset.Subset.refl G,
        (m.isGroebnerBasis_iff_no_remainderStep (fun g _ hg ↦ m.isUnit_leadingCoeff.2 hg)).2 ht⟩
    · push Not at ht
      obtain ⟨H, hHG⟩ := ht
      obtain ⟨K, hKH, hHK, hK⟩ := ih H hHG
      exact ⟨K, hKH.tail hHG, hHG.subset.trans hHK, hHG.span_eq ▸ hK⟩

end Field

end MonomialOrder
