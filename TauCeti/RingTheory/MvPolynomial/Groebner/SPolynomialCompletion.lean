/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Buchberger
public import TauCeti.RingTheory.MvPolynomial.Groebner.Completion

/-!
# Certified completion by S-polynomials

Buchberger completion adjoins a nonzero remainder of the S-polynomial of two current
basis elements. `MonomialOrder.SPolynomialStep H G` records the pair, its bounded division
certificate, and the resulting adjunction. As with `MonomialOrder.RemainderStep`, the enlarged
family comes first.

Every such step preserves the generated ideal and strictly enlarges its leading-term ideal.
Thus any sequence of these steps terminates when the polynomial ring is Noetherian, regardless
of the choices of pairs and remainders. For divisors with unit leading coefficients,
Buchberger's criterion identifies the terminal families with Gröbner bases. Over a field this
gives a finite completion of any finite family using only certified S-polynomial steps.

The finite path records actual S-polynomial remainders, rather than arbitrary elements of the
ideal. This is an existence and termination theorem, not an executable pair-selection or
polynomial-division algorithm. No monic normalization is imposed on newly adjoined elements.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §7,
  Buchberger's algorithm and its termination proof.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} [CommRing R] {m : MonomialOrder σ}

/-- A Buchberger completion step: adjoin a nonzero remainder of the S-polynomial of two
members of the current finite family. The enlarged family is the first argument. -/
def SPolynomialStep (m : MonomialOrder σ) (H G : Finset (MvPolynomial σ R)) : Prop :=
  ∃ g₁ ∈ G, ∃ g₂ ∈ G, ∃ r : MvPolynomial σ R,
    m.IsRemainder (m.sPolynomial g₁ g₂) (G : Set (MvPolynomial σ R)) r ∧ r ≠ 0 ∧
      (H : Set (MvPolynomial σ R)) = insert r (G : Set (MvPolynomial σ R))

/-- The selected pair, division representation, nonzero remainder, and adjunction equality
carried by an S-polynomial step. -/
theorem sPolynomialStep_iff {H G : Finset (MvPolynomial σ R)} :
    m.SPolynomialStep H G ↔
      ∃ g₁ ∈ G, ∃ g₂ ∈ G, ∃ r : MvPolynomial σ R,
        m.IsRemainder (m.sPolynomial g₁ g₂) (G : Set (MvPolynomial σ R)) r ∧ r ≠ 0 ∧
          (H : Set (MvPolynomial σ R)) = insert r (G : Set (MvPolynomial σ R)) :=
  Iff.rfl

namespace SPolynomialStep

variable {G H : Finset (MvPolynomial σ R)} {g₁ g₂ r : MvPolynomial σ R}

/-- Construct an S-polynomial step from the selected pair and its division certificate. -/
theorem of_isRemainder [DecidableEq (MvPolynomial σ R)] (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G)
    (h : m.IsRemainder (m.sPolynomial g₁ g₂) (G : Set (MvPolynomial σ R)) r) (hr : r ≠ 0) :
    m.SPolynomialStep (insert r G) G :=
  sPolynomialStep_iff.2 ⟨g₁, hg₁, g₂, hg₂, r, h, hr, Finset.coe_insert _ _⟩

/-- Every S-polynomial step is a remainder adjunction of an element of the current ideal. -/
theorem toRemainderStep (h : m.SPolynomialStep H G) : m.RemainderStep H G := by
  obtain ⟨g₁, hg₁, g₂, hg₂, r, hrem, hr, hH⟩ := sPolynomialStep_iff.1 h
  exact remainderStep_iff.2 ⟨m.sPolynomial g₁ g₂, r,
    sPolynomial_mem_ideal (Ideal.subset_span hg₁) (Ideal.subset_span hg₂), hrem, hr, hH⟩

/-- An S-polynomial step retains all previous generators. -/
theorem subset (h : m.SPolynomialStep H G) : G ⊆ H :=
  h.toRemainderStep.subset

/-- An S-polynomial step does not change the generated ideal. -/
theorem span_eq (h : m.SPolynomialStep H G) :
    Ideal.span (H : Set (MvPolynomial σ R)) = Ideal.span (G : Set (MvPolynomial σ R)) :=
  h.toRemainderStep.span_eq

/-- Each nonzero reduced S-polynomial strictly enlarges the leading-term ideal. -/
theorem span_leadingTerm_lt (h : m.SPolynomialStep H G) :
    Ideal.span (m.leadingTerm '' (G : Set (MvPolynomial σ R))) <
      Ideal.span (m.leadingTerm '' (H : Set (MvPolynomial σ R))) :=
  h.toRemainderStep.span_leadingTerm_lt

end SPolynomialStep

/-- S-polynomial completion terminates in a Noetherian polynomial ring, independently of
which pair and which nonzero remainder are selected at each step. -/
theorem wellFounded_sPolynomialStep (m : MonomialOrder σ)
    [IsNoetherianRing (MvPolynomial σ R)] : WellFounded (m.SPolynomialStep (R := R)) :=
  (m.wellFounded_remainderStep (R := R)).mono fun _ _ h ↦ h.toRemainderStep

/-- A finite family whose nonzero members have unit leading coefficients is terminal for
S-polynomial completion exactly when it is a Gröbner basis of its generated ideal. -/
theorem isGroebnerBasis_iff_no_sPolynomialStep (m : MonomialOrder σ)
    {G : Finset (MvPolynomial σ R)} (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (G : Set (MvPolynomial σ R))
      (Ideal.span (G : Set (MvPolynomial σ R))) ↔ ∀ H, ¬ m.SPolynomialStep H G := by
  classical
  refine ⟨fun h H hstep ↦ ?_, fun h ↦ ?_⟩
  · exact (m.isGroebnerBasis_iff_no_remainderStep hG).1 h H hstep.toRemainderStep
  · apply isGroebnerBasis_span_of_isRemainder_sPolynomial_zero hG
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨r, hr⟩ := exists_isRemainder hG (m.sPolynomial g₁ g₂)
    have hr0 : r = 0 := by
      by_contra hne
      exact h (insert r G) (SPolynomialStep.of_isRemainder hg₁ hg₂ hr hne)
    rwa [hr0] at hr

section Field

variable {k : Type*} [Field k] [IsNoetherianRing (MvPolynomial σ k)]

/-- **Finite Buchberger completion.** Every finite family over a field in a Noetherian
polynomial ring has a finite certified completion using only nonzero S-polynomial remainders.
The endpoint contains the starting family and is a Gröbner basis of the same ideal.

`ReflTransGen` records the finite sequence with the endpoint first, matching
`SPolynomialStep`. In particular the theorem applies to every finite variable type. -/
theorem exists_sPolynomialStep_completion (m : MonomialOrder σ) (G : Finset (MvPolynomial σ k)) :
    ∃ H : Finset (MvPolynomial σ k), Relation.ReflTransGen m.SPolynomialStep H G ∧
      G ⊆ H ∧ m.IsGroebnerBasis (H : Set (MvPolynomial σ k))
        (Ideal.span (G : Set (MvPolynomial σ k))) := by
  classical
  induction G using (m.wellFounded_sPolynomialStep (R := k)).induction with
  | h G ih =>
    by_cases ht : ∀ H, ¬ m.SPolynomialStep H G
    · exact ⟨G, .refl, Finset.Subset.refl G,
        (m.isGroebnerBasis_iff_no_sPolynomialStep
          (fun g _ hg ↦ m.isUnit_leadingCoeff.2 hg)).2 ht⟩
    · push Not at ht
      obtain ⟨H, hHG⟩ := ht
      obtain ⟨K, hKH, hHK, hK⟩ := ih H hHG
      exact ⟨K, hKH.tail hHG, hHG.subset.trans hHK, hHG.span_eq ▸ hK⟩

end Field

end MonomialOrder
