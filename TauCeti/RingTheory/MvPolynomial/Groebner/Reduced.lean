/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Basic
import Mathlib.Data.Finsupp.PWO

/-!
# Reduced monic Gröbner bases

A reduced monic Gröbner basis contains no zero polynomial, all its elements are monic, and
no monomial of any basis element is divisible by the leading monomial of another element.
The restriction applies to the entire support, including the leading monomial.

## Main results

* `MonomialOrder.IsReducedGroebnerBasis.eq`: two reduced monic Gröbner bases of the same ideal
  are equal as sets. The proof first matches their minimal leading exponents, then uses
  cancellation of equal monic leading terms to identify the polynomials.
* `MonomialOrder.IsGroebnerBasis.exists_isReducedGroebnerBasis`: an ideal with a Gröbner basis
  whose nonzero members have unit leading coefficients has a reduced monic Gröbner basis. Its
  elements are `X^a - r`, for `a` minimal for divisibility among the leading exponents of `I`
  and `r` a remainder of `X^a`.
* `MonomialOrder.existsUnique_isReducedGroebnerBasis`: over a field, every ideal has exactly
  one reduced monic Gröbner basis.
* `MonomialOrder.IsReducedGroebnerBasis.finite`: in finitely many variables a reduced monic
  Gröbner basis is finite, by Dickson's lemma.

Apart from finiteness, neither the variable type nor the bases need be finite. The coefficients
may be any commutative ring, including a ring with zero divisors; only the field corollaries
assume a field.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §7,
  Theorem 5: existence and uniqueness of the reduced Gröbner basis.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R] {m : MonomialOrder σ}
  {G H : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A reduced monic Gröbner basis of `I`: a Gröbner basis consisting of nonzero monic
polynomials, with every monomial of each element irreducible by all the other elements.
The nonzero condition is explicit so that the definition also works over the zero ring. -/
structure IsReducedGroebnerBasis (m : MonomialOrder σ) (G : Set (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ R)) : Prop where
  /-- The set is a Gröbner basis of the ideal. -/
  isGroebnerBasis : m.IsGroebnerBasis G I
  /-- Zero is not a basis element. -/
  ne_zero : ∀ g ∈ G, g ≠ 0
  /-- Every basis element has leading coefficient one. -/
  monic : ∀ g ∈ G, m.Monic g
  /-- No term of a basis element is divisible by another basis element's leading monomial. -/
  not_degree_le : ∀ g ∈ G, ∀ c ∈ g.support, ∀ h ∈ G, h ≠ g → ¬ m.degree h ≤ c

/-- In a reduced basis, divisibility between leading monomials forces the basis elements
to be equal. In particular the leading exponents are pairwise incomparable. -/
theorem IsReducedGroebnerBasis.eq_of_degree_le (hG : m.IsReducedGroebnerBasis G I)
    {g h : MvPolynomial σ R} (hg : g ∈ G) (hh : h ∈ G)
    (hle : m.degree h ≤ m.degree g) : h = g := by
  by_contra hne
  exact hG.not_degree_le g hg _ (m.degree_mem_support (hG.ne_zero g hg)) h hh hne hle

/-- Every leading exponent of a reduced basis occurs in any Gröbner basis of the same ideal.
This expresses minimality of its leading exponents, without assuming the other basis is
reduced or monic. -/
theorem IsReducedGroebnerBasis.exists_degree_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsGroebnerBasis H I) {g : MvPolynomial σ R} (hg : g ∈ G) :
    ∃ h ∈ H, h ≠ 0 ∧ m.degree h = m.degree g := by
  obtain ⟨h, hh, hh0, hhg⟩ := hH.exists_degree_le_degree
    (hG.isGroebnerBasis.subset hg) (hG.ne_zero g hg)
  obtain ⟨g', hg', _, hg'h⟩ := hG.isGroebnerBasis.exists_degree_le_degree (hH.subset hh) hh0
  have heq := hG.eq_of_degree_le hg hg' (hg'h.trans hhg)
  subst g'
  exact ⟨h, hh, hh0, le_antisymm hhg hg'h⟩

/-- The empty set is a reduced monic Gröbner basis of the zero ideal. -/
@[simp]
theorem isReducedGroebnerBasis_empty (m : MonomialOrder σ) :
    m.IsReducedGroebnerBasis (∅ : Set (MvPolynomial σ R)) ⊥ := by
  refine ⟨IsGroebnerBasis.mk (Set.empty_subset _) ?_, by simp, by simp, by simp⟩
  simp

/-- A reduced monic Gröbner basis is empty exactly when its ideal is zero. -/
theorem IsReducedGroebnerBasis.eq_empty_iff (hG : m.IsReducedGroebnerBasis G I) :
    G = ∅ ↔ I = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro p hp
    by_contra hp0
    obtain ⟨g, hg, _⟩ := hG.isGroebnerBasis.exists_degree_le_degree hp hp0
    simp [h] at hg
  · intro h
    apply Set.eq_empty_of_forall_notMem
    intro g hg
    apply hG.ne_zero g hg
    simpa [h] using hG.isGroebnerBasis.subset hg

/-- **Finiteness of reduced Gröbner bases.** In finitely many variables a reduced monic
Gröbner basis is finite. -/
theorem IsReducedGroebnerBasis.finite [Finite σ] (hG : m.IsReducedGroebnerBasis G I) :
    G.Finite := by
  have hinj : Set.InjOn m.degree G := fun _ hg _ hh hgh ↦ hG.eq_of_degree_le hh hg hgh.le
  refine Set.Finite.of_finite_image ?_ hinj
  refine WellQuasiOrderedLE.finite_of_isAntichain ?_
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ hne hle
  exact hne (congrArg m.degree (hG.eq_of_degree_le hh hg hle))

end CommSemiring

section CommRing

variable [CommRing R] {m : MonomialOrder σ}
  {G H : Set (MvPolynomial σ R)} {I J : Ideal (MvPolynomial σ R)}

/-- Elements of two reduced monic Gröbner bases of the same ideal with the same leading
exponent are equal. -/
theorem IsReducedGroebnerBasis.eq_of_degree_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H I) {g h : MvPolynomial σ R} (hg : g ∈ G) (hh : h ∈ H)
    (hdeg : m.degree g = m.degree h) : g = h := by
  classical
  by_contra hne
  have hdiff : g - h ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨b, hb, _, hbd⟩ := hG.isGroebnerBasis.exists_degree_le_degree
    (I.sub_mem (hG.isGroebnerBasis.subset hg) (hH.isGroebnerBasis.subset hh)) hdiff
  have htop : m.degree g ≤ m.degree (g - h) := by
    rcases Finset.mem_union.mp (support_sub σ g h (m.degree_mem_support hdiff)) with hc | hc
    · have hbg : b = g := by
        by_contra hbg
        exact hG.not_degree_le g hg _ hc b hb hbg hbd
      simpa [hbg] using hbd
    · obtain ⟨b', hb', _, hb'd⟩ := hG.exists_degree_eq hH.isGroebnerBasis hb
      have hb'h : b' = h := by
        by_contra hb'h
        exact hH.not_degree_le h hh _ hc b' hb' hb'h (hb'd ▸ hbd)
      rwa [← hb'd, hb'h, ← hdeg] at hbd
  have heq : m.degree (g - h) = m.degree g := m.toSyn.injective <|
    le_antisymm (by simpa [hdeg] using (m.degree_sub_le (f := g) (g := h)))
      (m.toSyn_monotone htop)
  have hz : (g - h).coeff (m.degree g) = 0 := by
    rw [coeff_sub, (hG.monic g hg).coeff_degree, hdeg, (hH.monic h hh).coeff_degree,
      sub_self]
  exact (mem_support_iff.mp (heq ▸ m.degree_mem_support hdiff)) hz

/-- **Uniqueness of the reduced monic Gröbner basis.** Any two reduced monic Gröbner bases
of the same ideal are equal, over an arbitrary commutative coefficient ring. -/
theorem IsReducedGroebnerBasis.eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H I) : G = H := by
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨h, hh, _, hdeg⟩ := hG.exists_degree_eq hH.isGroebnerBasis hg
    exact (hG.eq_of_degree_eq hH hg hh hdeg.symm) ▸ hh
  · intro h hh
    obtain ⟨g, hg, _, hdeg⟩ := hH.exists_degree_eq hG.isGroebnerBasis hh
    exact (hH.eq_of_degree_eq hG hh hg hdeg.symm) ▸ hg

/-- Reduced monic Gröbner bases agree exactly when the ideals they describe agree. -/
theorem IsReducedGroebnerBasis.eq_iff_ideal_eq (hG : m.IsReducedGroebnerBasis G I)
    (hH : m.IsReducedGroebnerBasis H J) : G = H ↔ I = J := by
  refine ⟨fun h ↦ ?_, fun h ↦ hG.eq (h ▸ hH)⟩
  rw [hG.isGroebnerBasis.ideal_eq_span, hH.isGroebnerBasis.ideal_eq_span, h]

/-- **Existence of the reduced monic Gröbner basis.** An ideal with a Gröbner basis whose
nonzero members have unit leading coefficients has a reduced monic Gröbner basis.

For each exponent `a` minimal, for divisibility, among the leading exponents of nonzero elements
of `I`, the basis element is `X^a - r`, where `r` is a remainder of `X^a` on division by `G`. -/
theorem IsGroebnerBasis.exists_isReducedGroebnerBasis (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∃ H, m.IsReducedGroebnerBasis H I := by
  classical
  -- The leading exponents of the nonzero elements of `I`.
  let D : Set (σ →₀ ℕ) := m.degree '' {p | p ∈ I ∧ p ≠ 0}
  choose r hr using fun a : σ →₀ ℕ ↦ exists_isRemainder hG (monomial a (1 : R))
  let red (a : σ →₀ ℕ) : MvPolynomial σ R := monomial a 1 - r a
  have hred {a : σ →₀ ℕ} (ha : a ∈ D) :
      red a ∈ I ∧ red a ≠ 0 ∧ m.degree (red a) = a ∧ m.Monic (red a) := by
    obtain ⟨p, ⟨hp, hp0⟩, rfl⟩ := ha
    exact h.monic_monomial_sub_of_isRemainder (hr _) hp hp0 rfl
  refine ⟨red '' {a | Minimal (· ∈ D) a}, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine (isGroebnerBasis_iff_forall_exists_degree_le_degree ?_).2 ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ -
      rw [(hred ha.prop).2.2.2.leadingCoeff_eq_one]
      exact isUnit_one
    · rintro _ ⟨a, ha, rfl⟩
      exact (hred ha.prop).1
    · intro p hp hp0
      obtain ⟨a, hap, ha⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D) (m.degree p)
        ⟨p, ⟨hp, hp0⟩, rfl⟩
      exact ⟨red a, ⟨a, ha, rfl⟩, (hred ha.prop).2.1, by rw [(hred ha.prop).2.2.1]; exact hap⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (hred ha.prop).2.1
  · rintro _ ⟨a, ha, rfl⟩
    exact (hred ha.prop).2.2.2
  · rintro _ ⟨a, ha, rfl⟩ c hc _ ⟨b, hb, rfl⟩ hne hle
    rw [(hred hb.prop).2.2.1] at hle
    rcases Finset.mem_union.1 (support_sub σ _ _ hc) with hc | hc
    · -- The other leading exponent divides `a`, so by minimality of `a` the two are equal.
      rw [Finset.mem_singleton.1 (support_monomial_subset hc)] at hle
      exact hne (congrArg red (le_antisymm hle (ha.le_of_le hb.prop hle)))
    · obtain ⟨q, ⟨hq, hq0⟩, hqb⟩ := hb.prop
      exact h.not_degree_le_of_isRemainder (hr a) hc hq hq0 (hqb ▸ hle)

end CommRing

section Field

variable {k : Type*} [Field k]

/-- Over a field, every ideal has a reduced monic Gröbner basis. -/
theorem exists_isReducedGroebnerBasis (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ k)) :
    ∃ G, m.IsReducedGroebnerBasis G I :=
  (isGroebnerBasis_self I).exists_isReducedGroebnerBasis fun _ _ hg ↦ m.isUnit_leadingCoeff.2 hg

/-- Over a field, every ideal has exactly one reduced monic Gröbner basis. -/
theorem existsUnique_isReducedGroebnerBasis (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ k)) : ∃! G, m.IsReducedGroebnerBasis G I :=
  let ⟨G, hG⟩ := m.exists_isReducedGroebnerBasis I
  ⟨G, hG, fun _ hH ↦ hH.eq hG⟩

end Field

end MonomialOrder
