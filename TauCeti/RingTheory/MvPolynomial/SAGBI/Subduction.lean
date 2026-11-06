/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Remainder

/-!
# Polynomial certificates for SAGBI subduction

For an indexed nonzero SAGBI family `b`, every element of its subalgebra has a polynomial
expression whose monomials substitute to products with leading exponent at most that of the
element. The bound is on each exponent in the expression's support, not just on the degree of
its substituted value. Such bounds are needed to lift binomial relations among leading
monomials to relations among the generators.

If the element is zero or has leading exponent strictly below a given bound, we construct a
strict subduction certificate, taking the zero polynomial when the element vanishes. This
also covers scalar generators and bounds of exponent zero, without asserting a strict bound
on the totalized degree of zero. The binomial certificates for monic families are provided in
`TauCeti.RingTheory.MvPolynomial.SAGBI.Criterion`.

## References

* W. Bruns, A. Conca, F. Lembo, *Sagbi bases, defining equations and algebras of minors*,
  arXiv:2504.10019, §2.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, Chapter 11.
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ ι k : Type*} [Field k] {m : MonomialOrder σ}
  {b : ι → MvPolynomial σ k} {A : Subalgebra k (MvPolynomial σ k)}
  {f : MvPolynomial σ k}

/-- Subduction in an indexed nonzero SAGBI family produces a polynomial expression with an
explicit bound on every substituted monomial's leading exponent. The family need not be
finite or monic. -/
theorem IsSAGBIBasis.exists_aeval_eq_support_le
    (h : m.IsSAGBIBasis (Set.range b) A) (hb : ∀ i, b i ≠ 0) (hf : f ∈ A) :
    ∃ Q : MvPolynomial ι k, aeval b Q = f ∧
      ∀ u ∈ Q.support, Finsupp.linearCombination ℕ (m.degree ∘ b) u ≼[m] m.degree f := by
  obtain ⟨Q, r, hs⟩ := m.exists_isSubduction hb f
  exact ⟨Q, by simpa [hs.remainder_eq_zero h hf] using hs.eq_aeval_add.symm, hs.support_le⟩

/-- If an element of a SAGBI subalgebra is zero or has leading exponent below `a`, it has an
expression all of whose substituted monomials have leading exponent strictly below `a`.
The zero case is certified by the empty support, including when `a = 0`. -/
theorem IsSAGBIBasis.exists_aeval_eq_support_lt
    (h : m.IsSAGBIBasis (Set.range b) A) (hb : ∀ i, b i ≠ 0) (hf : f ∈ A)
    {a : σ →₀ ℕ} (hfa : f = 0 ∨ m.degree f ≺[m] a) :
    ∃ Q : MvPolynomial ι k, aeval b Q = f ∧
      ∀ u ∈ Q.support, Finsupp.linearCombination ℕ (m.degree ∘ b) u ≺[m] a := by
  rcases hfa with rfl | hfa
  · exact ⟨0, by simp, by simp⟩
  · obtain ⟨Q, hQ, hbound⟩ := h.exists_aeval_eq_support_le hb hf
    exact ⟨Q, hQ, fun u hu ↦ (hbound u hu).trans_lt hfa⟩

end MonomialOrder
