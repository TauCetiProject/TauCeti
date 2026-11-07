/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Basic
public import Mathlib.Algebra.Group.Submonoid.Finsupp

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
  classical
  have hspan := h.mem_span hf
  -- Keep the target exponent fixed during span induction, so cancellation in a sum does not
  -- change the bounds imposed on the expression being constructed.
  refine Submodule.span_induction (p := fun g _ ↦
    ∃ Q : MvPolynomial ι k, aeval b Q = g ∧
      ∀ u ∈ Q.support, Finsupp.linearCombination ℕ (m.degree ∘ b) u ≼[m] m.degree f)
    ?_ ?_ ?_ ?_ hspan
  · intro g hg
    obtain ⟨u, rfl⟩ := Submonoid.mem_closure_range_iff.1 hg.1
    refine ⟨monomial u (1 : k), ?_, ?_⟩
    · simp [aeval_monomial]
    · intro v hv
      have hvu : u = v := by simpa using hv
      subst v
      rw [← m.degree_aeval_monomial_one_of_ne_zero hb]
      simpa [aeval_monomial] using hg.2
  · exact ⟨0, by simp, by simp⟩
  · intro g₁ g₂ _ _ ih₁ ih₂
    obtain ⟨Q₁, hQ₁, hbound₁⟩ := ih₁
    obtain ⟨Q₂, hQ₂, hbound₂⟩ := ih₂
    refine ⟨Q₁ + Q₂, by simp [hQ₁, hQ₂], fun u hu ↦ ?_⟩
    rcases Finset.mem_union.1 (support_add hu) with hu | hu
    · exact hbound₁ u hu
    · exact hbound₂ u hu
  · intro c g _ ih
    obtain ⟨Q, hQ, hbound⟩ := ih
    exact ⟨c • Q, by simp [hQ], fun u hu ↦ hbound u (support_smul hu)⟩

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
