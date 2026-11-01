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

For monic generators, a binomial whose two monomials have the same substituted leading
exponent has a substituted value which is zero or has strictly smaller leading exponent.
We construct a strict subduction certificate in both cases, taking the zero polynomial when
the substituted relation vanishes. This also covers scalar generators and relations of
exponent zero, without asserting a strict bound on the totalized degree of zero.

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
      rw [← m.degree_aeval_monomial_one hb]
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

/-- **Necessary bounded SAGBI certificates.** Every coefficient-one binomial relation among
leading monomials of a monic SAGBI family admits a polynomial zero-subduction expression
strictly below its common exponent. Exact-zero substitutions admit the zero expression. -/
theorem IsSAGBIBasis.exists_aeval_eq_aeval_monomial_sub_monomial_support_lt
    (h : m.IsSAGBIBasis (Set.range b) A) (hb : ∀ i, m.Monic (b i))
    (u v : ι →₀ ℕ) (huv : Finsupp.linearCombination ℕ (m.degree ∘ b) u =
      Finsupp.linearCombination ℕ (m.degree ∘ b) v) :
    ∃ Q : MvPolynomial ι k,
      aeval b Q = aeval b (monomial u (1 : k) - monomial v 1) ∧
      ∀ w ∈ Q.support, Finsupp.linearCombination ℕ (m.degree ∘ b) w ≺[m]
        Finsupp.linearCombination ℕ (m.degree ∘ b) u := by
  have hf : aeval b (monomial u (1 : k) - monomial v 1) ∈ A := by
    apply (Algebra.adjoin_le h.subset)
    rw [← aeval_range]
    exact AlgHom.mem_range_self _ _
  exact h.exists_aeval_eq_support_lt (fun i ↦ (hb i).ne_zero) hf
    (m.aeval_monomial_sub_monomial_eq_zero_or_degree_lt hb u v huv)

end MonomialOrder
