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

For an arbitrary SAGBI set, `IsSAGBIBasis.mem_span` gives the corresponding bounded linear
combination of products. These representations characterize SAGBI bases
(`isSAGBIBasis_iff_forall_mem_span`) and imply that a SAGBI basis generates its algebra
(`IsSAGBIBasis.adjoin_eq`).

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

variable {B : Set (MvPolynomial σ k)}

/-- **Subduction.** Every element `f` of a subalgebra `A` with SAGBI basis `B` is a `k`-linear
combination of products of elements of `B` whose leading exponents are at most that of `f`. -/
theorem IsSAGBIBasis.mem_span (h : m.IsSAGBIBasis B A) (hf : f ∈ A) :
    f ∈ Submodule.span k {g ∈ Submonoid.closure B | m.degree g ≼[m] m.degree f} := by
  classical
  let b : ↥(B \ {0}) → MvPolynomial σ k := Subtype.val
  have hrange : Set.range b = B \ {0} := Subtype.range_coe_subtype
  have hb : ∀ i, b i ≠ 0 := fun i ↦ i.property.2
  have hB : m.IsSAGBIBasis (Set.range b) A := by
    rw [hrange]
    exact isSAGBIBasis_sdiff_singleton_zero.2 h
  obtain ⟨Q, hQ, hbound⟩ := hB.exists_aeval_eq_support_le hb hf
  suffices aeval b Q ∈
      Submodule.span k {g ∈ Submonoid.closure B | m.degree g ≼[m] m.degree f} by
    rwa [hQ] at this
  rw [Q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun u hu ↦ ?_
  have hprod : aeval b (monomial u (1 : k)) ∈ Submonoid.closure B := by
    rw [aeval_monomial, map_one, one_mul]
    exact Submonoid.prod_mem _ fun i _ ↦
      pow_mem (Submonoid.subset_closure i.property.1) _
  have hdegree : m.degree (aeval b (monomial u (1 : k))) ≼[m] m.degree f := by
    rw [m.degree_aeval_monomial_one_of_ne_zero hb]
    exact hbound u hu
  have hmem : aeval b (monomial u (1 : k)) ∈
      Submodule.span k {g ∈ Submonoid.closure B | m.degree g ≼[m] m.degree f} :=
    Submodule.subset_span ⟨hprod, hdegree⟩
  simpa only [← map_smul, smul_monomial, smul_eq_mul, mul_one] using
    Submodule.smul_mem _ (Q.coeff u) hmem

/-- Over a field, `B ⊆ A` is a SAGBI basis of `A` if and only if every element `f` of `A` is a
`k`-linear combination of products of elements of `B` whose leading exponents are at most that
of `f`. -/
theorem isSAGBIBasis_iff_forall_mem_span :
    m.IsSAGBIBasis B A ↔ B ⊆ A ∧
      ∀ f ∈ A, f ∈ Submodule.span k {g ∈ Submonoid.closure B | m.degree g ≼[m] m.degree f} := by
  refine ⟨fun h ↦ ⟨h.subset, fun f ↦ h.mem_span⟩, fun ⟨hBA, h⟩ ↦
    isSAGBIBasis_iff_exists_mem_closure.2 ⟨hBA, fun f hf hf0 ↦ ?_⟩⟩
  -- Otherwise every product in the representation of `f` has vanishing coefficient at the leading
  -- exponent of `f`, and so does `f`.
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hker : Submodule.span k {g ∈ Submonoid.closure B | m.degree g ≼[m] m.degree f} ≤
      LinearMap.ker (lcoeff k (m.degree f)) := by
    refine Submodule.span_le.2 fun g ⟨hg, hgf⟩ ↦ ?_
    rw [SetLike.mem_coe, LinearMap.mem_ker, lcoeff_apply]
    by_contra hc
    exact hne g hg (fun h0 ↦ hc (by simp [h0]))
      (m.toSyn.injective (le_antisymm hgf (m.le_degree (mem_support_iff.2 hc))))
  have hf' := hker (h f hf)
  rw [LinearMap.mem_ker, lcoeff_apply] at hf'
  exact hf0 (m.coeff_degree_eq_zero_iff.1 hf')

/-- A SAGBI basis of `A` generates `A` as a `k`-algebra. -/
theorem IsSAGBIBasis.adjoin_eq (h : m.IsSAGBIBasis B A) : Algebra.adjoin k B = A := by
  refine le_antisymm (Algebra.adjoin_le h.subset) fun f hf ↦ ?_
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span]
  exact Submodule.span_mono (Set.sep_subset _ _) (h.mem_span hf)

end MonomialOrder
