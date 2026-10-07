/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Evaluation
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered

/-!
# The ordered Poincaré--Birkhoff--Witt basis

For any ordered basis `b` of a Lie algebra over a commutative ring, the products of its canonical
generators in increasing order form a basis of the enveloping algebra. The indices are finitely
supported natural exponents. The value at an exponent is the corresponding ordered product,
with coefficient `1`, including the empty product `1`.

The evaluation of the polynomial representation gives a linear equivalence with multivariate
polynomials carrying these basis vectors to the usual monomials. This is an equivalence of
modules; the enveloping algebra need not be commutative.

## Main results

* `Module.Basis.pbwBasis`: the ordered monomial basis of the enveloping algebra.
* `Module.Basis.pbwBasis_eq_prod_pow`: its value as the increasing product of generator powers.
* `Module.Basis.pbwEquiv`: the linear equivalence with multivariate polynomials.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace Module.Basis

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The ordered monomial with exponent vector `n`: repeat each generator `n i` times and
multiply the resulting word in increasing order. -/
private noncomputable def pbwBasisMonomial (n : ι →₀ ℕ) : U :=
  pbwMonomial R L b (n.toMultiset.sort (· ≤ ·))

/-- The ordered-word formula for a PBW basis monomial. -/
private theorem pbwBasisMonomial_def (n : ι →₀ ℕ) :
    b.pbwBasisMonomial n = pbwMonomial R L b (n.toMultiset.sort (· ≤ ·)) :=
  (rfl)

@[simp]
private theorem pbwBasisMonomial_zero : b.pbwBasisMonomial 0 = 1 := by
  simp [pbwBasisMonomial, Finsupp.toMultiset_zero]

/-- Ordered words are precisely the monomials indexed by their multiplicities. -/
private theorem pbwBasisMonomial_toFinsupp {word : List ι} (hword : word.Pairwise (· ≤ ·)) :
    b.pbwBasisMonomial (Multiset.toFinsupp (word : Multiset ι)) = pbwMonomial R L b word := by
  rw [pbwBasisMonomial_def, Multiset.toFinsupp_toMultiset, Multiset.coe_sort,
    List.mergeSort_eq_self (· ≤ ·) hword]

@[simp]
private theorem pbwEval_pbwBasisMonomial (n : ι →₀ ℕ) :
    b.pbwEval (b.pbwBasisMonomial n) = monomial n 1 := by
  rw [pbwBasisMonomial_def, pbwEval_pbwMonomial b (Multiset.pairwise_sort _ _),
    Multiset.sort_eq, Finsupp.toMultiset_toFinsupp]

/-- The ordered monomials in a basis are linearly independent. -/
private theorem linearIndependent_pbwBasisMonomial : LinearIndependent R b.pbwBasisMonomial := by
  apply LinearIndependent.of_comp b.pbwEval
  simpa [Function.comp_def] using (basisMonomials ι R).linearIndependent

/-- The ordered monomials in a basis span the enveloping algebra. -/
private theorem span_range_pbwBasisMonomial :
    Submodule.span R (Set.range b.pbwBasisMonomial) = ⊤ := by
  apply top_unique
  rw [← span_iUnion_orderedPBWMonomials_eq_top R L b b.span_eq]
  apply Submodule.span_mono
  intro a ha
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ha
  obtain ⟨word, hword, _, rfl⟩ := (mem_orderedPBWMonomials_iff R L b).1 hk
  exact ⟨Multiset.toFinsupp (word : Multiset ι), b.pbwBasisMonomial_toFinsupp hword⟩

/-- The Poincaré--Birkhoff--Witt basis: ordered monomials in a chosen basis of the Lie algebra,
over an arbitrary commutative ring. -/
noncomputable def pbwBasis : Basis (ι →₀ ℕ) R U :=
  Basis.mk b.linearIndependent_pbwBasisMonomial b.span_range_pbwBasisMonomial.ge

private theorem pbwBasis_apply_aux (n : ι →₀ ℕ) : b.pbwBasis n = b.pbwBasisMonomial n :=
  Basis.mk_apply _ _ n

/-- The basis vector at `n` is the word containing `n i` copies of each generator, sorted in
increasing order. -/
theorem pbwBasis_apply (n : ι →₀ ℕ) :
    b.pbwBasis n = pbwMonomial R L b (n.toMultiset.sort (· ≤ ·)) := by
  rw [pbwBasis_apply_aux, pbwBasisMonomial_def]

@[simp]
theorem pbwBasis_zero : b.pbwBasis 0 = 1 := by
  rw [pbwBasis_apply_aux, pbwBasisMonomial_zero]

/-- PBW evaluation sends each ordered basis vector to the corresponding polynomial monomial. -/
@[simp]
theorem pbwEval_pbwBasis (n : ι →₀ ℕ) : b.pbwEval (b.pbwBasis n) = monomial n 1 := by
  rw [pbwBasis_apply_aux, pbwEval_pbwBasisMonomial]

/-- The PBW evaluation is bijective: it carries the ordered basis to the polynomial basis. -/
theorem pbwEval_bijective : Function.Bijective b.pbwEval := by
  have h : b.pbwEval = b.pbwBasis.equiv (basisMonomials ι R) (Equiv.refl _) := by
    apply b.pbwBasis.ext
    intro n
    calc
      b.pbwEval (b.pbwBasis n) = basisMonomials ι R n := by simp
      _ = _ := (Basis.equiv_apply b.pbwBasis n (basisMonomials ι R) (Equiv.refl _)).symm
  rw [h]
  exact (b.pbwBasis.equiv (basisMonomials ι R) (Equiv.refl _)).bijective

/-- The linear PBW equivalence with polynomials, normalized by the ordered monomial basis. -/
noncomputable def pbwEquiv : U ≃ₗ[R] MvPolynomial ι R :=
  LinearEquiv.ofBijective b.pbwEval b.pbwEval_bijective

@[simp]
theorem pbwEquiv_apply (a : U) : b.pbwEquiv a = b.pbwEval a :=
  (rfl)

@[simp]
theorem pbwEquiv_symm_monomial (n : ι →₀ ℕ) :
    b.pbwEquiv.symm (monomial n 1) = b.pbwBasis n := by
  apply b.pbwEquiv.injective
  simp

/-- The basis vector at `n` is the product of `ι(b i) ^ n i`, with the support traversed in
increasing order. No commutativity of the enveloping algebra is assumed. -/
theorem pbwBasis_eq_prod_pow (n : ι →₀ ℕ) :
    b.pbwBasis n = ((n.support.sort (· ≤ ·)).map
      (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ n i)).prod := by
  let indices := n.support.sort (· ≤ ·)
  let word := indices.flatMap fun i ↦ List.replicate (n i) i
  have hword : word.Pairwise (· ≤ ·) := by
    apply List.pairwise_flatMap.2
    refine ⟨fun i _ ↦ List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
    exact (Finset.pairwise_sort _ _).imp fun {i j} hij x hx y hy ↦ by
      simpa [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy] using hij
  have hmult : Multiset.toFinsupp (word : Multiset ι) = n := by
    have haux (l : List ι) :
        Multiset.toFinsupp ((l.flatMap fun i ↦ List.replicate (n i) i) : Multiset ι) =
          (l.map fun i ↦ Finsupp.single i (n i)).sum := by
      induction l with
      | nil => simp [Multiset.toFinsupp_zero]
      | cons i l ih =>
          simp only [List.flatMap_cons, ← Multiset.coe_add, Multiset.toFinsupp_add,
            List.map_cons, List.sum_cons, ih]
          congr 1
          ext j
          by_cases hij : i = j
          · subst j
            simp
          · simp [Multiset.toFinsupp_apply, List.count_replicate, hij]
    rw [haux]
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
    exact Finsupp.sum_single n
  have hprod : pbwMonomial R L b word = ((indices.map
      (fun i ↦ _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ n i))).prod := by
    rw [pbwMonomial_def, List.map_map, List.map_flatMap]
    induction indices with
    | nil => simp
    | cons i indices ih =>
        rw [List.flatMap_cons, List.prod_append, ih]
        simp only [List.map_cons, List.prod_cons, List.map_replicate, List.prod_replicate,
          Function.comp_apply]
  rw [← hprod, ← b.pbwBasisMonomial_toFinsupp hword, hmult, pbwBasis_apply_aux]

@[simp]
theorem pbwBasis_single (i : ι) (k : ℕ) :
    b.pbwBasis (Finsupp.single i k) = _root_.UniversalEnvelopingAlgebra.ι R (b i) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [pbwBasis_eq_prod_pow]
    simp [Finsupp.support_single _ hk]

end Module.Basis
