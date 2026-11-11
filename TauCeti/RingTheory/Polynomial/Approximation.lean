/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Set.Countable

/-!
# Countable approximation of bounded-degree polynomials modulo ideals

Over a ring, if the quotients by the ideals of a countable family are countable, every set of
polynomials of bounded degree has a countable subset that approximates each of its members
coefficientwise modulo every ideal of the family. The approximants stay in the original set,
so constraints such as monicity or the Eisenstein condition are preserved without separate
stability arguments.

The main case is the family of powers of one ideal, which gives countable families of defining
polynomials when root counts are locally constant under ideal-adic perturbations. No topology
on the coefficient ring is required.
-/

public section

open Polynomial

namespace Ideal

variable {R : Type*} [Ring R]

/-- A set of polynomials of bounded degree has a countable subset approximating all its members
coefficientwise modulo every ideal of a countable family whose quotients are countable.
The approximants belong to the given set.
-/
theorem exists_countable_polynomial_approximations {ι : Type*} [Countable ι]
    (I : ι → Ideal R) (hI : ∀ k, Countable (R ⧸ I k))
    (s : Set R[X]) {n : ℕ} (hn : ∀ f ∈ s, f.natDegree ≤ n) :
    ∃ t ⊆ s, t.Countable ∧ ∀ f ∈ s, ∀ k, ∃ g ∈ t, ∀ i, g.coeff i - f.coeff i ∈ I k := by
  -- For each `k`, keep one member of `s` for each residue vector of the first `n + 1`
  -- coefficients that occurs; there are only countably many such vectors.
  choose u hus hu using fun k ↦ s.exists_subset_bijOn
    fun (f : R[X]) (i : Fin (n + 1)) ↦ Submodule.Quotient.mk (p := I k) (f.coeff i)
  refine ⟨⋃ k, u k, Set.iUnion_subset hus, Set.countable_iUnion fun k ↦ ?_, fun f hf k ↦ ?_⟩
  · have := hI k
    exact Set.countable_of_injective_of_countable_image (hu k).injOn (Set.to_countable _)
  obtain ⟨g, hg, hgf⟩ := (hu k).surjOn (Set.mem_image_of_mem _ hf)
  refine ⟨g, Set.mem_iUnion_of_mem k hg, fun i ↦ ?_⟩
  by_cases hi : i ≤ n
  · exact (Submodule.Quotient.eq _).mp (congrFun hgf ⟨i, Nat.lt_succ_of_le hi⟩)
  · -- Beyond degree `n`, both coefficients vanish.
    have hgi : g.coeff i = 0 :=
      coeff_eq_zero_of_natDegree_lt ((hn g (hus k hg)).trans_lt (by omega))
    have hfi : f.coeff i = 0 := coeff_eq_zero_of_natDegree_lt ((hn f hf).trans_lt (by omega))
    simp [hgi, hfi]

end Ideal
