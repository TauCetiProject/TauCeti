/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Set.Countable

/-!
# Countable ideal-adic approximation of bounded-degree polynomials

Over a commutative ring, if the quotients by powers of an ideal are countable, every set of
polynomials of bounded degree has a countable subset that approximates each of its members
coefficientwise modulo every power of that ideal. The approximants stay in the original set,
so constraints such as monicity or the Eisenstein condition are preserved without separate
stability arguments.

This gives countable families of defining polynomials when root counts are locally constant
under ideal-adic perturbations. No topology on the coefficient ring is required.
-/

public section

open Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A set of polynomials of bounded degree has a countable subset approximating all its members
coefficientwise modulo every power of an ideal whose power quotients are countable.
The approximants belong to the given set.
-/
theorem _root_.Ideal.exists_countable_polynomial_approximations (I : Ideal R)
    (hI : ∀ k : ℕ, Countable (R ⧸ I ^ k))
    (s : Set R[X]) {n : ℕ} (hn : ∀ f ∈ s, f.natDegree ≤ n) :
    ∃ t ⊆ s, t.Countable ∧ ∀ f ∈ s, ∀ k : ℕ, ∃ g ∈ t,
      ∀ i, g.coeff i - f.coeff i ∈ I ^ k := by
  classical
  have (k : ℕ) : Countable (R ⧸ I ^ k) := hI k
  -- There are only countably many residue vectors at each precision. Choose representatives
  -- only from the specified set, leaving an arbitrary value at unrealized vectors.
  let residue (k : ℕ) (f : R[X]) : Fin (n + 1) → R ⧸ I ^ k :=
    fun i ↦ Ideal.Quotient.mk (I ^ k) (f.coeff i)
  have hex (k : ℕ) (q : Fin (n + 1) → R ⧸ I ^ k) :
      ∃ g : R[X], (∃ f ∈ s, residue k f = q) → g ∈ s ∧ residue k g = q := by
    by_cases h : ∃ f ∈ s, residue k f = q
    · obtain ⟨f, hf, hq⟩ := h
      exact ⟨f, fun _ ↦ ⟨hf, hq⟩⟩
    · exact ⟨0, fun h' ↦ (h h').elim⟩
  choose g hg using hex
  refine ⟨s ∩ ⋃ k, Set.range (g k), Set.inter_subset_left, ?_, ?_⟩
  · exact (Set.countable_iUnion fun k ↦ Set.countable_range (g k)).mono
      Set.inter_subset_right
  intro f hf k
  have h := hg k (residue k f) ⟨f, hf, rfl⟩
  refine ⟨g k (residue k f), ⟨h.1, Set.mem_iUnion.mpr ⟨k, Set.mem_range_self _⟩⟩,
    fun i ↦ ?_⟩
  by_cases hi : i ≤ n
  · exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      (congrFun h.2 ⟨i, Nat.lt_succ_of_le hi⟩)
  · have hgi : (g k (residue k f)).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hn _ h.1).trans_lt (by omega))
    have hfi : f.coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hn f hf).trans_lt (by omega))
    simp [hgi, hfi]

end TauCeti
