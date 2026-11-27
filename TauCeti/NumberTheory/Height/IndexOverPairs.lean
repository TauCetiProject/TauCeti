/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.NumberTheory.Height.FamilyOverPairs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.LinearAlgebra.Matrix.Module

/-!
# Index bounds over prime-adic embeddings

Given a local integral submodule at each prime-adic embedding of `ℂ`, a finite family has
index at most `δ` if it can be made integral at every embedding by an integral matrix, with
logarithmic determinant losses of total size at most `δ`. The loss budget at a prime is
common to all embeddings at that prime. In applications the local submodules can themselves
be intersections of integral conditions, so the same matrix works for all those conditions.

Index bounds are independent of numbering. They add when concatenating families, and hence
when a family is drawn from a finite union of sets with uniform index bounds.

## References

The determinant index and the finite-union bound follow the statements of `New.TwistedLattice`
(`IndexLe`, `IndexLe.sumElim`, `indexLe_card_mul`) in `New/Reduction/Lattices/TwistedLattice.lean`
of [grh-lean](https://github.com/lsernau/grh-lean) at `72fead102f663d5c7a407964a13dc0cf9d977207`.
Here the index only takes the local integral submodules, not the maps producing them.
-/

public section

open Finset Matrix

namespace TauCeti.PrimePadicIso

universe u

variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
variable {I : Type u} {J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- A determinant index bound for a finite family relative to local integral submodules `L`.
At each embedding `ι`, a matrix over `ι.integers` puts every row combination in `L ι`.
The exponent in the determinant lower bound depends only on the prime, and the sum of these
exponents weighted by `log ℓ` over any finite set of primes is at most `δ`. -/
def IndexLe (L : (ι : PrimePadicIso) → Submodule ι.integers V) (y : I → V) (δ : ℝ) : Prop :=
  ∃ d : ℕ → ℝ, (∀ p : ℕ, p.Prime → 0 ≤ d p) ∧
    (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∑ p ∈ S, d p * Real.log p ≤ δ) ∧
    ∀ ι : PrimePadicIso, ∃ A : Matrix I I ι.integers,
      (ι.prime : ℝ) ^ (-d ι.prime) ≤ ‖ι.iso (A.det : ℂ)‖ ∧
      ∀ i, (∑ j, A i j • y j) ∈ L ι

variable {L : (ι : PrimePadicIso) → Submodule ι.integers V}
variable {y : I → V} {z : J → V} {δ δ' : ℝ}

/-- Characterize the index bound by its prime budgets and local matrices. -/
theorem indexLe_iff : IndexLe L y δ ↔
    ∃ d : ℕ → ℝ, (∀ p : ℕ, p.Prime → 0 ≤ d p) ∧
      (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∑ p ∈ S, d p * Real.log p ≤ δ) ∧
      ∀ ι : PrimePadicIso, ∃ A : Matrix I I ι.integers,
        (ι.prime : ℝ) ^ (-d ι.prime) ≤ ‖ι.iso (A.det : ℂ)‖ ∧
        ∀ i, (∑ j, A i j • y j) ∈ L ι := (Iff.rfl)

/-- Index bounds increase with the allowed loss. -/
theorem IndexLe.mono (h : IndexLe L y δ) (hle : δ ≤ δ') : IndexLe L y δ' := by
  obtain ⟨d, hd, hsum, hA⟩ := indexLe_iff.mp h
  exact indexLe_iff.mpr ⟨d, hd, fun S hS ↦ (hsum S hS).trans hle, hA⟩

/-- A valid index bound is nonnegative, including for the empty family. -/
theorem IndexLe.nonneg (h : IndexLe L y δ) : 0 ≤ δ := by
  obtain ⟨d, _, hsum, _⟩ := indexLe_iff.mp h
  simpa using hsum ∅ (by simp)

/-- A family has index at most zero exactly when it is already integral at every embedding. -/
@[simp]
theorem indexLe_zero_iff : IndexLe L y 0 ↔ ∀ ι i, y i ∈ L ι := by
  constructor
  · intro h ι i
    obtain ⟨d, hd, hsum, hA⟩ := indexLe_iff.mp h
    -- The budget of the singleton prime forces zero loss, so the row matrix is invertible.
    have hp := ι.fact_prime.out
    have hpLog : 0 < Real.log (ι.prime : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hd' : d ι.prime * Real.log ι.prime ≤ 0 := by
      simpa using hsum {ι.prime} (by simpa)
    have hzero : d ι.prime = 0 := le_antisymm (nonpos_of_mul_nonpos_left hd' hpLog) (hd _ hp)
    obtain ⟨A, hdet, hrows⟩ := hA ι
    have hdet' : 1 ≤ ‖ι.iso (A.det : ℂ)‖ := by simpa [hzero] using hdet
    have hunit : IsUnit A.det := isUnit_iff_norm_iso_eq_one.mpr
      (le_antisymm (mem_integers.mp A.det.property) hdet')
    obtain ⟨B, hB⟩ := isUnit_iff_exists_inv'.mp ((Matrix.isUnit_iff_isUnit_det A).mpr hunit)
    have hmem : (∑ j, (B * A) i j • y j) ∈ L ι := by
      rw [Matrix.sum_mul_apply_smul]
      exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hrows j)
    simpa [hB, Matrix.one_apply, ite_smul] using hmem
  · intro hy
    refine indexLe_iff.mpr ⟨0, by simp, by simp, fun ι ↦ ⟨1, by simp, fun i ↦ ?_⟩⟩
    simpa [Matrix.one_apply, ite_smul] using hy ι i

private theorem indexLe_comp_equiv (h : IndexLe L y δ) (e : J ≃ I) : IndexLe L (y ∘ e) δ := by
  obtain ⟨d, hd, hsum, hA⟩ := indexLe_iff.mp h
  refine indexLe_iff.mpr ⟨d, hd, hsum, fun ι ↦ ?_⟩
  obtain ⟨A, hdet, hrows⟩ := hA ι
  refine ⟨A.reindex e.symm e.symm, by simpa only [Matrix.det_reindex_self] using hdet, fun i ↦ ?_⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Function.comp_apply]
  rw [e.sum_comp (fun j ↦ A (e i) j • y j)]
  exact hrows (e i)

/-- Renumbering a family by an equivalence does not change whether it satisfies an index bound. -/
@[simp]
theorem indexLe_comp_equiv_iff (e : J ≃ I) : IndexLe L (y ∘ e) δ ↔ IndexLe L y δ := by
  refine ⟨fun h ↦ ?_, fun h ↦ indexLe_comp_equiv h e⟩
  simpa [Function.comp_assoc] using indexLe_comp_equiv h e.symm

/-- The index bound of a concatenated family is at most the sum of the two bounds. -/
theorem IndexLe.sumElim (hy : IndexLe L y δ) (hz : IndexLe L z δ') :
    IndexLe L (Sum.elim y z) (δ + δ') := by
  obtain ⟨d, hd, hsum, hA⟩ := indexLe_iff.mp hy
  obtain ⟨d', hd', hsum', hB⟩ := indexLe_iff.mp hz
  refine indexLe_iff.mpr ⟨fun p ↦ d p + d' p, fun p hp ↦ add_nonneg (hd p hp) (hd' p hp),
    fun S hS ↦ ?_, fun ι ↦ ?_⟩
  · simpa only [add_mul, Finset.sum_add_distrib] using add_le_add (hsum S hS) (hsum' S hS)
  obtain ⟨A, hdetA, hrowsA⟩ := hA ι
  obtain ⟨B, hdetB, hrowsB⟩ := hB ι
  refine ⟨fromBlocks A 0 0 B, ?_, ?_⟩
  · have hp : (0 : ℝ) < ι.prime := by exact_mod_cast ι.fact_prime.out.pos
    rw [neg_add, Real.rpow_add hp, det_fromBlocks_zero₂₁, Subring.coe_mul, map_mul, norm_mul]
    exact mul_le_mul hdetA hdetB (by positivity) (norm_nonneg _)
  · rintro (i | j)
    · simpa [Fintype.sum_sum_type] using hrowsA i
    · simpa [Fintype.sum_sum_type] using hrowsB j

/-- If each member of a finite collection of sets gives a uniform index bound on its finite
families, the sum of the individual bounds is an index bound for families in the union. -/
theorem indexLe_of_mem_biUnion {κ : Type*} (S : Finset κ) {A : κ → Set V} {d : κ → ℝ}
    (hA : ∀ k ∈ S, ∀ {J : Type u} [Fintype J] [DecidableEq J] (z : J → V),
      (∀ j, z j ∈ A k) → IndexLe L z (d k))
    (hy : ∀ i, y i ∈ ⋃ k ∈ S, A k) : IndexLe L y (∑ k ∈ S, d k) := by
  classical
  induction S using Finset.induction_on generalizing I with
  | empty =>
    rw [Finset.sum_empty, indexLe_zero_iff]
    intro _ i
    simpa using hy i
  | @insert k S hk ih =>
    let e := Equiv.sumCompl (fun i ↦ y i ∈ A k)
    have h₁ := hA k (mem_insert_self k S) (fun i : {i // y i ∈ A k} ↦ y i) Subtype.property
    have h₂ : IndexLe L (fun i : {i // y i ∉ A k} ↦ y i) (∑ l ∈ S, d l) := by
      apply ih (fun l hl ↦ hA l (mem_insert_of_mem hl))
      intro i
      simpa [Finset.mem_insert, i.property] using hy i
    have hcomp : (Sum.elim (fun i : {i // y i ∈ A k} ↦ y i)
        (fun i : {i // y i ∉ A k} ↦ y i)) ∘ e.symm = y := by
      symm
      rw [Equiv.eq_comp_symm]
      funext i
      cases i <;> simp [e, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    rw [sum_insert hk, ← hcomp]
    exact (indexLe_comp_equiv_iff e.symm).mpr (h₁.sumElim h₂)

end TauCeti.PrimePadicIso
