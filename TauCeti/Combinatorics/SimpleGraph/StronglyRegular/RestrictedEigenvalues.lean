/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdjMatrix.RestrictedEigenvalues
public import TauCeti.Combinatorics.SimpleGraph.StronglyRegular.Basic

import Mathlib.Tactic.Module

/-!
# Restricted eigenvalues of a strongly regular graph

A regular graph with both an edge and a distinct nonadjacent pair is strongly regular exactly
when it has exactly two distinct restricted eigenvalues.

The argument uses Mathlib's `LinearMap.IsSymmetric.apply_eigenvectorBasis` for the action on an
orthonormal eigenbasis and `Module.End.aeval_apply_of_mem_apply_eq_smul` for polynomial evaluation
on eigenvectors. The resulting polynomial identities are related to strong regularity by
`SimpleGraph.isSRGWith_iff_adjMatrix_sq_eq` and
`SimpleGraph.exists_isSRGWith_iff_exists_adjMatrix_sq_eq`.

## References

* A. E. Brouwer and W. H. Haemers, *Spectra of Graphs*, Universitext, Springer, 2012,
  Theorem 9.1.2 (i) and (iii), p. 117, formulated here for regular graphs.
-/

public section

open Matrix Polynomial
open scoped Polynomial

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

local notation "A" => G.adjMatrix ℝ
local notation "J" => (Matrix.of (fun _ _ ↦ (1 : ℝ)) : Matrix V V ℝ)

/-- A strongly regular graph with an edge and a pair of distinct nonadjacent vertices has
exactly two restricted eigenvalues. -/
theorem IsSRGWith.ncard_restrictedEigenvalues {n ℓ μ : ℕ} (h : G.IsSRGWith n k ℓ μ)
    (htop : G ≠ ⊤) (hbot : G ≠ ⊥) : G.restrictedEigenvalues.ncard = 2 := by
  classical
  let a := (ℓ : ℝ) - μ
  let b := (k : ℝ) - μ
  let p := X ^ 2 - a • X - C b
  have hA := (isSRGWith_iff_adjMatrix_sq_eq (R := ℝ)).mp h |>.2
  have hp : aeval A p = (μ : ℝ) • J := by
    simp only [p, map_sub, map_pow, map_smul, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, hA, a, b]
    module
  have hdeg : p.natDegree = 2 := by
    have ha := natDegree_smul_le a (X : ℝ[X])
    simp only [natDegree_X] at ha
    have hquad : ((X : ℝ[X]) ^ 2 - a • X).natDegree = 2 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
      simpa only [natDegree_X_pow] using ha.trans_lt (by decide : 1 < 2)
    dsimp only [p]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hquad]
    simp [hquad]
  have hp₀ : p ≠ 0 := by
    intro hp₀
    simp [hp₀] at hdeg
  have hsub : G.restrictedEigenvalues ⊆ p.rootSet ℝ := fun t ht ↦ by
    rw [mem_rootSet_of_ne hp₀, coe_aeval_eq_eval]
    exact isRoot_of_mem_restrictedEigenvalues_of_aeval_eq_smul hp ht
  have hle := (Set.ncard_le_ncard hsub (p.rootSet_finite ℝ)).trans (p.ncard_rootSet_le ℝ)
  have hlt := Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
    ⟨restrictedEigenvalues_nontrivial h.regular htop hbot, (p.rootSet_finite ℝ).subset hsub⟩
  omega

/-- A regular graph with exactly two restricted eigenvalues is strongly regular. -/
theorem exists_isSRGWith_of_ncard_restrictedEigenvalues (hk : G.IsRegularOfDegree k)
    (hs : G.restrictedEigenvalues.ncard = 2) :
    ∃ ℓ μ : ℕ, G.IsSRGWith (Fintype.card V) k ℓ μ := by
  classical
  obtain ⟨r, s, _, hs⟩ := Set.ncard_eq_two.mp hs
  let p : ℝ[X] := X ^ 2 - (r + s) • X + C (r * s)
  obtain ⟨d, hd⟩ := exists_aeval_adjMatrix_eq_smul hk p (by
    intro t ht
    rw [hs, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl <;> simp [p, IsRoot, eval_smul, smul_eq_mul] <;> ring)
  have hmatrix : A ^ 2 = (r + s) • A + (-(r * s)) • (1 : Matrix V V ℝ) + d • J := by
    rw [← hd]
    simp only [p, map_sub, map_add, map_pow, map_smul, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one]
    module
  obtain ⟨k', ℓ, μ, h⟩ := (exists_isSRGWith_iff_exists_adjMatrix_sq_eq (R := ℝ)).mpr
    ⟨r + s, -(r * s), d, hmatrix⟩
  have hr : r ∈ G.restrictedEigenvalues := by simp [hs]
  obtain ⟨u, hne, _, _⟩ := mem_restrictedEigenvalues_iff.mp hr
  obtain ⟨i, _⟩ := Function.ne_iff.mp hne
  have hkk' : k' = k := (h.regular i).symm.trans (hk i)
  exact ⟨ℓ, μ, hkk' ▸ h⟩

/-- A regular graph with both an edge and a pair of distinct nonadjacent vertices is strongly
regular exactly when it has exactly two distinct restricted eigenvalues. -/
theorem exists_isSRGWith_iff_ncard_restrictedEigenvalues
    (hk : G.IsRegularOfDegree k) (htop : G ≠ ⊤) (hbot : G ≠ ⊥) :
    (∃ ℓ μ : ℕ, G.IsSRGWith (Fintype.card V) k ℓ μ) ↔ G.restrictedEigenvalues.ncard = 2 :=
  ⟨fun ⟨_, _, h⟩ ↦ h.ncard_restrictedEigenvalues htop hbot,
    exists_isSRGWith_of_ncard_restrictedEigenvalues hk⟩

end SimpleGraph
