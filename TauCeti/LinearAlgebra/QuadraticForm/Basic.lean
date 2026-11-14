/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.Anisotropic.comp`: injective pullback preserves anisotropy.
* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
* `QuadraticMap.map_sum_of_pairwise_isOrtho`: a quadratic map is additive across a finite sum of
  pairwise `Q`-orthogonal vectors.
-/

public section

namespace QuadraticMap

/-- The source of a nonzero quadratic map is nontrivial. -/
theorem nontrivial_of_ne_zero {S V N : Type*} [CommSemiring S] [AddCommMonoid V]
    [Module S V] [AddCommMonoid N] [Module S N] {Q : QuadraticMap S V N} (hQ : Q ≠ 0) :
    Nontrivial V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact nontrivial_of_ne v 0 (fun h ↦ hv (by simp [h]))

/-- An injective pullback of an anisotropic quadratic map is anisotropic. -/
theorem Anisotropic.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.Anisotropic)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).Anisotropic := by
  intro x hx
  apply hf
  rw [map_zero]
  exact hQ _ hx

/-- For a pairwise `Q`-orthogonal family on a finite set `s`, `Q` is additive across
`∑ i ∈ s, u i`. -/
theorem map_sum_of_pairwise_isOrtho {R M P ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (Q : QuadraticMap R M P) (s : Finset ι) (u : ι → M)
    (hu : Set.Pairwise (s : Set ι) fun i j ↦ Q.IsOrtho (u i) (u j)) :
    Q (∑ i ∈ s, u i) = ∑ i ∈ s, Q (u i) := by
  classical
  have hcross : ∑ ij ∈ s.sym2 with ¬ij.IsDiag, polarSym2 Q (ij.map u) = 0 := by
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    induction ij using Sym2.ind with
    | h i j =>
      have hij_mem := Finset.mem_sym2_iff.mp (Finset.mem_filter.mp hij).1
      have hij_ne : i ≠ j := by simpa using (Finset.mem_filter.mp hij).2
      exact (hu (hij_mem i (Sym2.mem_mk_left i j)) (hij_mem j (Sym2.mem_mk_right i j))
        hij_ne).polar_eq_zero
  rw [Q.map_sum, hcross, add_zero]

end QuadraticMap
