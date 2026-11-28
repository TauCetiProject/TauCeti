/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Homogeneous parts of matrices on graded submodules

Given grade functions `g : ι → α` and `g' : ι' → α` on finite index types `ι`, `ι'` valued in an
additive type `α`, the degree-`e` homogeneous part of a matrix `W : Matrix ι' ι R` keeps only the
entries `(p, q)` with `g' p = g q + e` and zeroes all others.

When submodules `L ≤ (ι → R)` and `L' ≤ (ι' → R)` are graded — meaning each is stable under the
coordinate projections `fun q ↦ if g q = d then y q else 0` — the action of the degree-`e`
homogeneous part of `W` decomposes as the finite sum over grades `d` of the `(d + e)`-projection of
`W` applied to the `d`-projection of `y`. Consequently, if `W` maps `L` into `L'`, then every
homogeneous part of `W` also maps `L` into `L'`.

## Main results

* `TauCeti.mulVec_homogeneousPart_eq_sum`: decomposes `T *ᵥ y` as the finite sum over
  `d ∈ Finset.univ.image g` of the `(d + e)`-graded projection of `W *ᵥ` applied to the `d`-grade
  projection of `y`.
* `TauCeti.mulVec_homogeneousPart_mem_of_graded`: if `L` and `L'` are stable under coordinate grade
  projections and `W` maps `L` into `L'`, then its degree-`e` homogeneous part `T` maps `L` into
  `L'`.
* `TauCeti.mulVec_homogeneousPart_zero_mem_of_graded`: specialization to degree `0` (`g' p = g q`).

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/UpperBound/Seesaw/Frequency.lean`, declaration
`New.Grading.IsGraded.mulVec_mem_of_homogeneous`. Here the result is generalized from `Ô E`-lattices
in `ι → 𝔸f E` with `ℤ`-gradings to arbitrary `S`-submodules of `ι → R` over any semiring `R` with
`Add α`-valued gradings.
-/

public section

open Matrix

namespace TauCeti

/-- **Decomposition of a homogeneous part of a matrix by coordinate grade projections.** If `T`
equals `W` on entries `(p, q)` with `g' p = g q + e` and `0` elsewhere, then `T *ᵥ y` is the sum
over `d ∈ Finset.univ.image g` of the `(d + e)`-grade projection of `W *ᵥ` applied to the `d`-grade
projection of `y`. -/
theorem mulVec_homogeneousPart_eq_sum {ι ι' α R : Type*} [Fintype ι] [DecidableEq α] [Add α]
    [Semiring R] (g : ι → α) (g' : ι' → α) (W T : Matrix ι' ι R) (e : α)
    (hT : ∀ (p : ι') (q : ι), T p q = if g' p = g q + e then W p q else 0) (y : ι → R) :
    T *ᵥ y = ∑ d ∈ Finset.univ.image g,
      fun p : ι' ↦ if g' p = d + e then (W *ᵥ fun q : ι ↦ if g q = d then y q else 0) p else 0 := by
  ext p
  simp only [mulVec, dotProduct, Finset.sum_apply, hT, ite_mul, zero_mul]
  have h_push (d : α) :
      (if g' p = d + e then ∑ q : ι, W p q * (if g q = d then y q else 0) else 0) =
        ∑ q : ι, if g q = d then (if g' p = d + e then W p q * y q else 0) else 0 := by
    split_ifs with hp
    · simp only [mul_ite, mul_zero]
    · simp
  simp_rw [h_push]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Finset.sum_eq_single (g q)]
  · simp
  · intro d _ hd
    exact ite_eq_right (Ne.symm hd)
  · intro hq
    exact absurd (Finset.mem_image_of_mem g (Finset.mem_univ q)) hq

/-- **Homogeneous parts preserve graded submodules.** If `L ≤ (ι → R)` and `L' ≤ (ι' → R)` are
stable under coordinate grade projections and `W` maps `L` into `L'`, then the degree-`e`
homogeneous part `T` of `W` also maps `L` into `L'`. -/
theorem mulVec_homogeneousPart_mem_of_graded {ι ι' α R S : Type*} [Fintype ι] [DecidableEq α]
    [Add α] [Semiring R] [Semiring S] [Module S R] (g : ι → α) (g' : ι' → α)
    {L : Submodule S (ι → R)} {L' : Submodule S (ι' → R)}
    (hL : ∀ d : α, ∀ y ∈ L, (fun q : ι ↦ if g q = d then y q else 0) ∈ L)
    (hL' : ∀ d : α, ∀ z ∈ L', (fun p : ι' ↦ if g' p = d then z p else 0) ∈ L')
    {W T : Matrix ι' ι R} {e : α} (hW : ∀ y ∈ L, W *ᵥ y ∈ L')
    (hT : ∀ (p : ι') (q : ι), T p q = if g' p = g q + e then W p q else 0)
    {y : ι → R} (hy : y ∈ L) : T *ᵥ y ∈ L' := by
  rw [mulVec_homogeneousPart_eq_sum g g' W T e hT y]
  exact L'.sum_mem fun d _ ↦ hL' (d + e) _ (hW _ (hL d y hy))

/-- Degree-zero specialization of `TauCeti.mulVec_homogeneousPart_mem_of_graded`: if `W` maps a
graded submodule `L` into a graded submodule `L'`, then the part `T` of `W` keeping only entries
`(p, q)` with `g' p = g q` also maps `L` into `L'`. -/
theorem mulVec_homogeneousPart_zero_mem_of_graded {ι ι' α R S : Type*} [Fintype ι] [DecidableEq α]
    [AddMonoid α] [Semiring R] [Semiring S] [Module S R] (g : ι → α) (g' : ι' → α)
    {L : Submodule S (ι → R)} {L' : Submodule S (ι' → R)}
    (hL : ∀ d : α, ∀ y ∈ L, (fun q : ι ↦ if g q = d then y q else 0) ∈ L)
    (hL' : ∀ d : α, ∀ z ∈ L', (fun p : ι' ↦ if g' p = d then z p else 0) ∈ L')
    {W T : Matrix ι' ι R} (hW : ∀ y ∈ L, W *ᵥ y ∈ L')
    (hT : ∀ (p : ι') (q : ι), T p q = if g' p = g q then W p q else 0)
    {y : ι → R} (hy : y ∈ L) : T *ᵥ y ∈ L' :=
  mulVec_homogeneousPart_mem_of_graded g g' hL hL' hW (e := (0 : α))
    (fun p q ↦ by simpa only [add_zero] using hT p q) hy

end TauCeti
