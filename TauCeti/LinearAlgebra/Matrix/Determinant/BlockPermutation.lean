/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Leading minors of matrices permuting blocks

Let `b : n → α` label the blocks of a square matrix, and let `σ` permute their labels.
The support condition `M i j ≠ 0 → b i = σ (b j)` means that `M` carries the block at `a`
into the block at `σ a`. The maps inside these blocks are arbitrary: no permutation of
the individual basis vectors is assumed.

When the block labels are partially ordered and all occur, nonvanishing of every leading
block minor forces `σ = 1`. Consequently, for an invertible matrix over a nontrivial
commutative ring, every leading block minor is a unit exactly when the block permutation
is trivial. This criterion detects which weight-block permutations can occur in the
open set admitting block lower-diagonal-upper factorization.

The weight-space application is the big-cell argument in R. Steinberg, *Lectures on
Chevalley Groups*, Chapter 5, Theorem 7: a Weyl representative permutes weight spaces,
and its leading weight-block minors can all be invertible only if it fixes every weight.
-/

public section

namespace Matrix

variable {n α R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- If a matrix carries each block into the block prescribed by `f`, a principal minor
on a set of blocks vanishes whenever one of its source blocks is carried outside the set. -/
theorem det_toSquareBlockProp_eq_zero_of_block_maps_out
    (M : Matrix n n R) (b : n → α) (f : α → α)
    (hsupport : ∀ i j, b i ≠ f (b j) → M i j = 0)
    (p : α → Prop) [DecidablePred p] (j : n) (hj : p (b j)) (hfj : ¬p (f (b j))) :
    (M.toSquareBlockProp fun i => p (b i)).det = 0 := by
  apply det_eq_zero_of_column_eq_zero ⟨j, hj⟩
  intro i
  exact hsupport i j fun h => hfj (h ▸ i.property)

/-- Nonvanishing of the leading block minors forces a supported block map to send each
occurring label to a label no larger than itself. -/
theorem apply_le_of_det_toSquareBlockProp_le_ne_zero [Preorder α] [DecidableLE α]
    (M : Matrix n n R) (b : n → α) (f : α → α)
    (hsupport : ∀ i j, b i ≠ f (b j) → M i j = 0)
    (hminor : ∀ a, (M.toSquareBlockProp fun i => b i ≤ a).det ≠ 0) (j : n) :
    f (b j) ≤ b j := by
  by_contra hj
  exact hminor (b j) (det_toSquareBlockProp_eq_zero_of_block_maps_out M b f hsupport
    (· ≤ b j) j le_rfl hj)

variable [PartialOrder α] [DecidableLE α]

/-- A permutation of the occurring blocks is trivial if every leading block minor is
nonzero. The blocks may have arbitrary sizes and arbitrary internal matrices. -/
theorem eq_one_of_det_toSquareBlockProp_le_ne_zero
    (M : Matrix n n R) (b : n → α) (hb : Function.Surjective b) (σ : Equiv.Perm α)
    (hsupport : ∀ i j, b i ≠ σ (b j) → M i j = 0)
    (hminor : ∀ a, (M.toSquareBlockProp fun i => b i ≤ a).det ≠ 0) :
    σ = 1 := by
  have : Finite α := Finite.of_surjective b hb
  have hle (a : α) : σ a ≤ a := by
    obtain ⟨j, rfl⟩ := hb a
    exact apply_le_of_det_toSquareBlockProp_le_ne_zero M b σ hsupport hminor j
  ext a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    rcases (hle a).eq_or_lt with h | h
    · exact h
    · exact σ.injective (ih (σ a) h)

/-- For an invertible matrix permuting a partially ordered family of nonempty blocks,
all leading block minors are units if and only if the block permutation is trivial. -/
theorem isUnit_det_toSquareBlockProp_le_iff_eq_one [Nontrivial R]
    (M : Matrix n n R) (hM : IsUnit M.det) (b : n → α) (hb : Function.Surjective b)
    (σ : Equiv.Perm α) (hsupport : ∀ i j, b i ≠ σ (b j) → M i j = 0) :
    (∀ a, IsUnit (M.toSquareBlockProp fun i => b i ≤ a).det) ↔ σ = 1 := by
  refine ⟨fun h => eq_one_of_det_toSquareBlockProp_le_ne_zero M b hb σ hsupport
    (fun a => (h a).ne_zero), ?_⟩
  rintro rfl a
  have hdet := M.twoBlockTriangular_det (fun i => b i ≤ a) (by
    intro i hi j hj
    exact hsupport i j fun hij => hi (hij ▸ hj))
  rw [hdet] at hM
  exact isUnit_of_mul_isUnit_left hM

end Matrix
