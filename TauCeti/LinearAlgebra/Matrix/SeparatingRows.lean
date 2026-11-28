/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Order.WellFoundedSet

/-!
# Matrices with rows from a separating set and nonvanishing determinant

Let `R : S →+* D` be a ring homomorphism from a commutative ring `S` to a nontrivial semiring `D`,
and let `X : Set (d → S)` be a set of vectors that separates `d`-tuples modulo `R`, in the sense
that `R (t ⬝ᵥ x) = 0` for all `x ∈ X` forces `R (t i) = 0` for every `i : d`. Then there exists a
square matrix `N : Matrix d d S` whose rows all belong to `X` and such that `R N.det ≠ 0`.

## Main results

* `RingHom.exists_matrix_map_det_ne_zero`: existence of a square matrix with rows in `X` whose
  determinant has nonzero image under `R`.

## Proof idea

Among all square matrices `N : Matrix d d S` with `R N.det ≠ 0` (nonempty since
`R (1 : Matrix d d S).det = 1 ≠ 0` because `D` is nontrivial), choose one maximising the set
`{k | N k ∈ X}` of rows lying in `X`. If some row `k` is not in `X`, replacing row `k` by any
`x ∈ X` strictly enlarges that set, so `R (N.updateRow k x).det = 0`. By Cramer's rule, column `k`
of `N.adjugate` then has zero dot product with every `x ∈ X` after `R`; the separation hypothesis
forces `R (N.adjugate i k) = 0` for all `i`, contradicting `R N.det ≠ 0` via the cofactor expansion
along row `k`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean` (`New.Lift.Chart.exists_det_ne_zero`).
-/

@[expose] public section

open Matrix

/-- Let `R : S →+* D` be a ring homomorphism from a commutative ring `S` to a nontrivial semiring
`D`, and let `X : Set (d → S)` be a set of vectors such that `R (t ⬝ᵥ x) = 0` for all `x ∈ X`
implies `R (t i) = 0` for all `i : d`. Then there is a square matrix `N : Matrix d d S` whose rows
all lie in `X` and whose determinant satisfies `R N.det ≠ 0`. -/
theorem RingHom.exists_matrix_map_det_ne_zero {d S D : Type*} [Fintype d] [DecidableEq d]
    [CommRing S] [Semiring D] [Nontrivial D] (R : S →+* D) (X : Set (d → S))
    (h_sep : ∀ t : d → S, (∀ x ∈ X, R (t ⬝ᵥ x) = 0) → ∀ i : d, R (t i) = 0) :
    ∃ N : Matrix d d S, R N.det ≠ 0 ∧ ∀ k : d, N k ∈ X := by
  obtain ⟨N, hN, hmax⟩ := exists_maximalFor_of_wellFoundedGT
    (fun N : Matrix d d S ↦ R N.det ≠ 0) (fun N ↦ {k | N k ∈ X}) ⟨1, by simp⟩
  refine ⟨N, hN, fun k ↦ by_contra fun hk ↦ hN ?_⟩
  have hkill (x : d → S) (hx : x ∈ X) : R ((N.adjugate · k) ⬝ᵥ x) = 0 := by
    by_contra hne
    have hdet : R (N.updateRow k x).det ≠ 0 := by
      simpa [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
    have hsub : {l | N l ∈ X} ⊆ {l | N.updateRow k x l ∈ X} := fun l hl ↦ by
      by_cases hlk : l = k
      · subst hlk; simpa using hx
      · simpa [hlk] using hl
    exact hk (hmax hdet hsub (show k ∈ {l | N.updateRow k x l ∈ X} by simpa using hx))
  have hcol : ∀ i : d, R (N.adjugate i k) = 0 := h_sep (N.adjugate · k) hkill
  simp [N.det_eq_sum_mul_adjugate_row k, hcol]
