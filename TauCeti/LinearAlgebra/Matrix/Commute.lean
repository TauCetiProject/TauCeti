/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.scalar` occurs in the statements below, and the `2 × 2` entry lemma `Fin.sum_univ_two`
-- in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Notation
-- Non-public: the entry equations are rearranged by `linear_combination`, in the proofs only.
import Mathlib.Tactic.LinearCombination

/-!
# The commutant of a `2 × 2` matrix

A `2 × 2` matrix over a field is **regular** as soon as it is not scalar: it is then cyclic
(nonderogatory), and the matrices commuting with it are exactly the polynomials in it. In size `2`
those polynomials are the affine combinations `a • 1 + b • M`, so the commutant of a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` is the two-dimensional algebra `F[M]` — in particular it is
commutative.

Mathlib's `Matrix.mem_range_scalar_iff_commute_transvectionStruct` describes the matrices commuting
with *everything*; what is proved here is the commutant of a *single* matrix, in size two, read off
the three independent entry equations of `M * N = N * M` by splitting on which of the two
off-diagonal entries or the diagonal difference of `M` is nonzero.

Being scalar is recorded over a semiring. Computing the commutant divides by an entry of `M` and
needs a field, but that the commutant is commutative only cancels one, so it holds over any
commutative ring without zero divisors.

The commutant computation is what determines the centralizers of elements of `GL (Fin 2) F` in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer`.

## Main results

* `TauCeti.mem_range_scalar_fin_two_iff`: a `2 × 2` matrix is scalar exactly when its off-diagonal
  entries vanish and its two diagonal entries agree.
* `TauCeti.commute_fin_two_iff_entries`: over a commutative ring, two `2 × 2` matrices commute
  exactly when their off-diagonal entries and diagonal differences satisfy three cross-multiplied
  equations.
* `TauCeti.commute_fin_two_iff`: a matrix commutes with a non-scalar `2 × 2` matrix `M` over a field
  exactly when it is of the form `a • 1 + b • M`.
* `TauCeti.commute_of_commute_fin_two`: over a commutative ring without zero divisors, two matrices
  commuting with a common non-scalar `2 × 2` matrix commute with each other.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} {M N P : Matrix (Fin 2) (Fin 2) R}

/-- A `2 × 2` matrix is scalar exactly when its off-diagonal entries vanish and its two diagonal
entries agree. -/
theorem mem_range_scalar_fin_two_iff [Semiring R] :
    M ∈ Set.range (Matrix.scalar (Fin 2)) ↔ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 = M 1 1 := by
  constructor
  · rintro ⟨c, rfl⟩
    simp [Matrix.scalar_apply]
  · rintro ⟨h01, h10, h00⟩
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00]

section CommRing

variable [CommRing R]

/-- **Entrywise criterion for commuting `2 × 2` matrices**, over any commutative ring. The two
diagonal entries of `M * N - N * M` are negatives of each other, leaving three conditions: the
`2 × 2` minors of the triples `(M 0 1, M 1 0, M 0 0 - M 1 1)` and `(N 0 1, N 1 0, N 0 0 - N 1 1)`
vanish, so that over a field these triples are proportional. -/
theorem commute_fin_two_iff_entries :
    Commute M N ↔ M 0 1 * N 1 0 = N 0 1 * M 1 0 ∧
      M 0 1 * (N 0 0 - N 1 1) = N 0 1 * (M 0 0 - M 1 1) ∧
      M 1 0 * (N 0 0 - N 1 1) = N 1 0 * (M 0 0 - M 1 1) := by
  rw [Commute, SemiconjBy, ← Matrix.ext_iff, Fin.forall_fin_two, Fin.forall_fin_two,
    Fin.forall_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · rintro ⟨⟨h00, h01⟩, h10, -⟩
    exact ⟨by linear_combination h00, by linear_combination -h01, by linear_combination h10⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by linear_combination h1, by linear_combination -h2⟩,
      by linear_combination h3, by linear_combination -h1⟩

/-- A `2 × 2` matrix whose off-diagonal entries and diagonal difference are `b` times those of `M`
is of the form `a • 1 + b • M`. -/
private theorem exists_eq_scalar_add_smul_fin_two (b : R) (h01 : N 0 1 = b * M 0 1)
    (h10 : N 1 0 = b * M 1 0) (hd : N 0 0 - N 1 1 = b * (M 0 0 - M 1 1)) :
    ∃ a b : R, N = Matrix.scalar (Fin 2) a + b • M := by
  refine ⟨N 0 0 - b * M 0 0, b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10]
  linear_combination -hd

/-- Over a commutative ring without zero divisors, two matrices commuting with a common non-scalar
`2 × 2` matrix commute with each other; over a field this is because both lie in the commutative
algebra `F[M]` (`TauCeti.commute_fin_two_iff`).

Some hypothesis on `R` is needed: over `ZMod 4`, both `!![0, 1; 2, 0]` and `!![0, 0; 0, 2]`
commute with `!![0, 2; 0, 0]` but not with each other. -/
theorem commute_of_commute_fin_two [NoZeroDivisors R]
    (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) (hN : Commute M N) (hP : Commute M P) :
    Commute N P := by
  rw [commute_fin_two_iff_entries] at hN hP ⊢
  rw [mem_range_scalar_fin_two_iff] at hM
  -- Being non-scalar, `M` has a nonzero off-diagonal entry or distinct diagonal entries, and
  -- the proportionality relations of `N` and of `P` to `M` can be cancelled by it.
  by_cases h01 : M 0 1 = 0
  · by_cases h10 : M 1 0 = 0
    · have hd : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.mpr fun h => hM ⟨h01, h10, h⟩
      refine ⟨mul_left_cancel₀ hd ?_, mul_left_cancel₀ hd ?_, mul_left_cancel₀ hd ?_⟩ <;> grind
    · refine ⟨mul_left_cancel₀ h10 ?_, mul_left_cancel₀ h10 ?_, mul_left_cancel₀ h10 ?_⟩ <;> grind
  · refine ⟨mul_left_cancel₀ h01 ?_, mul_left_cancel₀ h01 ?_, mul_left_cancel₀ h01 ?_⟩ <;> grind

end CommRing

section Field

variable {F : Type*} [Field F] {M N : Matrix (Fin 2) (Fin 2) F}

/-- **The commutant of a non-scalar `2 × 2` matrix.** A matrix commutes with a non-scalar
`M : Matrix (Fin 2) (Fin 2) F` exactly when it lies in the two-dimensional subalgebra spanned by
`1` and `M`; equivalently, a non-scalar `2 × 2` matrix is cyclic, so its commutant is `F[M]`.

The hypothesis is necessary: everything commutes with a scalar matrix. -/
theorem commute_fin_two_iff (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    Commute M N ↔ ∃ a b : F, N = Matrix.scalar (Fin 2) a + b • M := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := commute_fin_two_iff_entries.mp h
    rw [mem_range_scalar_fin_two_iff] at hM
    -- Being non-scalar, `M` has a nonzero off-diagonal entry or distinct diagonal entries, and
    -- the ratio of the corresponding entries of `N` and `M` is the coefficient of `M`.
    by_cases h01 : M 0 1 = 0
    · by_cases h10 : M 1 0 = 0
      · have hd : M 0 0 - M 1 1 ≠ 0 := sub_ne_zero.mpr fun h => hM ⟨h01, h10, h⟩
        refine exists_eq_scalar_add_smul_fin_two ((N 0 0 - N 1 1) / (M 0 0 - M 1 1)) ?_ ?_ ?_ <;>
          grind
      · refine exists_eq_scalar_add_smul_fin_two (N 1 0 / M 1 0) ?_ ?_ ?_ <;> grind
    · refine exists_eq_scalar_add_smul_fin_two (N 0 1 / M 0 1) ?_ ?_ ?_ <;> grind
  · rintro ⟨a, b, rfl⟩
    exact ((Matrix.scalar_commute a (Commute.all a) M).symm).add_right
      ((Commute.refl M).smul_right b)

end Field

end TauCeti
