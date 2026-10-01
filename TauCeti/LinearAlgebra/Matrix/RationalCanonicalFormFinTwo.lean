/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.scalar` and the `2 × 2` matrix notation occur in the statements below, and
-- `TauCeti.mem_range_scalar_fin_two_iff` is how "non-scalar" is read off the entries.
public import TauCeti.LinearAlgebra.Matrix.Commute
-- `Matrix.det` occurs in the statements below, and `Matrix.det_fin_two_of` in the proofs.
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
-- `Matrix.trace` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Trace
-- `linearIndependent_fin2` and `LinearIndependent.pair_symm_iff` read off the invertibility of
-- the conjugating matrix from its two columns.
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
-- `Matrix.linearIndependent_rows_iff_isUnit` and `Matrix.isUnit_iff_isUnit_det`.
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
-- The entry identities below are polynomial, and are solved by `ring`.
import Mathlib.Tactic.Ring

/-!
# Rational canonical form in size two

A `2 × 2` matrix over a field is scalar or **cyclic**: as soon as it is not scalar some vector `v`
is not an eigenvector, and `v, M *ᵥ v` is then a basis in which `M` becomes the companion matrix
`!![0, -det M; 1, trace M]` of its characteristic polynomial `X² - (trace M) X + det M`. That is
the rational canonical form in size two, proved here at the level of matrices; the conjugacy
classification of `GL₂(F)` it yields is in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`.

Being scalar is spelled `M ∈ Set.range (Matrix.scalar (Fin 2))`, as in
`TauCeti.LinearAlgebra.Matrix.Commute`, and unfolded by
`TauCeti.mem_range_scalar_fin_two_iff`; that file's commutant computation is the companion result,
describing the centralizer of a non-scalar matrix rather than its normal form.

## Main definitions

* `TauCeti.companionFinTwo`: the companion matrix `!![0, -d; 1, t]` of `X² - t X + d`.

## Main results

* `TauCeti.exists_forall_mulVec_ne_smul`: a non-scalar `2 × 2` matrix over a semiring has a vector
  that is not an eigenvector; over a field such a vector is cyclic.
* `TauCeti.exists_det_ne_zero_mul_eq_mul_companionFinTwo`: **rational canonical form in size two**,
  a non-scalar `2 × 2` matrix over a field is similar to the companion matrix of its characteristic
  polynomial.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Matrix

namespace TauCeti

/-! ### The companion matrix of a monic quadratic -/

section CommRing

variable {R : Type*} [CommRing R] (t d : R)

/-- **The companion matrix** `!![0, -d; 1, t]` of the monic quadratic `X² - t X + d`: the matrix of
multiplication by `X` on `R[X] ⧸ (X² - t X + d)` in the basis `1, X`. Its trace is `t` and its
determinant is `d`, so it is the normal form that the classification of `2 × 2` matrices runs
on. -/
def companionFinTwo : Matrix (Fin 2) (Fin 2) R := !![0, -d; 1, t]

/-- The companion matrix, spelled out entrywise. -/
theorem companionFinTwo_def : companionFinTwo t d = !![0, -d; 1, t] := (rfl)

@[simp]
theorem det_companionFinTwo : (companionFinTwo t d).det = d := by
  simp [companionFinTwo, Matrix.det_fin_two_of]

@[simp]
theorem trace_companionFinTwo : (companionFinTwo t d).trace = t := by
  simp [companionFinTwo, Matrix.trace_fin_two_of]

/-- **A companion matrix is never scalar**: its lower-left entry is `1`. -/
theorem companionFinTwo_notMem_range_scalar [Nontrivial R] :
    companionFinTwo t d ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rw [mem_range_scalar_fin_two_iff]
  rintro ⟨-, h10, -⟩
  simp [companionFinTwo] at h10

end CommRing

/-! ### Non-eigenvectors of a non-scalar matrix -/

section Semiring

variable {R : Type*} [Semiring R] {M : Matrix (Fin 2) (Fin 2) R}

/-- **A non-scalar `2 × 2` matrix has a vector that is not an eigenvector.** Over a field such a
vector `v` is cyclic: `v, M *ᵥ v` is a basis. -/
theorem exists_forall_mulVec_ne_smul (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ v : Fin 2 → R, ∀ c : R, M *ᵥ v ≠ c • v := by
  by_contra! hcon
  obtain ⟨a, ha⟩ := hcon ![1, 0]
  obtain ⟨b, hb⟩ := hcon ![0, 1]
  obtain ⟨c, hc⟩ := hcon ![1, 1]
  have ha1 : M 1 0 = 0 := by simpa [mulVec, dotProduct] using congrFun ha 1
  have hb0 : M 0 1 = 0 := by simpa [mulVec, dotProduct] using congrFun hb 0
  have hc0 : M 0 0 + M 0 1 = c := by simpa [mulVec, dotProduct] using congrFun hc 0
  have hc1 : M 1 0 + M 1 1 = c := by simpa [mulVec, dotProduct] using congrFun hc 1
  rw [hb0, add_zero] at hc0
  rw [ha1, zero_add] at hc1
  exact hM (mem_range_scalar_fin_two_iff.2 ⟨hb0, ha1, hc0.trans hc1.symm⟩)

end Semiring

/-! ### Rational canonical form in size two -/

section Field

variable {F : Type*} [Field F] {M : Matrix (Fin 2) (Fin 2) F}

/-- **Rational canonical form in size two.** A non-scalar `2 × 2` matrix `M` over a field is
similar to the companion matrix of its characteristic polynomial `X² - (trace M) X + det M`: in the
basis `v, M *ᵥ v` given by a cyclic vector `v`, the matrix of `M` is that companion matrix.

The conjugating matrix is produced together with its determinant rather than as an element of
`GL₂`, so that the statement also covers a matrix that is not itself invertible;
`TauCeti.isConj_companionGL` is the group-level form. -/
theorem exists_det_ne_zero_mul_eq_mul_companionFinTwo
    (hM : M ∉ Set.range (Matrix.scalar (Fin 2))) :
    ∃ P : Matrix (Fin 2) (Fin 2) F,
      P.det ≠ 0 ∧ M * P = P * companionFinTwo M.trace M.det := by
  obtain ⟨v, hv⟩ := exists_forall_mulVec_ne_smul hM
  refine ⟨(of ![v, M *ᵥ v])ᵀ, ?_, ?_⟩
  · rw [det_transpose, ← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det,
      ← linearIndependent_rows_iff_isUnit, row_eq_self, Equiv.symm_apply_apply,
      LinearIndependent.pair_symm_iff, linearIndependent_fin2]
    exact ⟨fun hv0 => hv 0 (by simp_all), fun c hc => hv c hc.symm⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [companionFinTwo, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec,
        dotProduct, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

end Field

end TauCeti
