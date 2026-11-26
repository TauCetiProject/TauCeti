/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.LinearAlgebra.Matrix.ColumnBasis
import TauCeti.Analysis.Convex.Cone.Caratheodory
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.Logic.Function.Extend
import TauCeti.LinearAlgebra.Matrix.MaximalMinor
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Nonnegative solutions of linear systems

This file collects three facts about the nonnegative solutions `x ≥ 0` of a linear system
`A *ᵥ x = b`, the fibres counted by vector partition functions.

* **Integer heights.** The columns of an integer matrix `A` admit a strictly positive integer
  functional `h`, that is `0 < (h ᵥ* A) j` for every column `j`, exactly when `A` has no nonzero
  nonnegative vector in its kernel: over `ℕ`, or equivalently over any linearly ordered ring. This
  is Gordan's theorem with the denominators of the functional cleared, obtained from the integer
  form of Tucker's theorem `TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos`.
* **Basic solutions.** If an integer matrix `A` has linearly independent rows, then every vector
  `A *ᵥ x` with `x` nonnegative over a linearly ordered field is a nonnegative combination of the
  columns of some column basis (`Matrix.ColumnBasis`). Carathéodory's theorem for cones
  `TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn` applied to the columns gives a nonnegative
  solution with linearly independent support, which extends to a column basis.
* **Integral basic solutions.** If an integer matrix `A` has linearly independent rows and each
  of its maximal minors is `0`, `1` or `-1`, then every integer right-hand side `b` with a
  nonnegative solution over a linearly ordered field has a solution in natural numbers: the
  square submatrix of the column basis of a basic solution has determinant `±1`, so Cramer's rule
  makes the solution integral. Totally unimodular matrices (`Matrix.IsTotallyUnimodular`)
  satisfy the minor hypothesis, by `Matrix.isTotallyUnimodular_iff_fintype` applied to the rows
  `id`.

Both hypotheses of the last result are needed: the `1 × 1` matrix `[2]` has the nonnegative
solution `1 / 2` for `b = 1`, and the `2 × 1` matrix with rows `[2]` and `[0]`, which has no
nonzero maximal minor, has the nonnegative solution `1 / 2` for `b = (1, 0)`, while neither
system has an integer solution.

## Main results

* `Matrix.exists_pos_vecMul_iff`, `Matrix.exists_pos_vecMul_iff_forall_nonneg`: integer heights.
* `Matrix.exists_columnBasis_submatrix_mulVec_eq_of_nonneg`: basic solutions.
* `Matrix.exists_natCast_mulVec_eq_of_nonneg`: integral basic solutions.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §7.7 (Carathéodory's
  theorem) and §19.1 (unimodular matrices and integral polyhedra, Theorem 19.2).
* J. A. De Loera and B. Sturmfels, *Algebraic unimodular counting*, Math. Program. **96** (2003),
  183–203, §1.
-/

public section

open Function

namespace Matrix

variable {κ ι K : Type*} [Fintype ι]

section Height

variable [Fintype κ]

/-- **Integer heights.** An integer matrix has an integer functional `h` strictly positive on
each of its columns exactly when the only natural-number vector in its kernel is `0`. -/
theorem exists_pos_vecMul_iff (A : Matrix κ ι ℤ) :
    (∃ h : κ → ℤ, ∀ j, 0 < (h ᵥ* A) j) ↔
      ∀ c : ι → ℕ, A *ᵥ (fun j => (c j : ℤ)) = 0 → c = 0 := by
  classical
  constructor
  · rintro ⟨h, hh⟩ c hc
    have h0 : (h ᵥ* A) ⬝ᵥ (fun j => (c j : ℤ)) = 0 := by
      rw [← dotProduct_mulVec, hc, dotProduct_zero]
    have := (TauCeti.dotProduct_eq_zero_iff_of_pos hh fun j => Int.natCast_nonneg (c j)).1 h0
    funext j
    simpa using congrFun this j
  · intro hA
    -- Tucker's theorem over `ℤ` for the columns: the relation part vanishes by hypothesis.
    obtain ⟨x, m, hsum, -, hpos⟩ :=
      TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos A.col
    have hx : x = 0 := hA x <| by
      rw [← hsum]
      ext i
      simp [mulVec, dotProduct, Finset.sum_apply, col_apply, mul_comm]
    refine ⟨fun k => m (Pi.single k 1), fun j => ?_⟩
    have hcol : A.col j = ∑ k, A k j • Pi.single k (1 : ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, col_apply]
    have hm : ((fun k => m (Pi.single k 1)) ᵥ* A) j = m (A.col j) := by
      rw [hcol, map_sum]
      simp only [map_zsmul, smul_eq_mul, vecMul, dotProduct]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    simpa [hm, hx] using hpos j

/-- **Integer heights**, real form. An integer matrix has an integer functional `h` strictly
positive on each of its columns exactly when, over a linearly ordered ring `K`, the only
nonnegative vector in its kernel is `0`. For `K = ℝ` this says that the cone spanned by the
columns is pointed and contains no column `0`. -/
theorem exists_pos_vecMul_iff_forall_nonneg [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
    (A : Matrix κ ι ℤ) :
    (∃ h : κ → ℤ, ∀ j, 0 < (h ᵥ* A) j) ↔
      ∀ x : ι → K, 0 ≤ x → A.map (Int.cast : ℤ → K) *ᵥ x = 0 → x = 0 := by
  constructor
  · rintro ⟨h, hh⟩ x hx hAx
    refine (TauCeti.dotProduct_eq_zero_iff_of_pos (c := fun j => ((h ᵥ* A) j : K))
      (fun j => by exact_mod_cast hh j) hx).1 ?_
    rw [← map_intCast_vecMul, ← dotProduct_mulVec, hAx, dotProduct_zero]
  · intro hA
    refine (exists_pos_vecMul_iff A).2 fun c hc => ?_
    have h0 := hA (fun j => ((c j : ℤ) : K)) (fun j => by positivity) <| by
      rw [map_intCast_mulVec, hc]
      ext
      simp
    funext j
    simpa using congrFun h0 j

end Height

section Field

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Basic solutions.** Let `A` be an integer matrix with linearly independent rows. If `x` is
nonnegative over a linearly ordered field, then `A *ᵥ x` is a nonnegative combination of the
columns of some column basis `e` of `A`. -/
theorem exists_columnBasis_submatrix_mulVec_eq_of_nonneg [Fintype κ] [DecidableEq κ]
    {A : Matrix κ ι ℤ} (hA : LinearIndependent ℤ A.row) {x : ι → K} (hx : 0 ≤ x) :
    ∃ (e : A.ColumnBasis) (z : κ → K), 0 ≤ z ∧
      (A.map (Int.cast : ℤ → K)).submatrix id e *ᵥ z = A.map Int.cast *ᵥ x := by
  classical
  -- A nonnegative solution with linearly independent support, by Carathéodory's theorem.
  obtain ⟨y, hy, -, hsum, hli⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn (A.map (Int.cast : ℤ → K)).col hx
  have hyx : A.map (Int.cast : ℤ → K) *ᵥ y = A.map Int.cast *ᵥ x := by
    simpa only [mulVec_eq_sum, op_smul_eq_smul, col_def] using hsum
  have hrow : LinearIndependent K (A.map (Int.cast : ℤ → K)).row := by
    simpa using (linearIndependent_map_algebraMap_row_iff (S := K)).2 hA
  -- Its support extends to a column basis `e`, and `y` is `y ∘ e` extended by zero.
  obtain ⟨f, hyf, hdet⟩ := exists_det_submatrix_ne_zero_of_linearIndepOn hrow hli
  let e : A.ColumnBasis := ⟨f, det_submatrix_ne_zero_of_map (Int.castRingHom K) hdet⟩
  have hext : y = extend e (y ∘ e) 0 := (e.injective.extend_comp_eq_of_forall_notMem_range
    fun _ hj => by_contra fun hyj => hj (hyf hyj)).symm
  refine ⟨e, y ∘ e, fun k => hy (e k), ?_⟩
  rw [← mulVec_extend_zero e.injective, ← hext, hyx]

/-- **Integral basic solutions.** Let `A` be an integer matrix with linearly independent rows all of
whose maximal minors are `0`, `1` or `-1`. If an integer vector `b` is the image `A *ᵥ x` of a
nonnegative vector `x` over a linearly ordered field, then it is the image of a vector of natural
numbers. -/
theorem exists_natCast_mulVec_eq_of_nonneg [Fintype κ] [DecidableEq κ] (A : Matrix κ ι ℤ)
    (hA : LinearIndependent ℤ A.row)
    (hunit : ∀ e : κ → ι, Injective e → (A.submatrix id e).det ∈ Set.range SignType.cast)
    {b : κ → ℤ} {x : ι → K} (hx : 0 ≤ x)
    (hxb : A.map (Int.cast : ℤ → K) *ᵥ x = fun i => (b i : K)) :
    ∃ c : ι → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  -- A basic solution `z` for a column basis `e`.
  obtain ⟨e, z, hz, hzb⟩ := exists_columnBasis_submatrix_mulVec_eq_of_nonneg hA hx
  rw [hxb] at hzb
  -- The integer square submatrix `N` on the columns `e` has determinant `±1`.
  set N := A.submatrix id e
  have hdet : IsUnit N.det := by
    obtain ⟨s, hs⟩ : N.det ∈ Set.range SignType.cast := hunit e e.injective
    have hne : N.det ≠ 0 := e.det_submatrix_ne_zero
    rw [← hs] at hne ⊢
    rcases s with _ | _ | _
    · exact absurd rfl hne
    · simp
    · simp
  -- By Cramer's rule `z` is the integer vector `N⁻¹ *ᵥ b`, which is therefore nonnegative.
  have hdetK : ((A.map (Int.cast : ℤ → K)).submatrix id e).det ≠ 0 := by
    rw [submatrix_map]
    exact (isUnit_det_map_intCast e.det_submatrix_ne_zero).ne_zero
  have hzN : z = fun k => ((N⁻¹ *ᵥ b) k : K) := mulVec_injective_of_det_ne_zero hdetK
    (hzb.trans (e.submatrix_mulVec_intCast_nonsing_inv_mulVec hdet b).symm)
  have hN : ∀ k, 0 ≤ (N⁻¹ *ᵥ b) k := fun k => by
    have := hz k
    rwa [hzN, Pi.zero_apply, Int.cast_nonneg_iff] at this
  refine ⟨extend e (fun k => ((N⁻¹ *ᵥ b) k).toNat) 0, ?_⟩
  have hc : (fun j => ((extend e (fun k => ((N⁻¹ *ᵥ b) k).toNat) 0 j : ℕ) : ℤ)) =
      extend e (N⁻¹ *ᵥ b) 0 := by
    funext j
    rw [apply_extend Nat.cast]
    congr 1
    funext k
    exact Int.toNat_of_nonneg (hN k)
  rw [hc, mulVec_extend_zero_nonsing_inv_mulVec _ e.injective hdet]

end Field

end Matrix
