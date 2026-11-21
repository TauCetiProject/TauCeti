/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Alternative
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Analysis.Convex.Cone.Caratheodory
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Nonnegative solutions of linear systems

This file collects two facts about the nonnegative solutions `x ≥ 0` of a linear system
`A *ᵥ x = b`, the fibres counted by vector partition functions.

* **Integer heights.** The columns of an integer matrix `A` admit a strictly positive integer
  functional `h`, that is `0 < (h ᵥ* A) j` for every column `j`, exactly when `A` has no nonzero
  nonnegative vector in its kernel: over `ℕ`, or equivalently over any linearly ordered ring. This
  is Gordan's theorem with the denominators of the functional cleared, obtained from the integer
  form of Tucker's theorem `TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos`.
* **Integral basic solutions.** If an integer matrix `A` has linearly independent rows and each
  of its maximal minors is `0`, `1` or `-1`, then every integer right-hand side `b` with a
  nonnegative solution over a linearly ordered field has a solution in natural numbers. A basic
  solution, given by Carathéodory's theorem for cones
  `TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn` applied to the columns, extends to a
  column basis, whose square submatrix has determinant `±1`, so Cramer's rule makes the solution
  integral. Totally unimodular matrices (`Matrix.IsTotallyUnimodular`) satisfy the minor
  hypothesis, by `Matrix.isTotallyUnimodular_iff_fintype` applied to the rows `id`.

Both hypotheses of the last result are needed: the `1 × 1` matrix `[2]` has the nonnegative
solution `1 / 2` for `b = 1`, and the `2 × 1` matrix with rows `[2]` and `[0]`, which has no
nonzero maximal minor, has the nonnegative solution `1 / 2` for `b = (1, 0)`, while neither
system has an integer solution.

## Main results

* `Matrix.exists_pos_vecMul_iff`, `Matrix.exists_pos_vecMul_iff_forall_nonneg`: integer heights.
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

/-- A nonnegative solution over `K` with integer coordinates is a solution in natural numbers. -/
private theorem exists_natCast_mulVec_eq_of_forall_exists_intCast {A : Matrix κ ι ℤ} {b : κ → ℤ}
    {y : ι → K} (hy : 0 ≤ y) (hint : ∀ j, ∃ n : ℤ, y j = n)
    (hyb : A.map (Int.cast : ℤ → K) *ᵥ y = fun i => (b i : K)) :
    ∃ c : ι → ℕ, A *ᵥ (fun j => (c j : ℤ)) = b := by
  choose n hn using hint
  refine ⟨fun j => (n j).toNat, ?_⟩
  have hn0 : (fun j => ((n j).toNat : ℤ)) = n := funext fun j => by
    have := hy j
    rw [Pi.zero_apply, hn j, Int.cast_nonneg_iff] at this
    exact Int.toNat_of_nonneg this
  rw [hn0]
  rw [funext hn, map_intCast_mulVec] at hyb
  exact funext fun i => Int.cast_injective (congrFun hyb i)

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
  classical
  -- A basic solution `y`, and a column basis `f` containing its support.
  obtain ⟨y, hy, -, hsum, hli⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn (A.map (Int.cast : ℤ → K)).col hx
  have hyx : A.map (Int.cast : ℤ → K) *ᵥ y = A.map Int.cast *ᵥ x := by
    simpa only [mulVec_eq_sum, op_smul_eq_smul, col_def] using hsum
  have hrow : LinearIndependent K (A.map (Int.cast : ℤ → K)).row := by
    simpa using (linearIndependent_map_algebraMap_row_iff (S := K)).2 hA
  obtain ⟨f, hyf, hdetK⟩ := exists_det_submatrix_ne_zero_of_linearIndepOn hrow hli
  -- The integer square submatrix `N` on the columns `f` has determinant `±1`.
  set N := A.submatrix id f
  have hdet : IsUnit N.det := by
    -- `hdetK` is a minor of `A.map (Int.castRingHom K)`, whose coercion is `Int.cast`.
    have hne : N.det ≠ 0 := det_submatrix_ne_zero_of_map (Int.castRingHom K) hdetK
    obtain ⟨s, hs⟩ : N.det ∈ Set.range SignType.cast := hunit f f.injective
    rw [← hs] at hne ⊢
    rcases s with _ | _ | _
    · exact absurd rfl hne
    · simp
    · simp
  rw [submatrix_map] at hdetK
  -- `y` vanishes off the columns `f`, so `y ∘ f` solves the square system: it is `N⁻¹ *ᵥ b`.
  have hyf' : ∀ j ∉ Set.range f, y j = 0 := fun j hj => by_contra fun hyj => hj (hyf hyj)
  have hNy : N.map (Int.cast : ℤ → K) *ᵥ (fun k => y (f k)) = fun i => (b i : K) := by
    rw [← hxb, ← hyx]
    funext i
    exact Fintype.sum_of_injective f f.injective _ _ (fun j hj => by simp [hyf' j hj]) fun k => rfl
  have hNz : N.map (Int.cast : ℤ → K) *ᵥ (fun k => ((N⁻¹ *ᵥ b) k : K)) =
      fun i => (b i : K) := by
    rw [map_intCast_mulVec, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hint : ∀ j, ∃ n : ℤ, y j = n := fun j => by
    by_cases hj : j ∈ Set.range f
    · obtain ⟨k, rfl⟩ := hj
      exact ⟨(N⁻¹ *ᵥ b) k,
        congrFun (mulVec_injective_of_det_ne_zero hdetK (hNy.trans hNz.symm)) k⟩
    · exact ⟨0, by simp [hyf' j hj]⟩
  exact exists_natCast_mulVec_eq_of_forall_exists_intCast hy hint (hyx.trans hxb)

end Field

end Matrix
