/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.NegativeSecondMoment

import TauCeti.Analysis.Matrix.Eigenvalues.Interlacing
import TauCeti.Analysis.Matrix.Eigenvalues.Gram
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Lower bounds for singular values from row distances

The negative second-moment identity bounds the lower end of the singular-value list of a
rectangular matrix when its rows stay away from the spans of the other rows. Applying this to
a row submatrix gives bounds on intermediate singular values of the original matrix. This is
the deterministic step used to estimate small singular values in Girko's hermitization.

## References

* C. Bordenave and D. Chafaï, *Around the circular law*, Probab. Surv. 9 (2012), §4.3,
  equation (4.10).
* T. Tao, V. Vu, and M. Krishnapur, *Random matrices: universality of ESDs and the circular law*,
  Ann. Probab. 38 (2010), Appendix A, Lemmas A.1 and A.4.
-/

public section

open Submodule

namespace Matrix

variable {𝕜 m n p : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]

/-- Selecting rows by an embedding can only decrease each singular value. -/
theorem singularValues_submatrix_rows_le (A : Matrix m n 𝕜) (e : p ↪ m) (i : ℕ) :
    (toEuclideanLin (A.submatrix e id)).singularValues i ≤ (toEuclideanLin A).singularValues i := by
  classical
  by_cases hi : i < Fintype.card p
  · let B := A.submatrix e id
    have hgram : (A * Aᴴ).submatrix e e = B * Bᴴ := by
      rw [submatrix_mul _ _ e id e Function.bijective_id, conjTranspose_submatrix]
    have hle := (isHermitian_mul_conjTranspose_self A).eigenvalues₀_submatrix_le e ⟨i, hi⟩
    rw [IsHermitian.eigenvalues₀_congr hgram _ (isHermitian_mul_conjTranspose_self B),
      eigenvalues₀_mul_conjTranspose_self_eq_sq_singularValues,
      eigenvalues₀_mul_conjTranspose_self_eq_sq_singularValues] at hle
    exact (sq_le_sq₀ ((toEuclideanLin B).singularValues_nonneg i)
      ((toEuclideanLin A).singularValues_nonneg i)).mp hle
  · rw [(toEuclideanLin (A.submatrix e id)).singularValues_of_finrank_le_right
      (finrank_euclideanSpace.trans_le (le_of_not_gt hi))]
    exact (toEuclideanLin A).singularValues_nonneg i

/-- If every row is at distance at least `d` from the span of the others, the singular
value at index `i` is at least `d √((m - i) / m)`, where `m` is the number of rows. Indices
are zero-based and the singular values are decreasing. -/
theorem le_singularValues_of_le_infDist_row_span (A : Matrix m n 𝕜)
    (i : Fin (Fintype.card m)) {d : ℝ}
    (hrow : ∀ j, d ≤ Metric.infDist (WithLp.toLp 2 (A j))
      (span 𝕜 ((fun k ↦ WithLp.toLp 2 (A k)) '' {j}ᶜ) : Set (EuclideanSpace 𝕜 n))) :
    d * Real.sqrt ((Fintype.card m - (i : ℝ)) / Fintype.card m) ≤
      (toEuclideanLin A).singularValues i := by
  classical
  rcases le_or_gt d 0 with hd | hd
  · exact (mul_nonpos_of_nonpos_of_nonneg hd (Real.sqrt_nonneg _)).trans
      ((toEuclideanLin A).singularValues_nonneg i)
  have hli : LinearIndependent 𝕜 (fun j ↦ WithLp.toLp 2 (A j)) := by
    rw [linearIndependent_iff_notMem_span]
    intro j hj
    rw [← Set.compl_eq_univ_sdiff] at hj
    exact hd.not_ge ((hrow j).trans_eq (Metric.infDist_zero_of_mem (SetLike.mem_coe.mpr hj)))
  have hrank : A.rank = Fintype.card m := by
    apply LinearIndependent.rank_matrix
    exact hli.map' (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).toLinearMap
      (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 𝕜 (n → 𝕜)).injective)
  have hpos (j : Fin (Fintype.card m)) : 0 < (toEuclideanLin A).singularValues j :=
    (LinearMap.singularValues_pos_iff_lt_finrank_range _).mpr
      (by simpa only [← rank_eq_finrank_range_toEuclideanLin, hrank] using j.isLt)
  have hupper := A.sum_inv_sq_singularValues_eq_sum_inv_infDist_sq hli
  have hsum : (∑ j : Fin (Fintype.card m), ((toEuclideanLin A).singularValues j ^ 2)⁻¹) ≤
      (Fintype.card m : ℝ) * (d ^ 2)⁻¹ := by
    rw [hupper]
    calc
      _ ≤ ∑ _j : m, (d ^ 2)⁻¹ := Finset.sum_le_sum fun j _ ↦ inv_anti₀ (by positivity)
        ((sq_le_sq₀ hd.le Metric.infDist_nonneg).mpr (hrow j))
      _ = _ := by simp
  have hlower : ((Fintype.card m - (i : ℕ) : ℕ) : ℝ) *
        ((toEuclideanLin A).singularValues i ^ 2)⁻¹ ≤
      ∑ j : Fin (Fintype.card m), ((toEuclideanLin A).singularValues j ^ 2)⁻¹ := by
    rw [← Fin.card_Ici i, ← nsmul_eq_mul, ← Finset.sum_const]
    refine (Finset.sum_le_sum fun j hj ↦ inv_anti₀ (pow_pos (hpos j) 2) ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ by positivity))
    have hij : i ≤ j := Finset.mem_Ici.mp hj
    exact (sq_le_sq₀ (hpos j).le (hpos i).le).mpr
      ((toEuclideanLin A).singularValues_antitone hij)
  rw [Nat.cast_sub i.isLt.le] at hlower
  have h := hlower.trans hsum
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos (hpos i) 2) (by positivity)] at h
  apply (sq_le_sq₀ (by positivity) (hpos i).le).mp
  have hi : (i : ℝ) < Fintype.card m := by exact_mod_cast i.isLt
  have hm : 0 < (Fintype.card m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  rw [mul_pow, Real.sq_sqrt (by positivity), ← mul_div_assoc]
  exact (div_le_iff₀ hm).mpr (by linarith only [h])

/-- To bound the `i`-th singular value counted from the bottom, discard `i / 2` rows. If
all remaining row distances are at least `c √((i / 2 + 1) / N)`, the singular value is at
least `c (i + 1) / (2N)`. Both indices start at zero. -/
theorem le_singularValues_rev_of_le_infDist_row_span {N : ℕ} (A : Matrix (Fin N) n 𝕜)
    (i : Fin N) (e : Fin (N - (i : ℕ) / 2) ↪ Fin N) {c : ℝ}
    (hrow : ∀ j, c * Real.sqrt ((((i : ℕ) / 2 : ℕ) + 1 : ℝ) / N) ≤
      Metric.infDist (WithLp.toLp 2 (A (e j)))
        (span 𝕜 ((fun k ↦ WithLp.toLp 2 (A (e k))) '' {j}ᶜ) :
          Set (EuclideanSpace 𝕜 n))) :
    c * ((i : ℝ) + 1) / (2 * N) ≤ (toEuclideanLin A).singularValues i.rev := by
  rcases le_or_gt c 0 with hc | hc
  · exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc (by positivity))
      (by positivity)).trans ((toEuclideanLin A).singularValues_nonneg i.rev)
  let k := (i : ℕ) / 2
  have hi : (i.rev : ℕ) < N - k := by rw [Fin.val_rev]; dsimp [k]; omega
  let j : Fin (Fintype.card (Fin (N - k))) := ⟨i.rev, by simpa using hi⟩
  have hN : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hk : k < N := by omega
  have hj : (k : ℝ) + 1 ≤ (N - k : ℕ) - (j : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    have hj' : (j : ℝ) = N - ((i : ℝ) + 1) := by
      dsimp [j]
      rw [Nat.cast_sub i.isLt, Nat.cast_succ]
    have hki : 2 * k ≤ (i : ℕ) := by dsimp [k]; omega
    have hki' : (2 : ℝ) * (k : ℝ) ≤ i := by exact_mod_cast hki
    linarith only [hj', hki']
  have hratio : ((k : ℝ) + 1) / N ≤ ((N - k : ℕ) - (j : ℝ)) / (N - k : ℕ) :=
    (div_le_div_of_nonneg_right hj hN.le).trans
      (div_le_div_of_nonneg_left (by linarith only [hj])
        (by exact_mod_cast Nat.sub_pos_of_lt hk) (by exact_mod_cast Nat.sub_le N k))
  have hminor := le_singularValues_of_le_infDist_row_span (A.submatrix e id) j hrow
  calc
    _ ≤ c * (((k : ℝ) + 1) / N) := by
      have hik : (i : ℕ) + 1 ≤ 2 * (k + 1) := by dsimp [k]; omega
      have hik' : (i : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by exact_mod_cast hik
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hc.le
      rw [div_le_div_iff₀ (by positivity) hN]
      nlinarith only [hik', hN]
    _ = (c * Real.sqrt (((k : ℝ) + 1) / N)) * Real.sqrt (((k : ℝ) + 1) / N) := by
      rw [mul_assoc, ← sq, Real.sq_sqrt (by positivity)]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by positivity)).trans
      ((by simpa only [Fintype.card_fin] using hminor :
        _ ≤ (toEuclideanLin (A.submatrix e id)).singularValues i.rev).trans
        (A.singularValues_submatrix_rows_le e i.rev))

end Matrix
