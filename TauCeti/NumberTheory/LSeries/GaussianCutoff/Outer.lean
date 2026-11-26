/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianCutoff.Basic

/-!
# The two outer ranges of a Gaussian cutoff

For a logarithmic window `[U, U + X²]`, bound the Gaussian-weighted initial Dirichlet
polynomial on the left arc and the far tail on the right arc by the absolute series at
`1 + 1/U`. The lower endpoint belongs to the window, not to the polynomial, and the upper
endpoint belongs to the window, not to the tail. These estimates apply, in particular, to
von Mangoldt coefficients restricted to a residue class.

The normalization and the choice of reference point are those of `New.norm_sub_mul_sum_term_le`
in `grh/src/Lib/Analytic/Primes.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Complex Finset

namespace TauCeti.LSeries

-- Both outer estimates cancel the reciprocal Gaussian factors and widen the reference sum.
private theorem norm_gaussian_mul_tsum_term_le (a : ℕ → ℂ) (S : Set ℕ) {X U : ℝ} {z : ℂ}
    (hz : ‖(X : ℂ) * z‖ = 1) (hU : X ^ 2 ≤ U)
    (hcut : ∀ n ∈ S, (Real.log n - (U + gaussianShift X z)) * (U⁻¹ - z.re) ≤ 0)
    (href : LSeriesSummable a (1 + (U⁻¹ : ℝ))) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑' n : S, _root_.LSeries.term a (1 + z) n‖ ≤
      ∑' n : ℕ, ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖ := by
  let b (n : ℕ) := ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖
  have hb : Summable b := href.norm
  have hS := hb.subtype (· ∈ S)
  obtain ⟨L, hL, hn⟩ := exists_hasSum_term_gaussian_bound a S hz hU hcut hS.hasSum
  let w : ℂ := (U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2
  have hneg : (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re = -w.re := by
    rw [← neg_re]
    congr 1
    dsimp only [w]
    ring
  rw [hL.tsum_eq, norm_mul, Complex.norm_exp]
  calc
    _ ≤ Real.exp w.re * (Real.exp (-w.re) * ∑' n : S, b n) :=
      mul_le_mul_of_nonneg_left (hneg ▸ hn) (Real.exp_pos _).le
    _ = ∑' n : S, b n := by rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ ∑' n, b n :=
      hS.tsum_le_tsum_of_inj Subtype.val Subtype.coe_injective
        (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) hb

/-- On the arc `Re z ≤ 1 / U`, the Gaussian-weighted Dirichlet polynomial of indices strictly
below `exp U` is bounded by the full absolute series at `1 + 1 / U`. -/
theorem norm_gaussian_mul_sum_range_ceil_exp_le (a : ℕ → ℂ) {X U : ℝ} {z : ℂ}
    (hz : ‖(X : ℂ) * z‖ = 1) (hU : X ^ 2 ≤ U) (hre : z.re ≤ U⁻¹)
    (href : LSeriesSummable a (1 + (U⁻¹ : ℝ))) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑ n ∈ range ⌈Real.exp U⌉₊, _root_.LSeries.term a (1 + z) n‖ ≤
      ∑' n : ℕ, ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖ := by
  rw [← Finset.tsum_subtype (range ⌈Real.exp U⌉₊)]
  refine norm_gaussian_mul_tsum_term_le a _ hz hU (fun n hn ↦ ?_) href
  have hlog : Real.log n ≤ U := by
    rcases n.eq_zero_or_pos with rfl | hn₀
    · simpa using (sq_nonneg X).trans hU
    · exact (Real.log_lt_iff_lt_exp (Nat.cast_pos.mpr hn₀)).2
        (Nat.lt_ceil.mp (mem_range.mp hn)) |>.le
  have hshift := (gaussianShift_mem_Icc hz.le).1
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hre)

/-- On the arc `1 / U ≤ Re z`, the Gaussian-weighted far tail beyond `exp (U + X²)` is bounded
by the full absolute series at `1 + 1 / U`. -/
theorem norm_gaussian_mul_tsum_gt_floor_exp_le (a : ℕ → ℂ) {X U : ℝ} {z : ℂ}
    (hz : ‖(X : ℂ) * z‖ = 1) (hU : X ^ 2 ≤ U) (hre : U⁻¹ ≤ z.re)
    (href : LSeriesSummable a (1 + (U⁻¹ : ℝ))) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑' n : {n : ℕ // ⌊Real.exp (U + X ^ 2)⌋₊ < n}, _root_.LSeries.term a (1 + z) n‖ ≤
      ∑' n : ℕ, ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖ := by
  refine norm_gaussian_mul_tsum_term_le a {n | ⌊Real.exp (U + X ^ 2)⌋₊ < n}
    hz hU (fun n hn ↦ ?_) href
  have hnat : ⌊Real.exp (U + X ^ 2)⌋₊ < n := hn
  have hlog : U + X ^ 2 < Real.log n := (Real.lt_log_iff_exp_lt
    (Nat.cast_pos.mpr (Nat.zero_le _ |>.trans_lt hnat))).mpr (Nat.lt_of_floor_lt hnat)
  have hshift := (gaussianShift_mem_Icc hz.le).2
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (sub_nonpos.mpr hre)

end TauCeti.LSeries
