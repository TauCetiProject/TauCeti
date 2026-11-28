/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.NumberTheory.LSeries.GaussianCutoff
import TauCeti.NumberTheory.LSeries.GaussianWindow
import TauCeti.NumberTheory.LSeries.PrimeWindow
import TauCeti.NumberTheory.LSeries.ResidueClassTail
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.VonMangoldt

/-!
# Primes in logarithmic windows from bounds near one

Nonvanishing and logarithmic-derivative bounds for the pole-removed Dirichlet L-functions on
one disk about `1` suffice to find a prime in a prescribed reduced class in a logarithmic window.
The bounds on the two outer parts of the series use the same real reference point; in the absence
of primes the middle part is bounded by a convergent series of higher prime powers.

The argument is the Gaussian maximum-modulus method of `New.exists_prime_modEq_one_log_mem` in
[`Lib/Analytic/Primes.lean`][short-proof]. The criterion here is stated for any reduced class and
separates the disk estimates from the prime-existence argument.

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean
-/

public section

open Complex Filter Finset Metric Set
open ArithmeticFunction.vonMangoldt DirichletCharacter

namespace TauCeti.LSeries

-- Partition the indices by their logarithms, assigning both endpoints to the middle.
private theorem exists_logarithmicWindow_partition (U W : ℝ) :
    ∃ S M : Finset ℕ, Disjoint S M ∧
      (∀ n ∈ S, Real.log n < U) ∧
      (∀ n ∈ M, Real.log n ∈ Icc U (U + W)) ∧
      (∀ n ∉ S ∪ M, U + W < Real.log n) := by
  classical
  let B := (range (⌊Real.exp (U + W)⌋₊ + 1)).filter (fun n : ℕ ↦ Real.log n ≤ U + W)
  let S := B.filter (fun n : ℕ ↦ Real.log n < U)
  let M := B.filter (fun n : ℕ ↦ U ≤ Real.log n)
  have hB (n : ℕ) : n ∈ B ↔ Real.log n ≤ U + W := by
    dsimp only [B]
    rw [mem_filter, and_iff_right_of_imp]
    intro hn
    rcases n.eq_zero_or_pos with rfl | hn₀
    · simp
    · rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (Real.exp_pos _).le]
      exact (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn₀)).mp hn
  refine ⟨S, M, Finset.disjoint_left.mpr (fun n hn hm ↦ ?_),
    fun n hn ↦ (mem_filter.mp hn).2, fun n hn ↦ ?_, fun n hn ↦ ?_⟩
  · exact (mem_filter.mp hn).2.not_ge (mem_filter.mp hm).2
  · exact ⟨(mem_filter.mp hn).2, (hB n).mp (mem_filter.mp hn).1⟩
  · apply lt_of_not_ge
    intro h
    have hnB := (hB n).mpr h
    by_cases hlt : Real.log n < U
    · exact hn (mem_union_left _ (mem_filter.mpr ⟨hnB, hlt⟩))
    · exact hn (mem_union_right _ (mem_filter.mpr ⟨hnB, le_of_not_gt hlt⟩))

-- The uncut numerator provides exactly the continuation and size inputs for the left arc.
private theorem residueClassNumerator_disk {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) {X : ℝ}
    (hX : 0 < X) (hd : ∀ (χ : DirichletCharacter ℂ q) (z : ℂ), ‖z‖ ≤ X⁻¹ →
      χ.entireLFunction (1 + z) ≠ 0 ∧ ‖logDeriv χ.entireLFunction (1 + z)‖ ≤ X) :
    DiffContOnCl ℂ (residueClassTailNumerator a ∅) (ball 0 X⁻¹) ∧
      ∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → ‖residueClassTailNumerator a ∅ z‖ ≤ 2 := by
  constructor
  · apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' : ‖z‖ ≤ X⁻¹ := by
      simpa only [mem_closedBall, dist_zero_right] using closure_ball_subset_closedBall hz
    have ha := analyticAt_residueClassTailNumerator a ∅ (z := z)
      (by simpa only [entireLFunction_one] using (hd 1 z hz').1)
      (fun χ hχ ↦ by simpa only [entireLFunction_of_ne_one hχ] using (hd χ z hz').1)
    exact ha.differentiableAt.differentiableWithinAt
  · intro z hz
    have hzn : ‖z‖ = X⁻¹ := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hX.le] at hz
      exact eq_inv_of_mul_eq_one_right hz
    refine (norm_residueClassTailNumerator_empty_le a
      (by simpa only [entireLFunction_one] using (hd 1 z hzn.le).2)
      (fun χ hχ ↦ by simpa only [entireLFunction_of_ne_one hχ] using (hd χ z hzn.le).2)).trans ?_
    rw [hzn, inv_mul_cancel₀ hX.ne']
    have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    linarith [inv_le_one_of_one_le₀ ht]

/-- If all the pole-removed L-functions modulo `q` are nonzero with logarithmic derivative at
most `X` in norm on `‖s - 1‖ ≤ 1/X`, every reduced class modulo `q` has a prime with logarithm in
`[U, U + X²]`, provided `X² ≤ U` and `U, φ(q) ≤ X^A`. The threshold for `X` depends only on `A`. -/
theorem eventually_exists_prime_log_mem_Icc_of_logDeriv_bound (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {q : ℕ} [NeZero q] {U : ℝ},
      X ^ 2 ≤ U → U ≤ X ^ A → (q.totient : ℝ) ≤ X ^ A →
      (∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ‖s - 1‖ ≤ X⁻¹ →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X) →
      ∀ a : (ZMod q)ˣ, ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧
        Real.log p ∈ Icc U (U + X ^ 2) := by
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp eventually_exists_hasSum_norm_term_one_add_inv_le
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop U₀,
    eventually_exists_prime_log_mem_Icc_of_gaussian_bounds A,
    eventually_norm_gaussian_window_sum_le_one] with X hX hX₀ hdetect hmiddle
  intro q _ U hU hUA hq hd a
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hXsq : X ≤ X ^ 2 := by nlinarith
  have hUpos : 0 < U := hXpos.trans_le (hXsq.trans hU)
  obtain ⟨S, M, hSM, hS, hM, hfar⟩ := exists_logarithmicWindow_partition U (X ^ 2)
  obtain ⟨hF, hFle⟩ := residueClassNumerator_disk a hXpos (fun χ z hz ↦
    hd χ (1 + z) (by simpa only [add_comm (1 : ℂ), add_sub_cancel_right] using hz))
  have hout (V : Set ℕ) {z : ℂ} (hz : ‖(X : ℂ) * z‖ = 1)
      (hcut : ∀ n ∈ V, (Real.log n - (U + gaussianShift X z)) * (U⁻¹ - z.re) ≤ 0) :
      ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑' n : V, _root_.LSeries.term (fun k ↦ (residueClass (a : ZMod q) k : ℂ)) (1 + z) n‖ ≤
        U := by
    obtain ⟨B, hB, hBU⟩ := hU₀ U (hX₀.trans (hXsq.trans hU))
      (fun k ↦ (residueClass (a : ZMod q) k : ℂ)) V (fun n _ _ ↦ by
        simpa only [norm_real, Real.norm_of_nonneg (residueClass_nonneg _ _)] using
          residueClass_le (a : ZMod q) n)
    obtain ⟨L, hL, hle⟩ := exists_hasSum_term_gaussian_bound _ V hz hU hcut hB
    have hsign : (U * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2).re +
        (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re = 0 := by
      have hc : (U * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) +
          (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2) = 0 := by ring
      rw [← add_re, hc, zero_re]
    rw [hL.tsum_eq, norm_mul, norm_exp]
    refine (mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le).trans ?_
    simpa only [← mul_assoc, ← Real.exp_add, hsign, Real.exp_zero, one_mul] using hBU
  refine hdetect (NeZero.ne q) hU hUA hq (a : ZMod q) S M hSM hM (residueClassTailNumerator a ∅)
    hF (residueClassTailNumerator_zero a ∅) (fun z hz _ ↦ hFle z hz) ?_ ?_ ?_ ?_
  · intro z hz hre
    rw [← Finset.tsum_subtype']
    exact hout (↑S : Set ℕ) hz fun n hn ↦
      mul_nonpos_of_nonpos_of_nonneg (by linarith [hS n hn, (gaussianShift_mem_Icc hz.le).1])
        (sub_nonneg.mpr hre)
  · intro z _ hre
    have hsum := hasSum_residueClassTailNumerator_div a ∅ ((inv_pos.mpr hUpos).trans hre)
    exact ((Finset.hasSum_iff_compl ∅).mpr (by simpa using hsum))
  · intro z hz hre
    exact hout (↑(S ∪ M) : Set ℕ)ᶜ hz fun n hn ↦
      mul_nonpos_of_nonneg_of_nonpos (by linarith [hfar n hn, (gaussianShift_mem_Icc hz.le).2])
        (sub_nonpos.mpr hre.le)
  · intro hfree z hz _
    exact hmiddle (a : ZMod q) M hU hz.le hM fun p hp hp' he ↦ hfree p hp ⟨hp', he⟩

end TauCeti.LSeries
