/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.PowerLevel
import TauCeti.NumberTheory.LSeries.GaussianCutoff
import TauCeti.NumberTheory.LSeries.GaussianWindow
import TauCeti.NumberTheory.LSeries.PrimeWindow
import TauCeti.NumberTheory.LSeries.ResidueClassTail
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.VonMangoldt
import Mathlib.Analysis.Real.Sqrt

/-!
# Primes in logarithmic windows at powers of a fixed modulus

A uniform bound for pole-cleared logarithmic derivatives on a disc about `1` forces each
invertible residue class to contain a prime in a logarithmic window. For powers of a fixed
modulus the required disc estimate is uniform in the exponent. In particular, for any
fixed nonzero `m` and natural number `A`, a window `[U, U + W]` with `W ≤ U ≤ W ^ A`
contains the logarithm of a prime in every invertible class modulo `m ^ k`, uniformly
when `m ^ k ≤ W ^ A` and `W` is large enough.

The Gaussian window argument follows `New.exists_prime_modEq_one_log_mem` in
[lsernau/grh-lean, `Primes.lean`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean).
-/

public section

open Complex Filter Finset Metric Set
open DirichletCharacter ArithmeticFunction.vonMangoldt

namespace TauCeti.LSeries

-- Apply the same reference-abscissa comparison to both the finite initial part and the tail.
private theorem norm_gaussian_mul_tsum_residueClass_le {q : ℕ} (a : ZMod q) (J : Set ℕ)
    {X U : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ = 1) (hU : X ^ 2 ≤ U)
    (hcut : ∀ n ∈ J, (Real.log n - (U + gaussianShift X z)) * (U⁻¹ - z.re) ≤ 0)
    (href : ∃ B, HasSum (fun n : J ↦ ‖_root_.LSeries.term
      (fun k ↦ (residueClass a k : ℂ)) (1 + (U⁻¹ : ℝ)) n‖) B ∧ B ≤ U) :
    ‖Complex.exp ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2) *
        ∑' n : J, _root_.LSeries.term (fun k ↦ (residueClass a k : ℂ)) (1 + z) n‖ ≤ U := by
  obtain ⟨B, hB, hBU⟩ := href
  obtain ⟨L, hL, hLe⟩ := exists_hasSum_term_gaussian_bound _ J hz hU hcut hB
  rw [hL.tsum_eq, norm_mul, Complex.norm_exp]
  have he : ((U : ℂ) * z + (X : ℂ) / 4 * (1 + X * z) ^ 2 - 2).re =
      -(2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re := by
    rw [← neg_re]
    congr 1
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hLe (Real.exp_pos _).le).trans
    (by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]; exact hBU)

-- Isolate the two truncated parts; every omitted index lies beyond the logarithmic window.
private theorem exists_gaussian_window_finsets (U W : ℝ) :
    ∃ S M : Finset ℕ, Disjoint S M ∧
      (∀ n ∈ S, Real.log (n : ℝ) < U) ∧
      (∀ n ∈ M, Real.log (n : ℝ) ∈ Set.Icc U (U + W)) ∧
      (∀ n ∉ S ∪ M, U + W ≤ Real.log (n : ℝ)) := by
  classical
  let P := Finset.Iic ⌊Real.exp (U + W)⌋₊
  let S := P.filter fun n : ℕ ↦ Real.log (n : ℝ) < U
  let M := P.filter fun n : ℕ ↦ Real.log (n : ℝ) ∈ Set.Icc U (U + W)
  refine ⟨S, M, Finset.disjoint_left.mpr (fun n hn hm ↦
    (Finset.mem_filter.mp hn).2.not_ge (Finset.mem_filter.mp hm).2.1),
    (fun n hn ↦ (Finset.mem_filter.mp hn).2), (fun n hn ↦ (Finset.mem_filter.mp hn).2), ?_⟩
  intro n hn
  by_contra! hnlog
  have hnP : n ∈ P := Finset.mem_Iic.mpr (Nat.le_floor (Real.le_exp_of_log_le hnlog.le))
  refine hn (Finset.mem_union.mpr ?_)
  rcases lt_or_ge (Real.log (n : ℝ)) U with hnU | hnU
  · exact Or.inl (Finset.mem_filter.mpr ⟨hnP, hnU⟩)
  · exact Or.inr (Finset.mem_filter.mpr ⟨hnP, hnU, hnlog.le⟩)

-- Translate the zero-free disc to the disc used by the Gaussian window argument.
private theorem gaussian_window_numerator {q : ℕ} [NeZero q] (a : (ZMod q)ˣ) {X : ℝ} (hX : 0 < X)
    (hzero : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ‖s - 1‖ ≤ X⁻¹ →
      χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X) :
    DiffContOnCl ℂ (residueClassTailNumerator a ∅) (ball 0 X⁻¹) ∧
      ∀ z : ℂ, ‖(X : ℂ) * z‖ = 1 → ‖residueClassTailNumerator a ∅ z‖ ≤ 2 := by
  have hb (z : ℂ) (hz : ‖z‖ ≤ X⁻¹) (χ : DirichletCharacter ℂ q) :=
    hzero χ (1 + z) (by simpa using hz)
  constructor
  · refine DifferentiableOn.diffContOnCl_ball (U := closedBall 0 X⁻¹) (fun z hz ↦ ?_) Subset.rfl
    rw [mem_closedBall, dist_zero_right] at hz
    refine (analyticAt_residueClassTailNumerator a ∅ ?_ ?_).differentiableAt.differentiableWithinAt
    · simpa only [entireLFunction_one] using (hb z hz 1).1
    · intro χ hχ
      simpa only [entireLFunction_of_ne_one hχ] using (hb z hz χ).1
  · intro z hz
    have hzn : ‖z‖ = X⁻¹ := by
      rw [norm_mul, norm_real, Real.norm_of_nonneg hX.le] at hz
      rw [← one_div]
      exact (eq_div_iff hX.ne').2 (by rwa [mul_comm])
    have h := norm_residueClassTailNumerator_empty_le a
      (by simpa only [entireLFunction_one] using (hb z hzn.le 1).2)
      (fun χ hχ ↦ by simpa only [entireLFunction_of_ne_one hχ] using (hb z hzn.le χ).2)
    have hφ : 1 ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    rw [hzn, inv_mul_cancel₀ hX.ne'] at h
    linarith [inv_le_one_of_one_le₀ hφ]

/-- For all sufficiently large `X` depending only on `A`, a modulus with `φ(q) ≤ X ^ A` whose
pole-cleared Dirichlet L-functions are nonzero on `‖s - 1‖ ≤ 1 / X` with logarithmic derivatives
of norm at most `X` there has a prime in every invertible class in every logarithmic window
`[U, U + X²]` with `X² ≤ U ≤ X ^ A`. -/
theorem eventually_exists_prime_log_mem_Icc_of_logDeriv_bounds (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ {q : ℕ} [NeZero q], (q.totient : ℝ) ≤ X ^ A →
      (∀ (χ : DirichletCharacter ℂ q) (s : ℂ), ‖s - 1‖ ≤ X⁻¹ →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X) →
      ∀ (a : (ZMod q)ˣ) (U : ℝ), X ^ 2 ≤ U → U ≤ X ^ A →
        ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = a ∧ Real.log p ∈ Set.Icc U (U + X ^ 2) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp eventually_exists_hasSum_norm_term_one_add_inv_le
  have hlarge := (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).eventually (eventually_ge_atTop B)
  filter_upwards [eventually_exists_prime_log_mem_Icc_of_gaussian_bounds A,
    eventually_norm_gaussian_window_sum_le_one, eventually_gt_atTop (1 : ℝ), hlarge]
    with X hex hmid hX hlarge q _ hq hzero a U hU hUA
  have hX₀ : 0 < X := by linarith
  have hU₀ : 0 < U := (sq_pos_of_pos hX₀).trans_le hU
  obtain ⟨S, M, hSM, hS, hM, hT⟩ := exists_gaussian_window_finsets U (X ^ 2)
  have href (J : Set ℕ) := hB U (hlarge.trans hU) (fun k ↦ (residueClass (a : ZMod q) k : ℂ))
    J (fun n _ _ ↦ by
      rw [norm_real, Real.norm_of_nonneg (residueClass_nonneg _ _)]
      exact residueClass_le (a : ZMod q) n)
  obtain ⟨hF, hboundary⟩ := gaussian_window_numerator a hX₀ hzero
  refine hex (NeZero.ne q) hU hUA hq (a : ZMod q) S M hSM hM (residueClassTailNumerator a ∅) hF
    (residueClassTailNumerator_zero ..) (fun z hz _ ↦ hboundary z hz) ?_ ?_ ?_ ?_
  · intro z hz hr
    have hc (n : ℕ) (hn : n ∈ (S : Set ℕ)) :
        (Real.log n - (U + gaussianShift X z)) * (U⁻¹ - z.re) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (by linarith [hS n hn, (gaussianShift_mem_Icc hz.le).1]) (sub_nonneg.mpr hr)
    have h := norm_gaussian_mul_tsum_residueClass_le (a : ZMod q) (S : Set ℕ) hz hU hc (href _)
    have heq : (∑' n : (S : Set ℕ),
        _root_.LSeries.term (fun k ↦ (residueClass (a : ZMod q) k : ℂ)) (1 + z) n) =
        ∑ n ∈ S, _root_.LSeries.term (fun k ↦ (residueClass (a : ZMod q) k : ℂ)) (1 + z) n :=
      Finset.tsum_subtype S _
    rwa [heq] at h
  · intro z _ hr
    let e : {n : ℕ // n ∉ (∅ : Finset ℕ)} ≃ ℕ :=
      Equiv.subtypeUnivEquiv fun n ↦ Finset.notMem_empty n
    exact (e.hasSum_iff).mp (hasSum_residueClassTailNumerator_div a ∅ ((inv_pos.mpr hU₀).trans hr))
  · intro z hz hr
    refine norm_gaussian_mul_tsum_residueClass_le (a : ZMod q) (↑(S ∪ M) : Set ℕ)ᶜ
      hz hU (fun n hn ↦ ?_) (href _)
    exact mul_nonpos_of_nonneg_of_nonpos
      (by linarith [hT n hn, (gaussianShift_mem_Icc hz.le).2]) (sub_nonpos.mpr hr.le)
  · intro hno z hz _
    exact hmid (a : ZMod q) M hU hz.le hM (fun p hp hpp ha ↦ hno p hp ⟨hpp, ha⟩)

/-- For powers of a fixed nonzero modulus, every invertible class contains a prime whose
logarithm lies in `[U, U + W]`, uniformly for `W ≤ U ≤ W ^ A` and `m ^ k ≤ W ^ A`, once `W`
is large in terms of `m` and `A`. -/
theorem eventually_exists_prime_log_mem_Icc_pow_level (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ (k : ℕ) (a : (ZMod (m ^ k))ˣ) (U : ℝ),
      (↑(m ^ k) : ℝ) ≤ W ^ A → W ≤ U → U ≤ W ^ A →
      ∃ p : ℕ, p.Prime ∧ (p : ZMod (m ^ k)) = a ∧ Real.log p ∈ Set.Icc U (U + W) := by
  filter_upwards [Real.tendsto_sqrt_atTop.eventually
    (eventually_exists_prime_log_mem_Icc_of_logDeriv_bounds (2 * A)),
    Real.tendsto_sqrt_atTop.eventually
      (eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_pow_level m (2 * A)),
    eventually_ge_atTop (0 : ℝ)] with W hprime hzero hW k a U hk hU hUA
  have hpow : (√W) ^ (2 * A) = W ^ A := by rw [pow_mul, Real.sq_sqrt hW]
  have hφ : ((m ^ k).totient : ℝ) ≤ W ^ A :=
    (by exact_mod_cast Nat.totient_le (m ^ k) : ((m ^ k).totient : ℝ) ≤ ↑(m ^ k)).trans hk
  have hp := hprime (q := m ^ k) (by rwa [hpow])
    (hzero k (by rwa [hpow])) a U (by rwa [Real.sq_sqrt hW]) (by rwa [hpow])
  simpa only [Real.sq_sqrt hW] using hp

end TauCeti.LSeries
