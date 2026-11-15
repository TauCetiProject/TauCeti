/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# The analytic conductor of completed L-function data

The analytic conductor combines the arithmetic conductor with the sizes of the shifted
archimedean parameters. A complex gamma factor contributes two real-gamma shifts, separated
by one. Every factor uses the offset `+3`.

The strip comparison is uniform over records with fixed degree and bounded shifts: its
constants are independent of the arithmetic conductor. This is the comparison needed to
express vertical growth and convexity estimates in terms of the analytic conductor.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.1, equation (5.7).
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The analytic conductor at `s`. Each complex gamma shift contributes the pair `ν, ν + 1`.
The arithmetic conductor is the existing field `conductor`. -/
noncomputable def analyticConductorAt (d : AnalyticLFunctionData) (s : ℂ) : ℝ :=
  (d.conductor : ℝ) *
    ((d.gammaR + d.gammaC + d.gammaC.map (· + 1)).map fun μ ↦ ‖s + μ‖ + 3).prod

/-- The product formula for the analytic conductor, with each complex gamma factor split
into its two real-gamma contributions. -/
theorem analyticConductorAt_def (d : AnalyticLFunctionData) (s : ℂ) :
    d.analyticConductorAt s = (d.conductor : ℝ) *
      (d.gammaR.map fun μ ↦ ‖s + μ‖ + 3).prod *
      (d.gammaC.map fun ν ↦ (‖s + ν‖ + 3) * (‖s + ν + 1‖ + 3)).prod := by
  simp [analyticConductorAt, Multiset.map_add, Multiset.prod_add, Multiset.map_map,
    Multiset.prod_map_mul, add_assoc, mul_assoc]

/-- The analytic conductor at the analytic central point `1/2`. -/
noncomputable def centralAnalyticConductor (d : AnalyticLFunctionData) : ℝ :=
  d.analyticConductorAt (1 / 2)

theorem centralAnalyticConductor_def (d : AnalyticLFunctionData) :
    d.centralAnalyticConductor = d.analyticConductorAt (1 / 2) := (rfl)

/-- The offset gives a factor of at least three for every unit of degree. -/
theorem conductor_mul_three_pow_degree_le (d : AnalyticLFunctionData) (s : ℂ) :
    (d.conductor : ℝ) * 3 ^ d.degree ≤ d.analyticConductorAt s := by
  have h := Multiset.prod_map_le_prod_map₀
    (s := d.gammaR + d.gammaC + d.gammaC.map (· + 1))
    (fun _ ↦ (3 : ℝ)) (fun μ ↦ ‖s + μ‖ + 3) (fun _ _ ↦ by positivity)
    (fun μ _ ↦ by have := norm_nonneg (s + μ); linarith)
  have hcard : (d.gammaR + d.gammaC + d.gammaC.map (· + 1)).card = d.degree := by
    simp [degree_def]; omega
  simp only [Multiset.map_const', Multiset.prod_replicate, hcard] at h
  simpa only [analyticConductorAt] using
    mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (d.conductor : ℝ))

/-- The analytic conductor is always at least one, including for degree-zero data. -/
theorem one_le_analyticConductorAt (d : AnalyticLFunctionData) (s : ℂ) :
    1 ≤ d.analyticConductorAt s := by
  have hNat : 1 ≤ (d.conductor : ℕ) := d.conductor.pos
  have hN : (1 : ℝ) ≤ d.conductor := by
    exact_mod_cast hNat
  have hpow : (1 : ℝ) ≤ 3 ^ d.degree := one_le_pow₀ (by norm_num)
  exact (one_le_mul_of_one_le_of_one_le hN hpow).trans (d.conductor_mul_three_pow_degree_le s)

/-- In particular the analytic conductor never vanishes. -/
theorem analyticConductorAt_pos (d : AnalyticLFunctionData) (s : ℂ) :
    0 < d.analyticConductorAt s :=
  lt_of_lt_of_le zero_lt_one (d.one_le_analyticConductorAt s)

/-- The analytic conductor is continuous, also at poles and zeros of the completed function. -/
@[fun_prop]
theorem continuous_analyticConductorAt (d : AnalyticLFunctionData) :
    Continuous d.analyticConductorAt := by
  unfold analyticConductorAt
  fun_prop

/-- Duality conjugates the evaluation point and leaves the analytic conductor unchanged. -/
@[simp]
theorem analyticConductorAt_dual (d : AnalyticLFunctionData) (s : ℂ) :
    d.dual.analyticConductorAt s = d.analyticConductorAt (conj s) := by
  have hnorm (μ : ℂ) : ‖s + conj μ‖ = ‖conj s + μ‖ := by
    rw [← norm_conj (s + conj μ)]
    simp
  have hnorm1 (μ : ℂ) : ‖s + conj μ + 1‖ = ‖conj s + μ + 1‖ := by
    rw [← norm_conj (s + conj μ + 1)]
    simp only [map_add, conj_conj, map_one]
  simp only [analyticConductorAt_def, dual_conductor, dual_gammaR, dual_gammaC,
    Multiset.map_map, Function.comp_def, hnorm, hnorm1]

/-- The central analytic conductor is invariant under duality. -/
@[simp]
theorem centralAnalyticConductor_dual (d : AnalyticLFunctionData) :
    d.dual.centralAnalyticConductor = d.centralAnalyticConductor := by
  simp [centralAnalyticConductor_def, map_ofNat]

private theorem norm_le_of_mem_gammaShifts (d : AnalyticLFunctionData) {M : ℝ}
    (hR : ∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) (hC : ∀ ν ∈ d.gammaC, ‖ν‖ ≤ M)
    {μ : ℂ} (hμ : μ ∈ d.gammaR + d.gammaC + d.gammaC.map (· + 1)) : ‖μ‖ ≤ M + 1 := by
  simp only [Multiset.mem_add, Multiset.mem_map] at hμ
  rcases hμ with (hμ | hμ) | ⟨ν, hν, rfl⟩
  · linarith [hR μ hμ]
  · linarith [hC μ hμ]
  · simpa using (norm_add_le ν 1).trans (by simpa using add_le_add_right (hC ν hν) 1)

/-- An upper bound on a strip, uniform in the conductor. The same bound on the original
real and complex shifts suffices; the extra `+1` shift is absorbed in the constant. -/
theorem analyticConductorAt_le (d : AnalyticLFunctionData) {B M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hR : ∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) (hC : ∀ ν ∈ d.gammaC, ‖ν‖ ≤ M)
    {s : ℂ} (hs : |s.re| ≤ B) :
    d.analyticConductorAt s ≤
      (B + M + 2) ^ d.degree * (d.conductor : ℝ) * (|s.im| + 3) ^ d.degree := by
  have h := Multiset.prod_map_le_prod_map₀
    (s := d.gammaR + d.gammaC + d.gammaC.map (· + 1))
    (fun μ ↦ ‖s + μ‖ + 3) (fun _ ↦ (B + M + 2) * (|s.im| + 3))
    (fun _ _ ↦ by positivity) (fun μ hμ ↦ by
      have hn := norm_add_le s μ
      have hs' := norm_le_abs_re_add_abs_im s
      have hm := d.norm_le_of_mem_gammaShifts hR hC hμ
      have ht := abs_nonneg s.im
      nlinarith)
  have hcard : (d.gammaR + d.gammaC + d.gammaC.map (· + 1)).card = d.degree := by
    simp [degree_def]; omega
  simp only [Multiset.map_const', Multiset.prod_replicate, hcard, mul_pow] at h
  simpa only [analyticConductorAt, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (d.conductor : ℝ))

/-- A lower comparison with the height, uniform in the conductor. This direction needs
no bound on the real part. -/
theorem conductor_mul_height_pow_le (d : AnalyticLFunctionData) {M : ℝ} (hM : 0 ≤ M)
    (hR : ∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) (hC : ∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) (s : ℂ) :
    (d.conductor : ℝ) * (|s.im| + 3) ^ d.degree ≤
      (M + 2) ^ d.degree * d.analyticConductorAt s := by
  have h := Multiset.prod_map_le_prod_map₀
    (s := d.gammaR + d.gammaC + d.gammaC.map (· + 1))
    (fun _ ↦ |s.im| + 3) (fun μ ↦ (M + 2) * (‖s + μ‖ + 3))
    (fun _ _ ↦ by positivity)
    (fun μ hμ ↦ by
      have hn : |s.im| ≤ ‖s + μ‖ + ‖μ‖ := by
        calc
          |s.im| ≤ ‖s‖ := abs_im_le_norm s
          _ = ‖s + μ - μ‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖s + μ‖ + ‖μ‖ := norm_sub_le _ _
      have hm := d.norm_le_of_mem_gammaShifts hR hC hμ
      have hp := norm_nonneg (s + μ)
      nlinarith)
  have hcard : (d.gammaR + d.gammaC + d.gammaC.map (· + 1)).card = d.degree := by
    simp [degree_def]; omega
  simp only [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard] at h
  simpa only [analyticConductorAt, mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (d.conductor : ℝ))

/-- Two-sided vertical-strip comparison, with constants chosen before the record. They depend
only on the strip, degree and shift bound, not on the arithmetic conductor. -/
theorem exists_analyticConductorAt_strip_bounds (a b : ℝ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Set.Icc a b →
        C₁ * (d.conductor : ℝ) * (|s.im| + 3) ^ n ≤ d.analyticConductorAt s ∧
        d.analyticConductorAt s ≤ C₂ * (d.conductor : ℝ) * (|s.im| + 3) ^ n := by
  let B := max |a| |b|
  have hB : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  have hp : 0 < (M + 2) ^ n := pow_pos (by linarith) _
  refine ⟨((M + 2) ^ n)⁻¹, inv_pos.mpr hp,
    (B + M + 2) ^ n, pow_pos (by linarith) _, ?_⟩
  intro d hd hR hC s hs
  have hsB : |s.re| ≤ B := abs_le.mpr ⟨by
    have := neg_abs_le a
    have := le_max_left |a| |b|
    dsimp [B]
    linarith [hs.1], by
    exact hs.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  constructor
  · have h := d.conductor_mul_height_pow_le hM hR hC s
    rw [hd] at h
    calc
      ((M + 2) ^ n)⁻¹ * (d.conductor : ℝ) * (|s.im| + 3) ^ n =
          ((M + 2) ^ n)⁻¹ * ((d.conductor : ℝ) * (|s.im| + 3) ^ n) := mul_assoc _ _ _
      _ ≤ ((M + 2) ^ n)⁻¹ * ((M + 2) ^ n * d.analyticConductorAt s) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
      _ = d.analyticConductorAt s := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  · simpa only [hd] using d.analyticConductorAt_le hB hM hR hC hsB

end TauCeti.LFunctions.AnalyticLFunctionData
