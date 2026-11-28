/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.Archimedean
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Archimedean frame masses and successive hermitian mass ratios

The archimedean factors of the consecutive genus mass ratios cancel the sphere factors
of the frame mass. This leaves a product of Euler factors, whose logarithmic errors can
be summed over the rank interval. A separate factor accounts for the correction from the
level. The comparison applies once the consecutive mass formula and Euler factor bounds
are available.

The normalizations are those of `New.Data.unitSphereMass`, `New.Data.frameMass` and
`New.Data.prod_frameMass_mul_le` in `grh/src/New/Spanning/Unfolding/FrameMass.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Finset Real NumberField

namespace TauCeti

/-- The archimedean sphere factor at rank `j + 1`, with `a` the absolute value of the
chosen different generator at that place. -/
noncomputable def hermitianSphereMass (a : ℝ) (j : ℕ) : ℝ :=
  (2 * π) ^ (j + 1) / (a ^ ((j : ℝ) + 1 / 2) * j.factorial)

/-- Expand the normalized sphere factor at rank `j + 1`. -/
theorem hermitianSphereMass_def (a : ℝ) (j : ℕ) :
    hermitianSphereMass a j = (2 * π) ^ (j + 1) / (a ^ ((j : ℝ) + 1 / 2) * j.factorial) :=
  (rfl)

/-- The archimedean factor of a frame extending rank `k` to rank `r`. For level `N`, the
normalization `q` is `N ^ k`. -/
noncomputable def hermitianFrameMass (a q : ℝ) (k r : ℕ) : ℝ :=
  q * ∏ j ∈ Ico k r, hermitianSphereMass a j

/-- The frame factor in terms of the sphere factors for ranks `k + 1` through `r`. -/
theorem hermitianFrameMass_def (a q : ℝ) (k r : ℕ) :
    hermitianFrameMass a q k r = q * ∏ j ∈ Ico k r, hermitianSphereMass a j := (rfl)

/-- When the placewise factors have geometric mean `D`, the product of the sphere masses
is the reciprocal of the archimedean multiplier in the consecutive genus mass formula. -/
theorem prod_hermitianSphereMass {ι : Type*} [Fintype ι] {a : ι → ℝ} {D : ℝ}
    (ha : ∀ v, 0 ≤ a v) (hD : 0 ≤ D) (hprod : (∏ v, a v) = D ^ Fintype.card ι) (j : ℕ) :
    (∏ v, hermitianSphereMass (a v) j) =
      ((2 * π) ^ (j + 1) / (D ^ ((j : ℝ) + 1 / 2) * j.factorial)) ^ Fintype.card ι := by
  simp only [hermitianSphereMass_def, prod_div_distrib, prod_mul_distrib, prod_const, card_univ]
  rw [finsetProd_rpow _ _ (fun v _ ↦ ha v), hprod,
    ← rpow_natCast_mul hD, mul_comm (Fintype.card ι : ℝ), rpow_mul_natCast hD, div_pow]
  simp only [mul_pow]

/-- Multiply the consecutive mass ratios from `k` to `r` and cancel the sphere factors.
The remaining product consists of the Euler factors `L j` at ranks `j + 1`. -/
theorem prod_hermitianFrameMass_mul_eq_of_mass_ratios {ι : Type*} [Fintype ι]
    {a : ι → ℝ} {D q : ℝ} {k r : ℕ} {mass L : ℕ → ℝ} (hkr : k ≤ r)
    (ha : ∀ v, 0 ≤ a v) (hD : 0 < D) (hprod : (∏ v, a v) = D ^ Fintype.card ι)
    (hratio : ∀ j ∈ Ico k r, mass (j + 1) = mass j *
      (D ^ ((j : ℝ) + 1 / 2) * j.factorial / (2 * π) ^ (j + 1)) ^ Fintype.card ι * L j) :
    (∏ v, hermitianFrameMass (a v) q k r) * mass r =
      q ^ Fintype.card ι * mass k * ∏ j ∈ Ico k r, L j := by
  have hcancel (j : ℕ) : (∏ v, hermitianSphereMass (a v) j) *
      (D ^ ((j : ℝ) + 1 / 2) * j.factorial / (2 * π) ^ (j + 1)) ^ Fintype.card ι = 1 := by
    have hπ : (2 * π) ^ (j + 1) ≠ 0 := by positivity
    have hd : D ^ ((j : ℝ) + 1 / 2) * j.factorial ≠ 0 := by positivity
    rw [prod_hermitianSphereMass ha hD.le hprod, ← mul_pow, div_mul_div_comm,
      mul_comm _ ((2 * π) ^ (j + 1)), div_self (mul_ne_zero hπ hd), one_pow]
  have htel (l : ℕ) (hkl : k ≤ l) (hl : l ≤ r) :
      (∏ j ∈ Ico k l, ∏ v, hermitianSphereMass (a v) j) * mass l =
        mass k * ∏ j ∈ Ico k l, L j := by
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ j hkj ih =>
      have hj : j ∈ Ico k r := mem_Ico.mpr ⟨hkj, by omega⟩
      rw [prod_Ico_succ_top hkj, prod_Ico_succ_top hkj, hratio j hj]
      calc
        _ = ((∏ i ∈ Ico k j, ∏ v, hermitianSphereMass (a v) i) * mass j) *
              ((∏ v, hermitianSphereMass (a v) j) *
                (D ^ ((j : ℝ) + 1 / 2) * j.factorial / (2 * π) ^ (j + 1)) ^ Fintype.card ι) * L j :=
          by ring
        _ = _ := by rw [hcancel, mul_one, ih (by omega), ← mul_assoc]
  simp only [hermitianFrameMass_def, prod_mul_distrib, prod_const, card_univ]
  rw [prod_comm, mul_assoc, htel r hkr le_rfl, ← mul_assoc]

-- Pay for both the geometric Euler tail and the logarithm of the level correction.
private theorem frameMass_log_error_le {x b N : ℝ} {f k : ℕ}
    (hx : 4 ≤ x) (hb : 1 ≤ b) (hbx : log b ≤ x) (hN : 2 ≤ N)
    (hf : (f : ℝ) ≤ x ^ 12) (hk : x ^ 5 ≤ 2 * (k : ℝ)) :
    1 < N ^ k ∧ 2 * (f : ℝ) / 2 ^ k + 2 * (f : ℝ) / (N ^ k - 1) ≤ (1 + b ^ 9)⁻¹ := by
  have hx₀ : 0 < x := by linarith
  have hb₀ : 0 < b := zero_lt_one.trans_le hb
  have hb₉ : 1 ≤ b ^ 9 := one_le_pow₀ hb
  have hx₄ : (4 : ℝ) ^ 4 ≤ x ^ 4 := by gcongr
  have hx₅ : 256 * x ≤ x ^ 5 := by
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_right hx₄ hx₀.le]
  have hlog₂ : (1 / 2 : ℝ) ≤ log 2 := by
    convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    norm_num
  have hlog₁₆ : log (16 : ℝ) ≤ 4 := by
    have he : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
    rw [he, log_pow, Nat.cast_ofNat]
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpow : (16 * (f : ℝ) * b ^ 9) ≤ (2 : ℝ) ^ k := calc
    _ ≤ 16 * x ^ 12 * b ^ 9 := by gcongr
    _ ≤ _ := by
      apply (log_le_log_iff (by positivity) (by positivity)).mp
      rw [log_mul (by positivity) (pow_ne_zero _ hb₀.ne'), log_mul (by norm_num) (by positivity),
        log_pow, log_pow, log_pow]
      simp only [Nat.cast_ofNat]
      have hlogx := log_le_sub_one_of_pos hx₀
      have hklog := mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg k)
      linarith only [hx, hx₅, hk, hbx, hlogx, hklog, hlog₁₆]
  have hk₀ : 1 ≤ k := by
    have hkp : 0 < (k : ℝ) := by linarith [pow_pos hx₀ 5]
    exact Nat.cast_pos.mp hkp
  have htwo : 2 ≤ (2 : ℝ) ^ k := le_self_pow₀ (by norm_num) (by omega)
  have hq : (2 : ℝ) ^ k ≤ N ^ k := by gcongr
  have hhalf : (2 : ℝ) ^ k / 2 ≤ N ^ k - 1 := by linarith
  refine ⟨by linarith [htwo.trans hq], ?_⟩
  calc
    _ ≤ 2 * (f : ℝ) / 2 ^ k + 2 * (f : ℝ) / ((2 : ℝ) ^ k / 2) := by
      gcongr
    _ = 6 * (f : ℝ) / 2 ^ k := by ring
    _ ≤ _ := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      calc
        _ = (f : ℝ) * (6 * (1 + b ^ 9)) := by ring
        _ ≤ (f : ℝ) * (16 * b ^ 9) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg f)
        _ ≤ _ := by simpa only [mul_comm, mul_left_comm, mul_assoc] using hpow

-- This is the remaining factor after the archimedean terms in the mass formula cancel.
private theorem eulerFactors_mul_levelCorrection_le {q b : ℝ} {f k r : ℕ} {L : ℕ → ℝ}
    (hkr : k ≤ r) (hq : 1 < q) (hb : 0 < b)
    (hL : ∀ j ∈ Ico k r, log (L j) ≤ 2 * (f : ℝ) / 2 ^ (j + 1))
    (hbudget : 2 * (f : ℝ) / 2 ^ k + 2 * (f : ℝ) / (q - 1) ≤ (1 + b ^ 9)⁻¹) :
    (∏ j ∈ Ico k r, L j) * (q / (q - 1)) ^ (2 * f) ≤ 1 + (b ^ 9)⁻¹ := by
  have hq₀ : 0 < q - 1 := sub_pos.mpr hq
  have hsum : ∑ j ∈ Ico k r, 2 * (f : ℝ) / 2 ^ (j + 1) ≤ 2 * (f : ℝ) / 2 ^ k := by
    calc
      _ = ∑ j ∈ Ico k r, (-(2 * (f : ℝ) / 2 ^ (j + 1)) - -(2 * (f : ℝ) / 2 ^ j)) := by
        apply sum_congr rfl
        intro j _
        rw [pow_succ]
        ring
      _ ≤ _ := by
        rw [sum_Ico_sub (fun j ↦ -(2 * (f : ℝ) / 2 ^ j)) hkr]
        have h : 0 ≤ 2 * (f : ℝ) / 2 ^ r := by positivity
        linarith
  have hqlog : log (q / (q - 1)) ≤ 1 / (q - 1) := by
    convert log_le_sub_one_of_pos (div_pos (zero_lt_one.trans hq) hq₀) using 1
    field_simp
    ring
  have hlevel : (q / (q - 1)) ^ (2 * f) ≤ exp (2 * (f : ℝ) / (q - 1)) := by
    rw [← log_le_iff_le_exp (by positivity), log_pow, Nat.cast_mul, Nat.cast_ofNat]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hqlog (by positivity : 0 ≤ 2 * (f : ℝ))
  calc
    _ ≤ (∏ j ∈ Ico k r, |L j|) * (q / (q - 1)) ^ (2 * f) := by
      rw [← abs_prod]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ exp (∑ j ∈ Ico k r, 2 * (f : ℝ) / 2 ^ (j + 1)) * exp (2 * (f : ℝ) / (q - 1)) := by
      rw [exp_sum]
      apply mul_le_mul (prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun j hj ↦ ?_) hlevel
        (by positivity) (by positivity)
      exact le_exp_of_log_le (by simpa only [log_abs] using hL j hj)
    _ ≤ exp ((1 + b ^ 9)⁻¹) := by
      rw [← exp_add]
      exact exp_le_exp.mpr ((add_le_add hsum le_rfl).trans hbudget)
    _ ≤ 1 + (b ^ 9)⁻¹ := by
      have hb₉ : 0 < b ^ 9 := pow_pos hb _
      have hpos : 0 < 1 + (b ^ 9)⁻¹ := add_pos one_pos (inv_pos.mpr hb₉)
      rw [← le_log_iff_exp_le hpos]
      have h := one_sub_inv_le_log_of_pos hpos
      have he : 1 - (1 + (b ^ 9)⁻¹)⁻¹ = (1 + b ^ 9)⁻¹ := by
        field_simp
        ring
      rwa [he] at h

/-- The frame-mass comparison with the level correction. The consecutive mass formula is an
input, with `L j` the Euler factor at rank `j + 1`. If the starting rank is at least `x^5 / 2`,
the number of infinite places is at most `x^12`, and `log b ≤ x`, then the product of the
Euler factors and the level correction cost at most `1 + b⁻⁹`. -/
theorem prod_hermitianFrameMass_mul_le_of_mass_ratios {K : Type*} [Field K] [NumberField K]
    [IsTotallyComplex K] {δ : 𝓞 K} (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ})
    {x b N : ℝ} {k r : ℕ} {mass L : ℕ → ℝ} (hkr : k ≤ r) (hmass : 0 ≤ mass k)
    (hx : 4 ≤ x) (hb : 1 ≤ b) (hbx : log b ≤ x) (hN : 2 ≤ N)
    (hf : (Fintype.card (InfinitePlace K) : ℝ) ≤ x ^ 12) (hk : x ^ 5 ≤ 2 * (k : ℝ))
    (hratio : ∀ j ∈ Ico k r, mass (j + 1) = mass j *
      (rootDiscr K ^ ((j : ℝ) + 1 / 2) * j.factorial / (2 * π) ^ (j + 1)) ^
        Fintype.card (InfinitePlace K) * L j)
    (hL : ∀ j ∈ Ico k r, log (L j) ≤ 2 * (Fintype.card (InfinitePlace K) : ℝ) / 2 ^ (j + 1)) :
    (∏ v : InfinitePlace K, hermitianFrameMass (v (δ : K)) (N ^ k) k r) * mass r *
        (N ^ k / (N ^ k - 1)) ^ (2 * Fintype.card (InfinitePlace K)) ≤
      (1 + (b ^ 9)⁻¹) * N ^ (k * Fintype.card (InfinitePlace K)) * mass k := by
  have hD : 0 < rootDiscr K := by
    rw [rootDiscr_def, Int.cast_abs]
    exact rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast discr_ne_zero K)) _
  obtain ⟨hlevel, hbudget⟩ := frameMass_log_error_le hx hb hbx hN hf hk
  have hv (v : InfinitePlace K) : 0 ≤ v (δ : K) := apply_nonneg v _
  rw [prod_hermitianFrameMass_mul_eq_of_mass_ratios hkr hv hD
    (TauCeti.NumberField.prod_different_generator_eq_rootDiscr_pow hδ) hratio, mul_assoc,
    ← pow_mul, mul_assoc (1 + (b ^ 9)⁻¹), mul_comm (1 + (b ^ 9)⁻¹)]
  exact mul_le_mul_of_nonneg_left
    (eulerFactors_mul_levelCorrection_le hkr hlevel (zero_lt_one.trans_le hb) hL hbudget)
    (mul_nonneg (by positivity) hmass)

end TauCeti
