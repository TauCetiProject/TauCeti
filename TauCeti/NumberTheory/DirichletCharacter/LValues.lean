/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
public import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Cotangent
import TauCeti.Data.ZMod.Count
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Cotangent

/-!
# Generalized Bernoulli numbers and primitive character sums

For a primitive complex Dirichlet character `χ` modulo `N` and a natural weight `k ≥ 2`,
the integer-indexed critical-value sum has the normalization
`τ(χ) ∑' n : ℤ, χ⁻¹(n) n⁻ᵏ = -(2πi)ᵏ Bₖ,χ / (k! Nᵏ⁻¹)`.
Here `τ(χ)` uses the standard additive character, and `Bₖ,χ` is the generalized Bernoulli
number defined using residue representatives in `{1, …, N}`.

The formula includes both parities and modulus one: the integer sum is zero when the
character and weight have opposite parities. These special values give the constant
coefficients of normalized Eisenstein series.

In weight one the cotangent takes the place of the critical-value sum: for a nontrivial primitive
`φ` modulo `v ∣ N`, `∑_{j mod N} φ⁻¹(j) π cot (π j / N) = N · 2π i g(φ⁻¹) B₁,φ / v`
(`DirichletCharacter.IsPrimitive.sum_inv_mul_pi_mul_cot`), by the finite Fourier expansion of the
cotangent and the Fourier coefficients of `φ⁻¹`. For primitive odd characters the first
generalized Bernoulli number is nonzero (`DirichletCharacter.generalizedBernoulli_one_ne_zero`),
by the cotangent formula for `L(1, φ⁻¹)` and Dirichlet nonvanishing.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, equation (4.1).
* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Section 4.5.
-/

public noncomputable section

open Complex AddChar
open scoped Real

namespace DirichletCharacter

variable {N k : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- The integer-indexed critical-value sum of a primitive character, multiplied by its Gauss
sum, is an explicit multiple of its generalized Bernoulli number. No parity hypothesis is
needed: both sides vanish for opposite parities. -/
theorem gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli (hχ : χ.IsPrimitive)
    (hk : 2 ≤ k) :
    gaussSum χ ZMod.stdAddChar *
        (∑' n : ℤ, χ⁻¹ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ))) =
      -(2 * π * I) ^ k / ((k.factorial : ℂ) * (N : ℂ) ^ (k - 1)) *
        χ.generalizedBernoulli k := by
  classical
  have hNk : (N : ℂ) ^ (k - 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  -- Apply Mathlib's hasSum_one_div_pow_mul_fourier_mul_bernoulliFun at each residue,
  -- using its value in [0, 1).
  have hfourier (a : ZMod N) (n : ℤ) :
      fourier n ((a.val / (N : ℝ) : ℝ) : UnitAddCircle) =
        ZMod.stdAddChar ((n : ZMod N) * a) := by
    rw [fourier_coe_apply, ZMod.stdAddChar_apply]
    have h := ZMod.toCircle_intCast (N := N) (n * a.val)
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h]
    push_cast
    congr 1
    ring
  have hx (a : ZMod N) : (a.val / (N : ℝ) : ℝ) ∈ Set.Icc 0 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      (div_le_one (Nat.cast_pos.mpr (NeZero.pos N))).mpr
        (by exact_mod_cast (ZMod.val_lt a).le)⟩
  have hs (a : ZMod N) :=
    (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk (hx a)).mul_left (χ a)
  have hsum := hasSum_sum (s := Finset.univ) fun a _ ↦ hs a
  -- Mathlib's gaussSum_mulShift_of_isPrimitive evaluates the finite Fourier coefficient,
  -- also at nonunit frequencies.
  have hterm (n : ℤ) :
      (∑ a : ZMod N, χ a *
        (1 / (n : ℂ) ^ k * fourier n ((a.val / (N : ℝ) : ℝ) : UnitAddCircle))) =
      gaussSum χ ZMod.stdAddChar * (χ⁻¹ (n : ZMod N) * (n : ℂ) ^ (-(k : ℤ))) := by
    simp_rw [hfourier]
    have hgauss := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχ (n : ZMod N)
    simp only [gaussSum, AddChar.mulShift_apply] at hgauss
    simp_rw [← mul_assoc, mul_right_comm (χ _) (1 / (n : ℂ) ^ k)]
    rw [← Finset.sum_mul, hgauss]
    simp only [zpow_neg, zpow_natCast, one_div, gaussSum]
    ring
  -- The positive representative for the zero residue has the same Bernoulli value in k ≥ 2.
  have hB : χ.generalizedBernoulli k =
      (N : ℂ) ^ (k - 1) *
        ∑ a : ZMod N, χ a * bernoulliFun k (a.val / (N : ℝ)) := by
    rw [generalizedBernoulli_def]
    have hexp : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_natCast, map_pow, map_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    have hcast (x : ℚ) :
        algebraMap ℚ ℂ ((Polynomial.bernoulli k).eval x) =
          bernoulliFun k (x : ℝ) := by
      simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
        Polynomial.eval₂_at_apply]
      norm_cast
    by_cases ha : a = 0
    · subst a
      simp only [ite_true, div_self (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℚ) ≠ 0),
        hcast, Rat.cast_one, ZMod.val_zero, Nat.cast_zero, zero_div]
      exact congrArg ((↑) : ℝ → ℂ)
        (bernoulliFun_endpoints_eq_of_ne_one (by omega : k ≠ 1))
    · simp only [ha, ite_false, hcast, Rat.cast_div, Rat.cast_natCast]
  have hresult := hsum.congr_fun (fun n ↦ (hterm n).symm)
  -- Sum the Fourier identity and restore the power of the modulus in B_{k,χ}.
  rw [← tsum_mul_left, hresult.tsum_eq, hB]
  simp_rw [← mul_assoc, mul_comm (χ _ : ℂ) (-(2 * π * I) ^ k / (k.factorial : ℂ)),
    mul_assoc]
  rw [← Finset.mul_sum]
  field_simp

/-- **The cotangent sum of a primitive character.** For a nontrivial primitive `φ` modulo
`v ∣ N`, `∑_{j mod N} φ⁻¹(j) π cot (π j / N) = N · 2π i g(φ⁻¹) B₁,φ / v`. -/
theorem IsPrimitive.sum_inv_mul_pi_mul_cot {v N : ℕ} [NeZero v] [NeZero N]
    {φ : DirichletCharacter ℂ v} (hφ : φ.IsPrimitive) (hv : v ∣ N) (hφ1 : φ ≠ 1) :
    ∑ j : ZMod N, φ⁻¹ (j.val : ZMod v) * (π * cot (π * (j.val / N))) =
      N * (2 * π * I / v * gaussSum φ⁻¹ ZMod.stdAddChar * φ.generalizedBernoulli 1) := by
  have : Nontrivial (ZMod v) := ZMod.nontrivial_iff.mpr fun h ↦ hφ1 (φ.level_one' h)
  set L := N / v with hL
  have hN : N = v * L := (Nat.mul_div_cancel' hv).symm
  have hL0 : L ≠ 0 := fun h ↦ NeZero.ne N (by rw [hN, h, mul_zero])
  -- expand each cotangent in its finite Fourier series; the term at `j = 0` vanishes
  have hexp (j : ZMod N) : φ⁻¹ (j.val : ZMod v) * (π * cot (π * (j.val / N))) =
      π * I * φ⁻¹ (j.val : ZMod v) + 2 * π * I / N *
        ∑ m : ZMod N, (m.val : ℂ) * (φ⁻¹ (j.val : ZMod v) * ZMod.stdAddChar (m * j)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · simp [MulChar.map_zero]
    · rw [TauCeti.pi_mul_cot_pi_mul_val_div_eq_sum N hj]
      simp_rw [mul_left_comm _ (φ⁻¹ _), ← Finset.mul_sum]
      ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hφ.sum_inv_mul_stdAddChar hv, ← hL]
  rw [ZMod.sum_comp_natCast_val hv fun r ↦ φ⁻¹ r,
    MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hφ1), smul_zero, mul_zero, zero_add]
  -- only the multiples `m = L y` contribute, and `∑_y y φ(y) = v B₁,φ`
  have hreindex : ∑ m : ZMod N, (m.val : ℂ) * (if L ∣ m.val then
      (L : ℂ) * (φ ((m.val / L : ℕ) : ZMod v) * gaussSum φ⁻¹ ZMod.stdAddChar) else 0) =
      ∑ y : ZMod v, (L * y.val : ℕ) * ((L : ℂ) * (φ (y.val : ZMod v) *
        gaussSum φ⁻¹ ZMod.stdAddChar)) := by
    rw [← ZMod.sum_ite_dvd_val hv fun q ↦ ((L * q : ℕ) : ℂ) * ((L : ℂ) * (φ (q : ZMod v) *
      gaussSum φ⁻¹ ZMod.stdAddChar)), ← hL]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    split_ifs with h
    · rw [Nat.mul_div_cancel' h]
    · rw [mul_zero]
  rw [hreindex]
  simp_rw [ZMod.natCast_zmod_val]
  have hB := natCast_mul_generalizedBernoulli_one_of_ne_one hφ1
  have hsum : ∑ y : ZMod v, ((L * y.val : ℕ) : ℂ) *
      ((L : ℂ) * (φ y * gaussSum φ⁻¹ ZMod.stdAddChar)) =
      L * L * gaussSum φ⁻¹ ZMod.stdAddChar * (v * φ.generalizedBernoulli 1) := by
    rw [hB, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    push_cast
    ring
  rw [hsum]
  have hv0 : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  rw [hN]
  push_cast
  field_simp

/-- The first generalized Bernoulli number of a primitive odd character is nonzero.
Primitivity is essential: an imprimitive odd character can acquire an Euler factor vanishing
at zero. -/
theorem generalizedBernoulli_one_ne_zero (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    χ.generalizedBernoulli 1 ≠ 0 := by
  have hχ1 : χ ≠ 1 := by
    rintro rfl
    exact Odd.not_even 1 hodd even_one
  have hinv : χ⁻¹.Odd := by
    rw [Odd, MulChar.inv_apply_eq_inv', hodd, inv_neg, inv_one]
  have hL := χ⁻¹.two_mul_LFunction_one_eq_sum_mul_cot hinv
  have hsum := hχ.sum_inv_mul_pi_mul_cot (dvd_refl N) hχ1
  simp only [ZMod.natCast_zmod_val] at hsum
  simp_rw [div_mul_eq_mul_div] at hL
  rw [← Finset.sum_div, hsum] at hL
  intro hB
  have hzero : χ⁻¹.LFunction 1 = 0 := by simpa [hB] using hL
  exact LFunction_apply_one_ne_zero (inv_ne_one.mpr hχ1) hzero

omit [NeZero N] in
/-- For a character with `χ (-1) = -(-1) ^ k`, the series `∑ χ⁻¹ d * d ^ (-k)` over nonzero integers
vanishes, since the terms at `d` and `-d` cancel. -/
theorem tsum_inv_mul_zpow_neg_eq_zero_of_apply_neg_one_eq_neg
    (hχ : χ (-1) = -(-1 : ℂ) ^ k) :
    ∑' d : ℤ, χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) = 0 := by
  have hinv : χ⁻¹ (-1) = -(-1 : ℂ) ^ k := by
    rw [MulChar.inv_apply_eq_inv', hχ]
    rcases neg_one_pow_eq_or ℂ k with h | h <;> simp [h]
  have hodd : ∀ d : ℤ, χ⁻¹ (-d : ℤ) * ((-d : ℤ) : ℂ) ^ (-(k : ℤ)) =
      -(χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ))) := by
    intro d
    have hz : ((-d : ℤ) : ℂ) ^ (-(k : ℤ)) = (-1 : ℂ) ^ k * (d : ℂ) ^ (-(k : ℤ)) := by
      rw [Int.cast_neg, neg_eq_neg_one_mul, mul_zpow, zpow_neg, zpow_natCast, zpow_neg,
        zpow_natCast, ← inv_pow, inv_neg_one]
    have hc : χ⁻¹ (-d : ℤ) = -(-1 : ℂ) ^ k * χ⁻¹ d := by
      rw [Int.cast_neg, neg_eq_neg_one_mul, map_mul, hinv]
    rw [hz, hc]
    rcases neg_one_pow_eq_or ℂ k with h | h <;> rw [h] <;> ring
  have h2 : ∑' d : ℤ, χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) =
      -∑' d : ℤ, χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) := by
    rw [← tsum_neg, ← (Equiv.neg ℤ).tsum_eq]
    exact tsum_congr hodd
  linear_combination h2 / 2

/-- The constant coefficient identity of the normalized Eisenstein series for a character with
`χ (-1) = (-1) ^ k`. -/
private theorem inv_normalization_mul_tsum_eq_generalizedBernoulli_of_apply_neg_one_eq_pow
    (hk : 2 ≤ k) (hχ : χ.IsPrimitive) (hχpar : χ (-1) = (-1 : ℂ) ^ k) :
    (2 * (-2 * π * I) ^ k / (((k - 1).factorial : ℂ) * (N : ℂ) ^ k) *
        gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * ∑' d : ℤ, χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) =
      -χ.generalizedBernoulli k / (2 * (k : ℂ)) := by
  have hprod :=
    DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hχ
    (ZMod.isPrimitive_stdAddChar N)
  rw [ZMod.card, hχpar] at hprod
  have hv : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hτ := DirichletCharacter.gaussSum_ne_zero_of_isPrimitive hv hχ
    (ZMod.isPrimitive_stdAddChar N)
  have hτinv := DirichletCharacter.gaussSum_inv_ne_zero_of_isPrimitive hv hχ
    (ZMod.isPrimitive_stdAddChar N)
  have hf : ((k - 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hA : (-2 * π * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hC : 2 * (-2 * π * I) ^ k / ((k - 1).factorial * (N : ℂ) ^ k) *
      gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA))
      (mul_ne_zero hf (pow_ne_zero _ hv))) hτinv
  rw [inv_mul_eq_iff_eq_mul₀ hC]
  apply mul_left_cancel₀ hτ
  -- TauCeti's gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli evaluates the integer
  -- row sum; the primitive Gauss-sum product and parity then cancel the normalization.
  rw [χ.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli hχ hk]
  have hfac : (k.factorial : ℂ) = (k : ℂ) * (k - 1).factorial := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : k ≠ 0)).symm
  have hpower : (-2 * π * I : ℂ) ^ k * (-1 : ℂ) ^ k = (2 * π * I) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  have hpowv : (N : ℂ) ^ k = (N : ℂ) ^ (k - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  -- The Gauss product and the parity sign cancel the normalization factor.
  symm
  calc
    _ = (2 * (-2 * π * I) ^ k / ((k - 1).factorial * (N : ℂ) ^ k) *
        (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar)) *
          (-χ.generalizedBernoulli k / (2 * (k : ℂ))) := by ring
    _ = _ := by
      rw [hprod, hfac, hpowv]
      have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
      linear_combination -χ.generalizedBernoulli k * hpower

/-- The constant coefficient identity of the normalized Eisenstein series: for a primitive
character `χ` and `2 ≤ k`, the normalization of the Eisenstein series cancels against the Gauss
sum and the `L`-value, leaving `-Bₖ,χ / (2k)`. When `χ (-1) ≠ (-1) ᵏ` both sides vanish. -/
theorem inv_normalization_mul_tsum_eq_generalizedBernoulli
    (hk : 2 ≤ k) (hχ : χ.IsPrimitive) :
    (2 * (-2 * π * I) ^ k / (((k - 1).factorial : ℂ) * (N : ℂ) ^ k) *
        gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ * ∑' d : ℤ, χ⁻¹ d * (d : ℂ) ^ (-(k : ℤ)) =
      -χ.generalizedBernoulli k / (2 * (k : ℂ)) := by
  by_cases hχpar : χ (-1) = (-1 : ℂ) ^ k
  · exact inv_normalization_mul_tsum_eq_generalizedBernoulli_of_apply_neg_one_eq_pow χ hk hχ hχpar
  · have hneg : χ (-1) = -(-1 : ℂ) ^ k := by
      rcases χ.even_or_odd with he | ho
      · rw [he] at hχpar ⊢
        rcases neg_one_pow_eq_or ℂ k with h | h <;> simp_all
      · rw [ho] at hχpar ⊢
        rcases neg_one_pow_eq_or ℂ k with h | h <;> simp_all
    rw [tsum_inv_mul_zpow_neg_eq_zero_of_apply_neg_one_eq_neg χ hneg,
      generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg (Or.inl (by omega)) hneg]
    simp

end DirichletCharacter
