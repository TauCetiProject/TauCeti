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

/-!
# Generalized Bernoulli numbers and primitive character sums

The integer-indexed critical-value sum of a primitive Dirichlet character is evaluated using
its Gauss sum and its generalized Bernoulli number. The formula includes both parities and
modulus one: the integer sum is zero when the character and weight have opposite parities.

The proof applies Mathlib's Fourier expansion
`hasSum_one_div_pow_mul_fourier_mul_bernoulliFun` to each residue and uses
`DirichletCharacter.gaussSum_mulShift_of_isPrimitive` for the finite character sum.
These special values give the constant coefficients of normalized Eisenstein series.

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
  -- Apply the Bernoulli Fourier expansion at each residue, using its value in [0, 1).
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
  -- The finite Fourier coefficient is the shifted Gauss sum, also at nonunit frequencies.
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

end DirichletCharacter
