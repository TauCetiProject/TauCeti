/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.NumberTheory.ArithmeticStatistics.MonicWeightedBox.Basic
public import TauCeti.NumberTheory.SquareDivisorTail
import Mathlib.Analysis.PSeries
import TauCeti.Data.Int.CardIntervalMod
import TauCeti.Data.Int.Interval
import TauCeti.RingTheory.Polynomial.Monic.OfCoeff

/-!
# Square-divisor tails of monic quadratics

The monic quadratics `x^2 + a x + b` in the weighted box `TauCeti.monicWeightedBox 2 X` have
`|a| < X` and `|b| < X^2`, and discriminant `a^2 - 4 b`. Summing, over this box, the number of
squarefree `m > M` with `m^2` dividing a nonzero discriminant gives at most
`90 X^3 / (M + 1) + 12 X^2` for `X ≥ 1`
(`TauCeti.sum_squareDivisorMultiplicity_monicWeightedBox_two_le`). In particular at most that many
quadratics in the box have a nonzero discriminant divisible by `m^2` for some squarefree `m > M`
(`TauCeti.ncard_monicWeightedBox_two_inter_squareDivisorTail_le`).

Both moduli whose square divides the discriminant strongly or only weakly at every prime factor
are counted, so the bound covers the degree-two case of the weak tail of Bhargava, Shankar and
Wang, *Squarefree values of polynomial discriminants I*, Invent. Math. 228 (2022), Theorem 1.5(b)
and Theorem 4.4. Its exponents `3` and `2` beat the `X^(3 + ε) / M + X^(14/5 + ε)` stated there.

The argument is elementary. A discriminant in the box has absolute value below `5 X^2`
(`TauCeti.abs_discr_lt_of_mem_monicWeightedBox_two`), so every counted `m` is at most `⌈3 X⌉`.
A monic quadratic is determined by `(a, b)` (`TauCeti.Polynomial.monicOfCoeff_coeff`), and its
discriminant is `discrim 1 a b`. For fixed `a` and `m`, the map `b ↦ a^2 - 4 b` is injective, and
its values in an interval of length `8 X^2` divisible by `m^2` number at most `15 X^2 / m^2 + 1`.
Summing over `m > M` with `∑_{m > M} m⁻² ≤ 2 / (M + 1)` and over the `3 X` values of `a` gives the
bound.
-/

public section

open Finset Polynomial

namespace TauCeti

variable {X : ℝ}

/-- A monic quadratic `x^2 + a x + b` with `|a| < X` and `|b| < X^2` has discriminant of absolute
value less than `5 X^2`. -/
theorem abs_discr_lt_of_mem_monicWeightedBox_two {f : ℤ[X]} (hf : f ∈ monicWeightedBox 2 X) :
    |(f.discr : ℝ)| < 5 * X ^ 2 := by
  obtain ⟨hm, hd, hc⟩ := mem_monicWeightedBox.mp hf
  have h2 : f.coeff 2 = 1 := hd ▸ hm.coeff_natDegree
  have h₁ : |(f.coeff 1 : ℝ)| < X := by simpa using hc 1 one_lt_two
  have h₀ : |(f.coeff 0 : ℝ)| < X ^ 2 := by simpa using hc 0 two_pos
  have hsq : (f.coeff 1 : ℝ) ^ 2 < X ^ 2 := by
    rw [← sq_abs]
    exact pow_lt_pow_left₀ h₁ (abs_nonneg _) two_ne_zero
  have habs :
      |(f.coeff 1 : ℝ) ^ 2 - 4 * f.coeff 0| ≤ (f.coeff 1 : ℝ) ^ 2 + 4 * |(f.coeff 0 : ℝ)| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos four_pos]
  rw [discr_of_degree_eq_two ((degree_eq_iff_natDegree_eq hm.ne_zero).mpr hd), h2, mul_one]
  push_cast
  linarith

/-- The pairs `(a, b)` with `|a| < X` and `|b| < X^2`, counted with the `m ∈ (M, ⌈3 X⌉]` such that
`m^2 ∣ a^2 - 4 b`, number at most `90 X^3 / (M + 1) + 12 X^2`. -/
private theorem sum_card_filter_sq_dvd_discrim_le (M : ℕ) (hX : 1 ≤ X) :
    ∑ p ∈ Ioo (-⌈X⌉) ⌈X⌉ ×ˢ Ioo (-⌈X ^ 2⌉) ⌈X ^ 2⌉,
      (#{m ∈ Ioc M ⌈3 * X⌉₊ | ((m : ℕ) : ℤ) ^ 2 ∣ discrim 1 p.1 p.2} : ℝ) ≤
        90 * X ^ 3 / (M + 1) + 12 * X ^ 2 := by
  set A := Ioo (-⌈X⌉) ⌈X⌉
  set B := Ioo (-⌈X ^ 2⌉) ⌈X ^ 2⌉
  set N := ⌈3 * X⌉₊
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hA : (#A : ℝ) ≤ 3 * X := by
    rw [← Set.ncard_coe_finset, ← setOf_abs_intCast_lt_eq_Ioo]
    exact ncard_setOf_abs_intCast_lt_le hX
  have hN : (#(Ioc M N) : ℝ) ≤ 4 * X := by
    rw [Nat.card_Ioc]
    have h3X : 0 ≤ 3 * X := by linarith
    have := Nat.ceil_lt_add_one h3X
    have : ((N - M : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
    linarith
  have hinv : ∑ m ∈ Ioc M N, ((m : ℝ) ^ 2)⁻¹ ≤ 2 / (M + 1) :=
    (sum_le_sum_of_subset_of_nonneg (fun m hm ↦ by simp only [mem_Ioc, mem_Ioo] at hm ⊢; omega)
      fun _ _ _ ↦ by positivity).trans (sum_Ioo_inv_sq_le M (N + 1))
  -- For fixed `a` and `m > 0`, at most `15 X^2 / m^2 + 1` values of `b` are admissible.
  have hfib (a : ℤ) {m : ℕ} (hm : 0 < m) :
      (#{b ∈ B | ((m : ℤ) ^ 2) ∣ discrim 1 a b} : ℝ) ≤ 15 * X ^ 2 * ((m : ℝ) ^ 2)⁻¹ + 1 := by
    have hc : (1 : ℤ) ≤ ⌈X ^ 2⌉ := Int.one_le_ceil_iff.mpr (by linarith)
    have hq : (0 : ℤ) < (m : ℤ) ^ 2 := by positivity
    have h := Int.card_Ioo_filter_dvd_sub_mul_le (a ^ 2) four_pos hq hc
    have h' : (#{b ∈ B | ((m : ℤ) ^ 2) ∣ discrim 1 a b} : ℝ) ≤
        (2 * 4 * ⌈X ^ 2⌉ - 1) / (m : ℝ) ^ 2 + 1 := by
      simp only [discrim, mul_one]
      exact_mod_cast h
    refine h'.trans ?_
    have := Int.ceil_lt_add_one (X ^ 2)
    rw [div_eq_mul_inv]
    gcongr
    linarith
  calc ∑ p ∈ A ×ˢ B, (#{m ∈ Ioc M N | ((m : ℕ) : ℤ) ^ 2 ∣ discrim 1 p.1 p.2} : ℝ)
      = ∑ m ∈ Ioc M N, ∑ a ∈ A, (#{b ∈ B | ((m : ℤ) ^ 2) ∣ discrim 1 a b} : ℝ) := by
        simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        rw [sum_comm]
        exact sum_congr rfl fun m _ ↦ sum_product _ _ _
    _ ≤ ∑ m ∈ Ioc M N, ∑ _a ∈ A, (15 * X ^ 2 * ((m : ℝ) ^ 2)⁻¹ + 1) :=
        sum_le_sum fun m hm ↦ sum_le_sum fun a _ ↦ hfib a (by simp only [mem_Ioc] at hm; omega)
    _ = #A * (15 * X ^ 2 * ∑ m ∈ Ioc M N, ((m : ℝ) ^ 2)⁻¹ + #(Ioc M N)) := by
        simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum]
        ring
    _ ≤ 3 * X * (15 * X ^ 2 * (2 / (M + 1)) + 4 * X) := by
        gcongr
    _ = 90 * X ^ 3 / (M + 1) + 12 * X ^ 2 := by ring

/-- Over the monic quadratics `x^2 + a x + b` with `|a| < X` and `|b| < X^2`, the number of
squarefree `m > M` with `m^2` dividing a nonzero discriminant sums to at most
`90 X^3 / (M + 1) + 12 X^2`, for `X ≥ 1`. -/
theorem sum_squareDivisorMultiplicity_monicWeightedBox_two_le (M : ℕ) (hX : 1 ≤ X) :
    ∑ f ∈ (finite_monicWeightedBox 2 X).toFinset, (squareDivisorMultiplicity discr M f : ℝ) ≤
      90 * X ^ 3 / (M + 1) + 12 * X ^ 2 := by
  set S := (finite_monicWeightedBox 2 X).toFinset
  set N := ⌈3 * X⌉₊
  have hS : ∀ f ∈ S, f ∈ monicWeightedBox 2 X := fun f hf ↦ (Set.Finite.mem_toFinset _).mp hf
  -- Every counted modulus is at most `⌈3 X⌉`, since `|discr f| < 5 X^2 ≤ ⌈3 X⌉^2`.
  have hN (f : ℤ[X]) (hf : f ∈ S) : f.discr.natAbs ≤ N ^ 2 := by
    have h3X : 3 * X ≤ N := Nat.le_ceil _
    have : (f.discr.natAbs : ℝ) ≤ (N : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      nlinarith [abs_discr_lt_of_mem_monicWeightedBox_two (hS f hf)]
    exact_mod_cast this
  have hdiscr (f : ℤ[X]) (hf : f ∈ S) : f.discr = discrim 1 (f.coeff 1) (f.coeff 0) := by
    obtain ⟨hm, hd, -⟩ := mem_monicWeightedBox.mp (hS f hf)
    have h2 : f.coeff 2 = 1 := hd ▸ hm.coeff_natDegree
    rw [discr_of_degree_eq_two ((degree_eq_iff_natDegree_eq hm.ne_zero).mpr hd), discrim, h2]
    ring
  calc ∑ f ∈ S, (squareDivisorMultiplicity discr M f : ℝ)
      ≤ ∑ f ∈ S, (#{m ∈ Ioc M N | ((m : ℕ) : ℤ) ^ 2 ∣ f.discr} : ℝ) :=
        sum_le_sum fun f hf ↦ Nat.cast_le.mpr (squareDivisorMultiplicity_le_card_Ioc (hN f hf))
    _ = ∑ p ∈ S.image fun f : ℤ[X] ↦ (f.coeff 1, f.coeff 0),
          (#{m ∈ Ioc M N | ((m : ℕ) : ℤ) ^ 2 ∣ discrim 1 p.1 p.2} : ℝ) := by
        rw [sum_image]
        · exact sum_congr rfl fun f hf ↦ by rw [hdiscr f hf]
        -- A monic quadratic is determined by its two lower coefficients.
        intro f hf g hg h
        obtain ⟨hfm, hfd, -⟩ := mem_monicWeightedBox.mp (hS f hf)
        obtain ⟨hgm, hgd, -⟩ := mem_monicWeightedBox.mp (hS g hg)
        rw [Prod.mk.injEq] at h
        rw [← Polynomial.monicOfCoeff_coeff hfm hfd, ← Polynomial.monicOfCoeff_coeff hgm hgd]
        congr 1
        ext i
        fin_cases i
        exacts [h.2, h.1]
    _ ≤ ∑ p ∈ Ioo (-⌈X⌉) ⌈X⌉ ×ˢ Ioo (-⌈X ^ 2⌉) ⌈X ^ 2⌉,
          (#{m ∈ Ioc M N | ((m : ℕ) : ℤ) ^ 2 ∣ discrim 1 p.1 p.2} : ℝ) := by
        refine sum_le_sum_of_subset_of_nonneg (fun p hp ↦ ?_) fun _ _ _ ↦ by positivity
        obtain ⟨f, hf, rfl⟩ := mem_image.mp hp
        obtain ⟨-, -, hc⟩ := mem_monicWeightedBox.mp (hS f hf)
        have h₁ := hc 1 one_lt_two
        have h₀ := hc 0 two_pos
        rw [mem_product, mem_Ioo_neg_ceil_ceil_iff, mem_Ioo_neg_ceil_ceil_iff]
        exact ⟨by simpa using h₁, by simpa using h₀⟩
    _ ≤ 90 * X ^ 3 / (M + 1) + 12 * X ^ 2 := sum_card_filter_sq_dvd_discrim_le M hX

/-- At most `90 X^3 / (M + 1) + 12 X^2` monic quadratics `x^2 + a x + b` with `|a| < X` and
`|b| < X^2` have a nonzero discriminant divisible by `m^2` for some squarefree `m > M`,
for `X ≥ 1`. -/
theorem ncard_monicWeightedBox_two_inter_squareDivisorTail_le (M : ℕ) (hX : 1 ≤ X) :
    ((monicWeightedBox 2 X ∩ squareDivisorTail discr M).ncard : ℝ) ≤
      90 * X ^ 3 / (M + 1) + 12 * X ^ 2 := by
  have h := ncard_inter_squareDivisorTail_le_sum (finite_monicWeightedBox 2 X).toFinset discr M
  rw [Set.Finite.coe_toFinset] at h
  exact (Nat.cast_le.mpr h).trans (by
    simpa only [Nat.cast_sum] using sum_squareDivisorMultiplicity_monicWeightedBox_two_le M hX)

end TauCeti
