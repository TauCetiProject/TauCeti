/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.Fourier.ExponentialAbs
public import TauCeti.Analysis.Fourier.HaagerupZsido.Defs

/-!
# Lattice sums and Poisson summation for the Cauchy kernel

This file evaluates the two-sided geometric lattice sum, the Poisson-summation
identity relating the two-sided exponential to the Cauchy lattice, and the
half-lattice and odd-pole Cauchy sums that expose the hyperbolic weight.

This is a topic split of `ForTauCeti/Analysis/Fourier/HaagerupZsidoKernel.lean`;
declarations are moved verbatim and remain in the `TauCeti.HaagerupZsido`
namespace.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti` at Davis--Kahan
  commit `f35ffc0`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti
namespace HaagerupZsido

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- The positive tail of the geometric exponential series. -/
private theorem tsum_nat_exp_neg_mul_add_one {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
      Real.exp (-a) / (1 - Real.exp (-a)) := by
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  calc
    (∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ))) =
        ∑' n : ℕ, q ^ (n + 1) := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ = ∑' n : ℕ, q ^ n * q := by simp_rw [pow_succ]
    _ = (∑' n : ℕ, q ^ n) * q := tsum_mul_right
    _ = (1 - q)⁻¹ * q := by rw [tsum_geometric_of_norm_lt_one hqnorm]
    _ = Real.exp (-a) / (1 - Real.exp (-a)) := by
      simp only [q, div_eq_mul_inv]
      ring

/-- The elementary two-sided geometric lattice sum. -/
private theorem tsum_int_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-a * |(n : ℝ)|)) =
      (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
  let f : ℤ → ℝ := fun n => Real.exp (-a * |(n : ℝ)|)
  let q := Real.exp (-a)
  have hqpos : 0 < q := Real.exp_pos _
  have hqlt : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hqpos]
    exact hqlt
  have hgeo : Summable (fun n : ℕ => q ^ n) :=
    (hasSum_geometric_of_norm_lt_one hqnorm).summable
  have hsum : Summable f := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun n => ?_
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change q ^ n = Real.exp (-a * |(((n : ℕ) : ℤ) : ℝ)|)
      rw [show |(((n : ℕ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    · refine hgeo.congr fun n => ?_
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change q ^ n = Real.exp (-a * |((-(n : ℤ) : ℤ) : ℝ)|)
      rw [show |((-(n : ℤ) : ℤ) : ℝ)| = (n : ℝ) by simp]
      simp only [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
  have heven : Function.Even f := by
    intro n
    simp only [f, Int.cast_neg, abs_neg]
  have hpnat :
      (∑' n : ℕ+, f (n : ℤ)) =
        ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
    calc
      (∑' n : ℕ+, f (n : ℤ)) = ∑' n : ℕ, f (Nat.succPNat n : ℤ) :=
        (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f (n : ℤ))).symm
      _ = ∑' n : ℕ, Real.exp (-a * (n + 1 : ℕ)) := by
        apply tsum_congr
        intro n
        dsimp only [f, Nat.succPNat]
        rw [abs_of_nonneg]
        · congr 1
        · positivity
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ∑' n : ℤ, f n = _
  calc
    (∑' n : ℤ, f n) = f 0 + 2 • ∑' n : ℕ+, f (n : ℤ) :=
      tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum
    _ = 1 + 2 * (Real.exp (-a) / (1 - Real.exp (-a))) := by
      rw [hpnat, tsum_nat_exp_neg_mul_add_one ha]
      simp [f]
    _ = (1 + Real.exp (-a)) / (1 - Real.exp (-a)) := by
      have hne : 1 - Real.exp (-a) ≠ 0 := by
        have : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
        linarith
      field_simp [hne]
      ring

/-- Poisson summation for the two-sided exponential, before evaluating its
geometric side. -/
private theorem poisson_exponential_eq_cauchy_lattice
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ,
        Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
      ∑' n : ℤ,
        ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t =>
    Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (cexp_neg_mul_abs_isLittleO_rpow_cocompact hscale (-2)).isBigO
  have hFourier : 𝓕 f = fun x : ℝ =>
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
    funext x
    exact fourier_cexp_neg_two_pi_mul_abs x hy
  have hFourierDecay : (𝓕 f) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [hFourier]
    exact cauchy_fourier_isBigO_rpow_neg_two hy
  have hPoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hfContinuous (by norm_num : (1 : ℝ) < 2) hfDecay hFourierDecay 0
  simpa only [f, zero_add, hFourier, Int.cast_zero, QuotientAddGroup.mk_zero,
    fourier_eval_zero, mul_one] using hPoisson

/-- The Cauchy lattice sum, written in exponential rather than hyperbolic
notation. -/
private theorem tsum_int_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) := by
  let q : ℝ := Real.exp (-(2 * Real.pi * y))
  let Q : ℝ := (1 + q) / (1 - q)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hexpReal :
      (∑' n : ℤ, Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) = Q := by
    simpa only [Q, q, neg_mul] using tsum_int_exp_neg_mul_abs hscale
  have hexpComplex :
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
        (Q : ℂ) := by
    calc
      (∑' n : ℤ,
          Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
          ∑' n : ℤ, (Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|) : ℂ) := by
        apply tsum_congr
        intro n
        rw [Complex.ofReal_exp]
        congr 1
        norm_cast
        ring
      _ = (((∑' n : ℤ,
          Real.exp (-(2 * Real.pi * y) * |(n : ℝ)|)) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum _).symm
      _ = (Q : ℂ) := by rw [hexpReal]
  have hPoisson := poisson_exponential_eq_cauchy_lattice hy
  have hscaled :
      (Q : ℂ) = ((y / Real.pi : ℝ) : ℂ) *
        ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
    calc
      (Q : ℂ) = ∑' n : ℤ,
          ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
        rw [← hPoisson, hexpComplex]
      _ = ∑' n : ℤ, ((y / Real.pi : ℝ) : ℂ) *
          (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := by
        apply tsum_congr
        intro n
        norm_cast
        have hden : y ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (n : ℝ)]
        field_simp [Real.pi_ne_zero, hden]
      _ = ((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) := tsum_mul_left
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  calc
    (∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) =
        (((Real.pi / y : ℝ) : ℂ) * (((y / Real.pi : ℝ) : ℂ) *
          ∑' n : ℤ, (((y ^ 2 + (n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ))) := by
      push_cast
      field_simp [Real.pi_ne_zero, hy.ne']
    _ = (((Real.pi / y : ℝ) : ℂ) * (Q : ℂ)) := by rw [← hscaled]
    _ = (((Real.pi / y) * Q : ℝ) : ℂ) := by push_cast; rfl
    _ = (((Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ) := rfl

/-- The natural-number Cauchy series is summable, uniformly with respect to
the harmless nonnegative square added to its denominator. -/
private theorem summable_nat_inv_sq_add_sq (y : ℝ) :
    Summable (fun n : ℕ => (y ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
  have hmajor : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h := Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  have htail : Summable (fun n : ℕ =>
      (y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · intro n
      have hbase : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
      have hden : 0 < y ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      exact (inv_le_inv₀ hden hbase).2 (by nlinarith [sq_nonneg y])
    · exact hmajor
  apply (summable_nat_add_iff 1).mp
  exact htail

/-- The half-lattice version of the Cauchy sum. -/
private theorem tsum_nat_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (1 / 2) *
        ((Real.pi / y) *
          ((1 + Real.exp (-(2 * Real.pi * y))) /
            (1 - Real.exp (-(2 * Real.pi * y)))) + y⁻¹ ^ 2) := by
  let fNat : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  let fInt : ℤ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hNat : Summable fNat := summable_nat_inv_sq_add_sq y
  have hpos : Summable (fun n : ℕ => fInt (n + 1)) := by
    have := (summable_nat_add_iff 1).mpr hNat
    simpa only [fNat, fInt, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using this
  have hneg : Summable (fun n : ℕ => fInt (-(n + 1))) := by
    simpa only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      neg_sq] using hpos
  have hIntSplit := tsum_of_add_one_of_neg_add_one hpos hneg
  have hNatSplit := hNat.tsum_eq_zero_add
  have hLattice := tsum_int_inv_sq_add_sq hy
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change ∑' n : ℕ, fNat n = _
  simp only [fInt, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Int.cast_zero, neg_sq] at hIntSplit
  simp only [fNat, Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hNatSplit
  have hzero : (y ^ 2 + (0 : ℝ) ^ 2)⁻¹ = y⁻¹ ^ 2 := by simp [inv_pow]
  rw [hzero] at hIntSplit hNatSplit
  nlinarith

/-- The positive odd part of the Cauchy lattice. -/
private theorem tsum_odd_inv_sq_add_sq
    {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹) =
      (Real.pi / (4 * y)) * weight y := by
  let f : ℕ → ℝ := fun n => (y ^ 2 + (n : ℝ) ^ 2)⁻¹
  have hAll : Summable f := summable_nat_inv_sq_add_sq y
  have hmul : Function.Injective (fun n : ℕ => 2 * n) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have hEven := hAll.comp_injective hmul
  have hOdd := hAll.comp_injective ((add_left_injective 1).comp hmul)
  have hSplit := (hEven.hasSum.even_add_odd hOdd.hasSum).tsum_eq
  simp only [Function.comp_apply] at hSplit
  have hEvenScale :
      (∑' n : ℕ, f (2 * n)) =
        (1 / 4 : ℝ) * ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [f]
    have hdenLeft : y ^ 2 + ((2 * n : ℕ) : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (((2 * n : ℕ) : ℝ))]
    have hdenRight : (y / 2) ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg (n : ℝ)]
    field_simp [hdenLeft, hdenRight]
    norm_num
    ring
  have hOddEq :
      (∑' n : ℕ, f (2 * n + 1)) =
        (∑' n : ℕ, f n) - (1 / 4 : ℝ) *
          ∑' n : ℕ, ((y / 2) ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    rw [← hEvenScale]
    linarith [hSplit]
  have hAllValue := tsum_nat_inv_sq_add_sq hy
  have hHalfValue := tsum_nat_inv_sq_add_sq (show 0 < y / 2 by positivity)
  rw [hAllValue, hHalfValue] at hOddEq
  let r : ℝ := Real.exp (-(Real.pi * y))
  have hrpos : 0 < r := Real.exp_pos _
  have hrlt : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hFullExp : Real.exp (-(2 * Real.pi * y)) = r ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hHalfExp : Real.exp (-(2 * Real.pi * (y / 2))) = r := by
    dsimp only [r]
    congr 1
    ring
  have hInvHalf : (y / 2)⁻¹ ^ 2 = 4 * y⁻¹ ^ 2 := by
    field_simp [hy.ne']
    ring
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (∑' n : ℕ, f (2 * n + 1)) = _
  calc
    (∑' n : ℕ, f (2 * n + 1)) =
        (1 / 2) *
            ((Real.pi / y) * ((1 + r ^ 2) / (1 - r ^ 2)) + y⁻¹ ^ 2) -
          (1 / 4) * ((1 / 2) *
            ((Real.pi / (y / 2)) * ((1 + r) / (1 - r)) +
              (y / 2)⁻¹ ^ 2)) := by
      simpa only [hFullExp, hHalfExp] using hOddEq
    _ = (Real.pi / (4 * y)) * weight y := by
      rw [weight_eq_exp_quotient, show Real.exp (-(Real.pi * y)) = r by rfl,
        hInvHalf]
      have hOneSub : 1 - r ≠ 0 := by linarith
      have hOneAdd : 1 + r ≠ 0 := by positivity
      have hSq : 1 - r ^ 2 ≠ 0 := by nlinarith
      field_simp [hy.ne', hOneSub, hOneAdd, hSq]
      ring

/-- Odd-pole partial-fraction expansion of the hyperbolic weight. -/
theorem weight_div_eq_tsum_odd
    {y : ℝ} (hy : 0 < y) :
    weight y / y =
      (4 / Real.pi) *
        ∑' n : ℕ, (y ^ 2 + (((2 * n + 1 : ℕ) : ℝ) ^ 2))⁻¹ := by
  rw [tsum_odd_inv_sq_add_sq hy]
  field_simp [Real.pi_ne_zero, hy.ne']

end

end HaagerupZsido
end TauCeti
