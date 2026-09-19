/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` of a number field `K` of degree `d = [K : ℚ]`, the partial sums
`∑_{N(I) ≤ x} χ(I)` over the nonzero integral ideals are trivially `O(x)`, by the linear ideal
count. For nontrivial finite-order ray class characters, equidistribution among ray classes gives
the stronger bound `O(x ^ (1 - 1 / d))`. This file names that bound as a hypothesis and extracts
its analytic consequence.

* `TauCeti.HasCancellation χ` is the uniform bound
  `‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / d)` for every real cutoff `x ≥ 1`, with the inclusive
  summatory function `TauCeti.idealSummatory`.
  Equivalently (`TauCeti.hasCancellation_iff_isBigO`), the partial sums are
  `O(x ^ (1 - 1 / d))` as `x → ∞`.
* `TauCeti.continuedLFunctionOfWeight χ` is the partial-summation integral
  `s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

It agrees with the norm-regrouped L-series of `χ` on `Re s > 1` for *every* unitary weight
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`), and under `HasCancellation χ` it is holomorphic
on `Re s > 1 - 1 / d` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`); so it is an analytic
continuation of the L-series of `χ` across the line `Re s = 1`.

Cancellation is a hypothesis about the partial sums themselves. It cannot be replaced by
finiteness of the image of `χ` or of a quotient through which it factors: the values of a weight
factoring through a finite quotient of the free group on the prime ideals can be prescribed
arbitrarily prime by prime. The trivial weight shows that the hypothesis is not automatic:
its partial sums are the ideal counts, which grow linearly, and it fails `HasCancellation`
(`TauCeti.not_hasCancellation_one`); correspondingly its L-series is the Dedekind zeta function,
which has a pole at `s = 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII §6, for the partial-sum bound of finite-order
  ray class character L-series.
-/

public section

namespace TauCeti

open Filter Asymptotics
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Cancellation in the ideal partial sums of a unitary weight.** There is a constant `C` with
`‖∑_{N(I) ≤ x} χ(I)‖ ≤ C * x ^ (1 - 1 / [K : ℚ])` for every real cutoff `x ≥ 1`, the sum running
over the nonzero integral ideals of absolute norm at most `x`. -/
def HasCancellation (χ : UnitaryIdealWeight K) : Prop :=
  ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
    ‖idealSummatory K χ.toIdealArithmeticFunction x‖ ≤
      C * x ^ (1 - 1 / (Module.finrank ℚ K : ℝ))

/-- The cancellation exponent `1 - 1 / [K : ℚ]` is less than `1`. -/
theorem cancellationExponent_lt_one : 1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
  have h : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  linarith [one_div_pos.mpr h]

/-- **Cancellation is an asymptotic bound.** A weight has cancellation exactly when its ideal
partial sums are `O(x ^ (1 - 1 / [K : ℚ]))` as `x → ∞`: on any bounded range of cutoffs `x ≥ 1`
the partial sums are bounded by an ideal count, so the eventual bound is uniform. -/
theorem hasCancellation_iff_isBigO {χ : UnitaryIdealWeight K} :
    HasCancellation χ ↔
      (fun x : ℝ ↦ idealSummatory K χ.toIdealArithmeticFunction x) =O[atTop]
        fun x : ℝ ↦ x ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  set θ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  constructor
  · rintro ⟨C, hC⟩
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hC x hx
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hc
    have hθ : 0 ≤ θ := by
      have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
      exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hd)).mpr hd)
    set M : ℝ := ∑ k ∈ Finset.Icc 1 ⌊x₀⌋₊, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖
    have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    refine ⟨max c M, fun x hx ↦ ?_⟩
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ
    rcases le_total x₀ x with hx₀x | hxx₀
    · have hbound := hx₀ x hx₀x
      rw [Real.norm_of_nonneg (by positivity)] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · calc ‖idealSummatory K χ.toIdealArithmeticFunction x‖
          ≤ ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, ‖normCoeff K χ.toIdealArithmeticFunction k‖ := by
            rw [idealSummatory_eq_sum_Icc_normCoeff]
            exact norm_sum_le _ _
        _ ≤ M := (Finset.sum_le_sum fun k _ ↦
              UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k).trans
            (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.Icc_subset_Icc_right (Nat.floor_mono hxx₀)) fun _ _ _ ↦ norm_nonneg _)
        _ ≤ max c M * x ^ θ :=
            (le_max_right c M).trans (le_mul_of_one_le_right (hM.trans (le_max_right c M)) hxθ)

/-- A weight has cancellation exactly when its complex conjugate does: conjugation commutes with
the finite partial sums and preserves their modulus. -/
@[simp]
theorem hasCancellation_conj_iff {χ : UnitaryIdealWeight K} :
    HasCancellation χ.conj ↔ HasCancellation χ := by
  have h (x : ℝ) : ‖idealSummatory K χ.conj.toIdealArithmeticFunction x‖ =
      ‖idealSummatory K χ.toIdealArithmeticFunction x‖ := by
    simp only [idealSummatory_apply, UnitaryIdealWeight.toIdealArithmeticFunction_apply,
      UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply, ← map_sum,
      Complex.norm_conj]
  simp only [HasCancellation, h]

/-- **Cancellation bounds the partial sums of the norm coefficients**, in the `O(n ^ r)` form of
Mathlib's `LSeries_eq_mul_integral`. -/
theorem HasCancellation.isBigO_sum_normCoeff {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC⟩ := hχ
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← Nat.floor_natCast (R := ℝ) n, ← idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_natCast,
    Real.norm_of_nonneg (by positivity)]
  exact hC n (by exact_mod_cast hn)

/-- **The trivial weight has no cancellation.** Its partial sums are the ideal counts, which are
bounded below by a positive multiple of `x`, while `x ^ (1 - 1 / [K : ℚ]) = o(x)`. -/
theorem not_hasCancellation_one : ¬ HasCancellation (1 : UnitaryIdealWeight K) := by
  rw [HasCancellation]
  rintro ⟨C, hC⟩
  obtain ⟨b⟩ := idealCount_linearBounds K
  set θ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ)
  have hθ : 0 < 1 - θ := sub_pos.mpr cancellationExponent_lt_one
  obtain ⟨x, hx⟩ := ((tendsto_rpow_atTop hθ).eventually_gt_atTop (C / b.lower)).and
    (eventually_ge_atTop (1 : ℝ)) |>.exists
  have hxpos : 0 < x := zero_lt_one.trans_le hx.2
  have hsum : ‖idealSummatory K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction x‖ =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := by
    rw [UnitaryIdealWeight.toIdealArithmeticFunction_one, idealSummatory_apply,
      Nat.card_coe_normLE]
    simp
  have hle : b.lower * x ≤ C * x ^ θ := (b.le_card x hx.2).trans (hsum ▸ hC x hx.2)
  have hsplit : b.lower * x ^ (1 - θ) * x ^ θ ≤ C * x ^ θ := by
    rwa [mul_assoc, ← Real.rpow_add hxpos, sub_add_cancel, Real.rpow_one]
  exact absurd ((div_lt_iff₀' b.lower_pos).mp hx.1)
    (not_lt.mpr (le_of_mul_le_mul_right hsplit (Real.rpow_pos_of_pos hxpos θ)))

/-- **The continued L-function of a unitary weight**, defined by partial summation:
`s * ∫_{1}^{∞} (∑_{N(I) ≤ t} χ(I)) t ^ (-(s + 1)) dt`.

On `Re s > 1` it is the norm-regrouped L-series of `χ`
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`); under `TauCeti.HasCancellation χ` it is
holomorphic on `Re s > 1 - 1 / [K : ℚ]` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`).
Where the integral does not converge it takes the junk value of Mathlib's Bochner integral. -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ),
    idealSummatory K χ.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1))

/-- The continued L-function as the integral of Mathlib's `LSeries_eq_mul_integral`, over the
partial sums of the norm coefficients. -/
theorem continuedLFunctionOfWeight_eq_mul_integral (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, normCoeff K χ.toIdealArithmeticFunction k) *
        (t : ℂ) ^ (-(s + 1)) := by
  simp only [continuedLFunctionOfWeight, idealSummatory_eq_sum_Icc_normCoeff]

/-- **The continued L-function is the L-series on `Re s > 1`.** For every unitary weight, with or
without cancellation, `continuedLFunctionOfWeight χ` agrees with the `LSeries` of the norm
coefficients of `χ` to the right of `1`, where that series converges absolutely. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [continuedLFunctionOfWeight_eq_mul_integral]
  refine (LSeries_eq_mul_integral' _ zero_le_one (by simpa using hs) ?_).symm
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)).trans
    (isBigO_sum_norm_normCoeff_one K)
  rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
  exact Finset.sum_le_sum fun k _ ↦
    UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K χ k

/-- **Cancellation continues the L-series of a weight.** If `χ` has cancellation, its continued
L-function is holomorphic on the half-plane `Re s > 1 - 1 / [K : ℚ]`, which contains the line
`Re s = 1`. -/
theorem differentiableOn_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re} := by
  rw [funext (continuedLFunctionOfWeight_eq_mul_integral χ)]
  exact LSeries.differentiableOn_mul_integral_of_isBigO _ hχ.isBigO_sum_normCoeff

end TauCeti
