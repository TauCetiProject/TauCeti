/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.LSeries.SumCoeff

/-!
# Cancellation in ideal partial sums and the continued L-function of a weight

For a unitary ideal weight `χ` on a number field `K` of degree `d = [K : ℚ]`, the ideal partial
sums `A_χ(x) = ∑_{N(I) ≤ x} χ(I)` are at most the number of ideals of norm at most `x`, hence
`O(x)`.  For a nontrivial finite-order Hecke character the classical ideal-counting estimate
in a class gives the stronger bound `A_χ(x) = O(x ^ (1 - 1/d))`; it is not proved here.
This file names that estimate and draws its analytic consequence.

* `TauCeti.UnitaryIdealWeight.HasCancellation χ` is the bound
  `A_χ(x) = O(x ^ (1 - 1/d))` as `x → ∞`, with the inclusive real cutoff of
  `TauCeti.idealSummatory`.
* `TauCeti.continuedLFunctionOfWeight χ s = s * ∫_1^∞ A_χ(t) t^{-(s+1)} dt` is the partial-sum
  integral of the norm-regrouped Dirichlet series of `χ`.

## Main results

* `TauCeti.continuedLFunctionOfWeight_eq_LSeries`: on `Re s > 1` the continued L-function is the
  `LSeries` of the norm coefficients `TauCeti.normCoeff K χ.toIdealArithmeticFunction`.  This
  needs no cancellation: the trivial `O(x)` bound suffices.
* `TauCeti.differentiableOn_continuedLFunctionOfWeight` and
  `TauCeti.analyticOnNhd_continuedLFunctionOfWeight`: under `HasCancellation`, the continued
  L-function is holomorphic on `Re s > 1 - 1/d`, so it continues the Dirichlet series across
  `Re s = 1`.
* `TauCeti.UnitaryIdealWeight.not_hasCancellation_one`: the trivial weight has no cancellation.
  Its partial sums are the ideal counts, which grow linearly; indeed its series is the Dedekind
  zeta function, which has a pole at `s = 1`.
* `TauCeti.UnitaryIdealWeight.hasCancellation_conj_iff`: cancellation is stable under complex
  conjugation of the weight.

Finiteness of the image of `χ` is not a substitute for `HasCancellation`: the prime values of a
weight factoring through a finite quotient of the ideal group can be arbitrary, and cancellation
comes from the equidistribution of ideals among classes, which is a separate theorem.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1 (partial summation).
* S. Lang, *Algebraic Number Theory*, Chapter VI §3 (the ideal-counting estimate in a class).
-/

public section

open Asymptotics Filter MeasureTheory Set
open scoped nonZeroDivisors NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

namespace UnitaryIdealWeight

variable (χ : UnitaryIdealWeight K)

/-- A unitary ideal weight **has cancellation** if its ideal partial sums
`∑_{N(I) ≤ x} χ(I)` are `O(x ^ (1 - 1/[K : ℚ]))` as `x → ∞`. -/
def HasCancellation : Prop :=
  (fun x : ℝ ↦ idealSummatory K χ.toIdealArithmeticFunction x) =O[atTop]
    fun x : ℝ ↦ x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)

theorem hasCancellation_iff :
    χ.HasCancellation ↔ (fun x : ℝ ↦ idealSummatory K χ.toIdealArithmeticFunction x) =O[atTop]
      fun x : ℝ ↦ x ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) :=
  (Iff.rfl)

/-- The ideal partial sums of the conjugate weight are the conjugates of those of `χ`. -/
@[simp]
theorem idealSummatory_conj (x : ℝ) :
    idealSummatory K χ.conj.toIdealArithmeticFunction x =
      starRingEnd ℂ (idealSummatory K χ.toIdealArithmeticFunction x) := by
  simp [idealSummatory_apply, val_conj, MultiplicativeIdealWeight.conj_apply]

/-- Cancellation is stable under complex conjugation of the weight. -/
@[simp]
theorem hasCancellation_conj_iff : χ.conj.HasCancellation ↔ χ.HasCancellation := by
  rw [hasCancellation_iff, hasCancellation_iff, ← isBigO_norm_left]
  simp_rw [idealSummatory_conj, Complex.norm_conj]
  exact isBigO_norm_left

/-- Each norm coefficient of a unitary weight is bounded in modulus by the number of ideals of
that norm, the norm coefficient of the trivial weight. -/
theorem norm_normCoeff_le_norm_normCoeff_one (n : ℕ) :
    ‖normCoeff K χ.toIdealArithmeticFunction n‖ ≤
      ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ := by
  rw [norm_normCoeff_one, normCoeff_eq_sum_normFiber]
  refine (norm_sum_le _ _).trans ?_
  simpa using Finset.sum_le_card_nsmul _ _ 1 fun I _ ↦ χ.norm_le_one _

/-- **The trivial weight has no cancellation.** Its partial sums count the ideals of norm at most
`x`, which is at least a positive multiple of `x`, while `x ^ (1 - 1/[K : ℚ]) = o(x)`. -/
theorem not_hasCancellation_one : ¬ (1 : UnitaryIdealWeight K).HasCancellation := by
  intro h
  obtain ⟨b⟩ := idealCount_linearBounds K
  obtain ⟨C, hC⟩ := h.bound
  set θ : ℝ := 1 - (Module.finrank ℚ K : ℝ)⁻¹
  have hθ : 0 < 1 - θ := by
    simp only [θ, sub_sub_cancel]
    exact inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  obtain ⟨x, hxC, hx1⟩ := ((((tendsto_rpow_atTop hθ).eventually_gt_atTop (C / b.lower)).and
    hC).and (eventually_ge_atTop 1)).exists
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hcard : ‖idealSummatory K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction x‖ =
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := by
    simp only [toIdealArithmeticFunction_one, idealSummatory_apply, Pi.one_apply,
      Finset.sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast, ← Nat.card_eq_finsetCard]
    exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun I ↦ mem_normLE _))
  have hlow := b.le_card x hx1
  rw [← hcard] at hlow
  have := hlow.trans hxC.2
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le θ)] at this
  have hsplit : x ^ (1 - θ) * b.lower * x ^ θ = b.lower * x := by
    rw [mul_comm (x ^ (1 - θ)), mul_assoc, ← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  rw [div_lt_iff₀ b.lower_pos] at hxC
  linarith [mul_lt_mul_of_pos_right hxC.1 (Real.rpow_pos_of_pos hx0 θ)]

end UnitaryIdealWeight

/-- The **continued L-function of a unitary ideal weight**:
`s * ∫_1^∞ A_χ(t) t^{-(s+1)} dt`, where `A_χ(t) = ∑_{N(I) ≤ t} χ(I)` is the inclusive ideal partial
sum.  It is the `LSeries` of the norm coefficients of `χ` on `Re s > 1`
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`) and, when `χ` has cancellation, holomorphic on
`Re s > 1 - 1/[K : ℚ]` (`TauCeti.differentiableOn_continuedLFunctionOfWeight`). -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) (s : ℂ) : ℂ :=
  s * ∫ t in Ioi (1 : ℝ), idealSummatory K χ.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1))

theorem continuedLFunctionOfWeight_def (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s =
      s * ∫ t in Ioi (1 : ℝ), idealSummatory K χ.toIdealArithmeticFunction t *
        (t : ℂ) ^ (-(s + 1)) :=
  (rfl)

/-- **Agreement with the norm-regrouped series.** On `Re s > 1` the continued L-function of a
unitary weight is the `LSeries` of its norm coefficients.  No cancellation is needed here. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.toIdealArithmeticFunction) s := by
  rw [LSeries_eq_mul_integral' _ zero_le_one hs, continuedLFunctionOfWeight_def]
  · simp_rw [idealSummatory_eq_sum_Icc_normCoeff]
  · refine (IsBigO.of_bound 1 (Eventually.of_forall fun n ↦ ?_)).trans
      (isBigO_sum_norm_normCoeff_one K)
    rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    exact Finset.sum_le_sum fun k _ ↦ χ.norm_normCoeff_le_norm_normCoeff_one k

/-- **Holomorphic continuation from cancellation.** If `χ` has cancellation, its continued
L-function is complex differentiable on the half-plane `Re s > 1 - 1/[K : ℚ]`. -/
theorem differentiableOn_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : χ.HasCancellation) :
    DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} := by
  have hA : LocallyIntegrableOn
      (fun t : ℝ ↦ idealSummatory K χ.toIdealArithmeticFunction t) (Ici 1) := by
    simpa [idealSummatory_eq_sum_Icc_normCoeff] using
      locallyIntegrableOn_mul_sum_Icc (normCoeff K χ.toIdealArithmeticFunction) (m := 1)
        zero_le_one (g := fun _ ↦ (1 : ℂ)) (locallyIntegrableOn_const 1)
  exact differentiableOn_id.mul (differentiableOn_integral_Ioi_one_mul_cpow hA hχ)

/-- **Analytic continuation from cancellation.** If `χ` has cancellation, its continued
L-function is analytic on the open half-plane `Re s > 1 - 1/[K : ℚ]`. -/
theorem analyticOnNhd_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : χ.HasCancellation) :
    AnalyticOnNhd ℂ (continuedLFunctionOfWeight χ)
      {s | 1 - (Module.finrank ℚ K : ℝ)⁻¹ < s.re} :=
  (differentiableOn_continuedLFunctionOfWeight hχ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

end TauCeti
