/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow

/-!
# Schur's test for integral operators

Let `k : α → β → ℝ≥0∞` be a jointly measurable kernel whose row integrals `∫⁻ y, k x y ∂ν` are
at most `A` and whose column integrals `∫⁻ x, k x y ∂μ` are at most `B`. Then, for `1 ≤ p`, the
integral operator `g ↦ (x ↦ ∫⁻ y, k x y * g y ∂ν)` satisfies

`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`,

that is, it maps `Lᵖ(ν)` to `Lᵖ(μ)` with norm at most `A ^ (1 - 1/p) * B ^ (1/p)`. For a
translation-invariant kernel `k x y = K (x - y)` with `K` integrable this is Young's inequality
for convolution with an `L¹` function; a typical use is for weakly singular kernels such as
`‖x - y‖ ^ (1 - n)` restricted to a bounded set, which bound Riesz potentials in `Lᵖ`.

The proof applies Hölder's inequality, in the form
`TauCeti.rpow_lintegral_le_measure_univ_rpow_mul`, to the measure `ν.withDensity (k x)` for each
`x`, and then exchanges the order of integration by Tonelli's theorem.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses, and the bounds on the row
and column integrals are only required almost everywhere.

## Main declarations

* `TauCeti.lintegral_rpow_lintegral_mul_le`: Schur's test.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- **Schur's test.** If the kernel `k` has row integrals `∫⁻ y, k x y ∂ν` at most `A` for almost
every `x` and column integrals `∫⁻ x, k x y ∂μ` at most `B` for almost every `y`, then for
`1 ≤ p` the integral operator with kernel `k` satisfies
`∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν`. -/
theorem lintegral_rpow_lintegral_mul_le [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {g : β → ℝ≥0∞} (hg : AEMeasurable g ν) {p : ℝ}
    (hp : 1 ≤ p) {A B : ℝ≥0∞} (hA : ∀ᵐ x ∂μ, ∫⁻ y, k x y ∂ν ≤ A)
    (hB : ∀ᵐ y ∂ν, ∫⁻ x, k x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ ≤ A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν := by
  have hkx : ∀ x, Measurable (k x) := fun x => hk.comp measurable_prodMk_left
  have hky : ∀ y, Measurable fun x => k x y := fun y => hk.comp measurable_prodMk_right
  -- Hölder's inequality for the measure `ν.withDensity (k x)`, for each fixed `x`.
  have hrow : ∀ x, (∫⁻ y, k x y * g y ∂ν) ^ p ≤
      (∫⁻ y, k x y ∂ν) ^ (p - 1) * ∫⁻ y, k x y * g y ^ p ∂ν := by
    intro x
    have h := rpow_lintegral_le_measure_univ_rpow_mul
      (hg.mono_ac (withDensity_absolutelyContinuous ν (k x))) hp
    rwa [lintegral_withDensity_eq_lintegral_mul₀ (hkx x).aemeasurable hg,
      lintegral_withDensity_eq_lintegral_mul₀ (hkx x).aemeasurable (hg.pow_const p),
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  have hjoint : AEMeasurable (Function.uncurry fun x y => k x y * g y ^ p) (μ.prod ν) :=
    hk.aemeasurable.mul (hg.pow_const p).comp_snd
  calc
    ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ p ∂μ
        ≤ ∫⁻ x, A ^ (p - 1) * ∫⁻ y, k x y * g y ^ p ∂ν ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [hA] with x hx
      exact (hrow x).trans (by gcongr)
    _ = A ^ (p - 1) * ∫⁻ y, ∫⁻ x, k x y * g y ^ p ∂μ ∂ν := by
      have hmeas : AEMeasurable (fun x => ∫⁻ y, k x y * g y ^ p ∂ν) μ :=
        hjoint.lintegral_prod_right'
      rw [lintegral_const_mul'' _ hmeas, lintegral_lintegral_swap hjoint]
    _ = A ^ (p - 1) * ∫⁻ y, (∫⁻ x, k x y ∂μ) * g y ^ p ∂ν := by
      simp_rw [lintegral_mul_const _ (hky _)]
    _ ≤ A ^ (p - 1) * ∫⁻ y, B * g y ^ p ∂ν := by
      gcongr 1
      refine lintegral_mono_ae ?_
      filter_upwards [hB] with y hy
      gcongr
    _ = A ^ (p - 1) * B * ∫⁻ y, g y ^ p ∂ν := by
      rw [lintegral_const_mul'' _ (hg.pow_const p), mul_assoc]

end TauCeti
