/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.InternalEnergy.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The Rényi entropy functional

The *Rényi entropy* of a measure `μ` relative to a reference measure `m`, with dimension parameter
`N`, is

`S_N(μ | m) = -∫ ρ^{-1/N} dμᵃᶜ = -∫ ρ^{1-1/N} dm`,

where `μ = ρ m + μˢ` is the Lebesgue decomposition of `μ` with respect to `m` and the first
integral is over the absolutely continuous part `μᵃᶜ = ρ m` (`TauCeti.renyiEntropy`). It is the
entropy functional of the finite-dimensional curvature-dimension conditions `CD(K, N)` and
`CD*(K, N)` and of the measure-contraction property `MCP(K, N)` of Sturm and Lott–Villani: those
conditions compare `S_N` along a Wasserstein geodesic with distortion coefficients (`CD(K, N)`
with `TauCeti.distortionTau`, `CD*(K, N)` with `TauCeti.distortionSigma`), as `CD(K, ∞)` does with
the Boltzmann entropy.

It is the internal energy (`TauCeti.internalEnergy`) for `U(r) = -r · r^{-1/N}`, which is
`-r^{1-1/N}` for `r > 0` and `0` at `r = 0`. For `N > 0` the recession constant of `U` is `0`, so
the singular part of `μ` does not contribute, and since `U ≤ 0` the entropy takes values in
`[-∞, 0]`: `S_N(μ | m) = -∫⁻ ρ · ρ^{-1/N} dm` (`TauCeti.renyiEntropy_eq_neg_lintegral`), which is
`-∫⁻ ρ^{1-1/N} dm` when `N > 1` and `μ` is σ-finite
(`TauCeti.renyiEntropy_eq_neg_lintegral_rpow`). For `N = 1` the integrand is the indicator of
`{ρ > 0}`, so `S_1(μ | m) = -m {ρ > 0}`, as in Sturm's convention `S_N(μ | m) = -∫ ρ^{-1/N} dμᵃᶜ`.
A measure singular with respect to `m`, such as a Dirac mass against Lebesgue measure, has Rényi
entropy `0`.

For `N ≥ 1`, Hölder's inequality bounds the entropy below by the measure of a set carrying `μ`:
if `μ(Aᶜ) = 0`, then

`S_N(μ | m) ≥ -m(A)^{1/N} μ(X)^{1-1/N}`

(`TauCeti.neg_rpow_mul_rpow_le_renyiEntropy`), so the entropy of a finite measure carried by a set
of finite `m`-measure is finite (`TauCeti.renyiEntropy_ne_bot_of_measure_compl_eq_zero`). The
bound is sharp: the uniform law `m(A)⁻¹ m|_A` on a set of finite positive measure has
`S_N = -m(A)^{1/N}` (`TauCeti.renyiEntropy_smul_restrict`).

As `N → ∞` the Rényi entropies recover the Boltzmann entropy `Ent_m(μ)`
(`TauCeti.boltzmannEntropy`) of `CD(K, ∞)`: for `μ` finite and carried by a set of finite
`m`-measure,

`N (S_N(μ | m) + μ(X)) → Ent_m(μ)`

(`TauCeti.tendsto_mul_renyiEntropy_add_measureReal_univ_nhds_boltzmannEntropy`). The left side is
`∫ U_N(ρ) dm` plus `N μˢ(X)`, where `U_N(r) = N (r - r^{1-1/N})` increases with `N` to `r log r`; a
nonzero singular part makes `Ent_m(μ) = ⊤`, and the left side tends to `⊤` through the term
`N μˢ(X)`.

## Main definitions

* `TauCeti.renyiEntropy N m μ`: the Rényi entropy `S_N(μ | m)`, as an extended real.

## Main results

* `TauCeti.renyiEntropy_eq_neg_lintegral`, `TauCeti.renyiEntropy_eq_neg_lintegral_rpow`: the
  integral formulas for `S_N`.
* `TauCeti.renyiEntropy_nonpos`, `TauCeti.renyiEntropy_ne_top`, `TauCeti.renyiEntropy_eq_bot_iff`:
  the entropy lies in `[-∞, 0]`, and is `-∞` exactly when `∫ ρ · ρ^{-1/N} dm` diverges.
* `TauCeti.renyiEntropy_of_mutuallySingular`: singular measures have Rényi entropy `0`.
* `TauCeti.neg_rpow_mul_rpow_le_renyiEntropy`: the Hölder lower bound, and
  `TauCeti.renyiEntropy_ne_bot_of_measure_compl_eq_zero`, `TauCeti.renyiEntropy_ne_bot`: the entropy
  of a finite measure carried by a set of finite `m`-measure, or against a finite reference, is
  finite.
* `TauCeti.renyiEntropy_smul_restrict`: the entropy of a uniform law.
* `TauCeti.tendsto_mul_renyiEntropy_add_measureReal_univ_nhds_boltzmannEntropy`: the Boltzmann
  entropy as the limit of the Rényi entropies.

## References

* K.-T. Sturm, *On the geometry of metric measure spaces. II*, Acta Math. 196 (2006), 133–177.
* J. Lott and C. Villani, *Ricci curvature for metric-measure spaces via optimal transport*,
  Ann. of Math. 169 (2009), 903–991.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapters 16–17 and 29.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {N : ℝ} {m μ : Measure X}

/-- The *Rényi entropy* `S_N(μ | m) = -∫ ρ^{1-1/N} dm` of a measure `μ` relative to a reference
measure `m`, where `ρ` is the density of the absolutely continuous part of `μ`: the internal energy
for `U(r) = -r · r^{-1/N}`.

For `N > 0` the singular part of `μ` does not contribute and the value lies in `[-∞, 0]`
(`TauCeti.renyiEntropy_eq_neg_lintegral`). For `N = 1` the integrand is the indicator of
`{ρ > 0}`, following Sturm's convention `S_N(μ | m) = -∫ ρ^{-1/N} dμᵃᶜ`. The curvature-dimension
theory uses `N ≥ 1`; other values of `N` carry no meaning. -/
def renyiEntropy (N : ℝ) (m μ : Measure X) : EReal :=
  internalEnergy (fun r ↦ -(r * r ^ (-N⁻¹))) m μ

/-- The Rényi entropy is the internal energy for `U(r) = -r · r^{-1/N}`. -/
theorem renyiEntropy_def (N : ℝ) (m μ : Measure X) :
    renyiEntropy N m μ = internalEnergy (fun r ↦ -(r * r ^ (-N⁻¹))) m μ := (rfl)

/-- The recession constant of the Rényi integrand vanishes: `-r^{-1/N} → 0`. -/
private theorem recessionConstant_neg_mul_rpow_neg (hN : 0 < N) :
    recessionConstant (fun r ↦ -(r * r ^ (-N⁻¹))) = 0 := by
  refine recessionConstant_eq_of_tendsto ?_
  rw [← EReal.coe_zero]
  refine EReal.tendsto_coe.2 ?_
  have h := (tendsto_rpow_neg_atTop (inv_pos.2 hN)).neg
  rw [neg_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [neg_div, mul_div_cancel_left₀ _ hs.ne']

/-- The real and extended forms of the Rényi integrand agree everywhere, including at `0` and `∞`,
where both vanish. -/
private theorem ofReal_toReal_mul_rpow_neg (hN : 0 < N) (x : ℝ≥0∞) :
    ENNReal.ofReal (x.toReal * x.toReal ^ (-N⁻¹)) = x * x ^ (-N⁻¹) := by
  have hN' : -N⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hN)
  rcases eq_or_ne x ∞ with rfl | hx
  · simp [ENNReal.top_rpow_of_neg hN']
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx, ENNReal.toReal_rpow,
    ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_ne_zero hx₀ hx)]

/-- For `N > 0`, the Rényi entropy is `S_N(μ | m) = -∫⁻ ρ · ρ^{-1/N} dm`, where `ρ` is the
Radon–Nikodym derivative of `μ` with respect to `m`; the singular part of `μ` does not
contribute. -/
theorem renyiEntropy_eq_neg_lintegral (hN : 0 < N) :
    renyiEntropy N m μ =
      -((∫⁻ x, μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹) ∂m : ℝ≥0∞) : EReal) := by
  have hpos (x : X) : ENNReal.ofReal (-((μ.rnDeriv m x).toReal *
      (μ.rnDeriv m x).toReal ^ (-N⁻¹))) = 0 :=
    ENNReal.ofReal_eq_zero.2 <| neg_nonpos.2 <|
      mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  rw [renyiEntropy_def, internalEnergy_def]
  simp only [recessionConstant_neg_mul_rpow_neg hN, hpos, neg_neg, ofReal_toReal_mul_rpow_neg hN,
    lintegral_zero, neg_zero, EReal.toENNReal_zero, zero_mul, add_zero, ENNReal.zero_ne_top,
    ↓reduceIte, EReal.coe_ennreal_zero, zero_sub]

/-- For `N > 1` and σ-finite `μ`, the Rényi entropy is `S_N(μ | m) = -∫⁻ ρ^{1-1/N} dm`. -/
theorem renyiEntropy_eq_neg_lintegral_rpow [SigmaFinite μ] (hN : 1 < N) :
    renyiEntropy N m μ = -((∫⁻ x, μ.rnDeriv m x ^ (1 - N⁻¹) ∂m : ℝ≥0∞) : EReal) := by
  have hN₀ : 0 < N := one_pos.trans hN
  have hq : 0 < 1 - N⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hN)
  rw [renyiEntropy_eq_neg_lintegral hN₀]
  congr 2
  refine lintegral_congr_ae <| (μ.rnDeriv_lt_top m).mono fun x hx ↦ ?_
  rcases eq_or_ne (μ.rnDeriv m x) 0 with h₀ | h₀
  · simp [h₀, ENNReal.zero_rpow_of_pos hq]
  · simp only [sub_eq_add_neg, ENNReal.rpow_add _ _ h₀ hx.ne, ENNReal.rpow_one]

/-- For `N > 0`, the Rényi entropy is nonpositive. -/
theorem renyiEntropy_nonpos (hN : 0 < N) : renyiEntropy N m μ ≤ 0 := by
  rw [renyiEntropy_eq_neg_lintegral hN, EReal.neg_le, neg_zero]
  exact EReal.coe_ennreal_nonneg _

/-- For `N > 0`, the Rényi entropy is never `⊤`. -/
theorem renyiEntropy_ne_top (hN : 0 < N) : renyiEntropy N m μ ≠ ⊤ :=
  ((renyiEntropy_nonpos hN).trans_lt EReal.zero_lt_top).ne

/-- For `N > 0`, the Rényi entropy is `⊥` exactly when `∫⁻ ρ · ρ^{-1/N} dm` diverges. -/
theorem renyiEntropy_eq_bot_iff (hN : 0 < N) :
    renyiEntropy N m μ = ⊥ ↔ ∫⁻ x, μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹) ∂m = ∞ := by
  rw [renyiEntropy_eq_neg_lintegral hN, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]

/-- The Rényi entropy of the zero measure is `0`. -/
@[simp]
theorem renyiEntropy_zero_measure (N : ℝ) (m : Measure X) : renyiEntropy N m 0 = 0 :=
  internalEnergy_zero_measure (by simp) m

/-- The Rényi entropy of an absolutely continuous measure does not depend on the choice of density:
for `N > 0` and every almost everywhere measurable density `f`,
`S_N(f m | m) = -∫⁻ f · f^{-1/N} dm`. -/
theorem renyiEntropy_withDensity [SigmaFinite m] (hN : 0 < N) {f : X → ℝ≥0∞}
    (hf : AEMeasurable f m) :
    renyiEntropy N m (m.withDensity f) = -((∫⁻ x, f x * f x ^ (-N⁻¹) ∂m : ℝ≥0∞) : EReal) := by
  rw [renyiEntropy_eq_neg_lintegral hN]
  congr 2
  exact lintegral_congr_ae <| (Measure.rnDeriv_withDensity₀ m hf).mono fun x hx ↦ by simp only [hx]

/-- For `N > 0`, a measure singular with respect to `m` has Rényi entropy `0`. -/
theorem renyiEntropy_of_mutuallySingular [μ.HaveLebesgueDecomposition m] (hN : 0 < N)
    (h : μ ⟂ₘ m) : renyiEntropy N m μ = 0 := by
  rw [renyiEntropy_eq_neg_lintegral hN,
    lintegral_congr_ae (g := 0) <| ((Measure.rnDeriv_eq_zero μ m).2 h).mono fun x hx ↦ by
      simp [hx]]
  simp

/-- For `N > 1`, the Rényi integrand `x · x^{-1/N}` is at most `x^{1-1/N}`, with equality off
`∞`. -/
private theorem mul_rpow_neg_le_rpow_one_sub (hN : 1 < N) (x : ℝ≥0∞) :
    x * x ^ (-N⁻¹) ≤ x ^ (1 - N⁻¹) := by
  have hq : 0 < 1 - N⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ hN)
  rcases eq_or_ne x ∞ with rfl | hx
  · simp [ENNReal.top_rpow_of_neg (neg_neg_of_pos (inv_pos.2 (one_pos.trans hN)))]
  rcases eq_or_ne x 0 with rfl | hx₀
  · simp [ENNReal.zero_rpow_of_pos hq]
  rw [sub_eq_add_neg, ENNReal.rpow_add _ _ hx₀ hx, ENNReal.rpow_one]

/-- For `N ≥ 1`, Hölder's inequality bounds the Rényi entropy below by the measure of any set
carrying `μ`: if `μ(Aᶜ) = 0`, then `S_N(μ | m) ≥ -m(A)^{1/N} μ(X)^{1-1/N}`. The uniform laws attain
the bound (`TauCeti.renyiEntropy_smul_restrict`). -/
theorem neg_rpow_mul_rpow_le_renyiEntropy (hN : 1 ≤ N) {A : Set X} (hA : μ Aᶜ = 0) :
    -((m A ^ N⁻¹ * μ univ ^ (1 - N⁻¹) : ℝ≥0∞) : EReal) ≤ renyiEntropy N m μ := by
  have hN₀ : 0 < N := one_pos.trans_le hN
  rw [renyiEntropy_eq_neg_lintegral hN₀, EReal.neg_le_neg_iff,
    EReal.coe_ennreal_le_coe_ennreal_iff]
  -- Pass to a measurable hull `B` of `A`, off which the density vanishes.
  set B := toMeasurable m A
  have hB : MeasurableSet B := measurableSet_toMeasurable m A
  have hρB := Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := m)
    (measure_mono_null (compl_subset_compl.2 (subset_toMeasurable m A)) hA)
  rcases hN.eq_or_lt with rfl | hN₁
  · -- For `N = 1` the integrand is at most the indicator of `B`.
    calc ∫⁻ x, μ.rnDeriv m x * μ.rnDeriv m x ^ (-(1 : ℝ)⁻¹) ∂m
        ≤ ∫⁻ x, B.indicator 1 x ∂m := by
          refine lintegral_mono_ae <| hρB.mono fun x hx ↦ ?_
          by_cases hxB : x ∈ B
          · simp [hxB, ENNReal.rpow_neg_one]
          · simp [hxB, hx hxB]
      _ = m A ^ (1 : ℝ)⁻¹ * μ univ ^ (1 - (1 : ℝ)⁻¹) := by
          simp [lintegral_indicator_one hB, B, measure_toMeasurable]
  -- For `N > 1`, apply Hölder's inequality to `ρ^{1-1/N}` and the indicator of `B`, with the
  -- conjugate exponents `N / (N - 1)` and `N`.
  have hpq := (Real.HolderConjugate.conjExponent hN₁).symm
  set p := N.conjExponent
  have hp : p⁻¹ = 1 - N⁻¹ := eq_sub_of_add_eq hpq.inv_add_inv_eq_one
  have hqp : (1 - N⁻¹) * p = 1 := by rw [← hp, inv_mul_cancel₀ hpq.ne_zero]
  have hind (x : X) : B.indicator (1 : X → ℝ≥0∞) x ^ N = B.indicator 1 x := by
    by_cases hxB : x ∈ B <;> simp [hxB, hN₀]
  calc ∫⁻ x, μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹) ∂m
      ≤ ∫⁻ x, ((fun x ↦ μ.rnDeriv m x ^ (1 - N⁻¹)) * B.indicator 1 : X → ℝ≥0∞) x ∂m := by
        refine lintegral_mono_ae <| hρB.mono fun x hx ↦ ?_
        by_cases hxB : x ∈ B
        · simpa [hxB] using mul_rpow_neg_le_rpow_one_sub hN₁ (μ.rnDeriv m x)
        · simp [hxB, hx hxB]
    _ ≤ (∫⁻ x, (μ.rnDeriv m x ^ (1 - N⁻¹)) ^ p ∂m) ^ (1 / p) *
          (∫⁻ x, B.indicator 1 x ^ N ∂m) ^ (1 / N) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq m hpq
          ((Measure.measurable_rnDeriv μ m).pow_const _).aemeasurable
          (aemeasurable_one.indicator hB)
    _ = (∫⁻ x, μ.rnDeriv m x ∂m) ^ (1 - N⁻¹) * m A ^ N⁻¹ := by
        simp only [← ENNReal.rpow_mul, hqp, ENNReal.rpow_one, hind, lintegral_indicator_one hB,
          one_div, hp, B, measure_toMeasurable]
    _ ≤ m A ^ N⁻¹ * μ univ ^ (1 - N⁻¹) := by
        rw [mul_comm]
        gcongr
        · exact (sub_pos.2 (inv_lt_one_of_one_lt₀ hN₁)).le
        · exact Measure.lintegral_rnDeriv_le

/-- For `N ≥ 1`, the Rényi entropy of a finite measure carried by a set of finite `m`-measure is
never `⊥`. -/
theorem renyiEntropy_ne_bot_of_measure_compl_eq_zero [IsFiniteMeasure μ] (hN : 1 ≤ N) {A : Set X}
    (hA : μ Aᶜ = 0) (hmA : m A ≠ ∞) : renyiEntropy N m μ ≠ ⊥ := by
  refine ne_bot_of_le_ne_bot ?_ (neg_rpow_mul_rpow_le_renyiEntropy hN hA)
  rw [Ne, EReal.neg_eq_bot_iff, EReal.coe_ennreal_eq_top_iff]
  exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 (zero_le_one.trans hN)) hmA)
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 (inv_le_one_of_one_le₀ hN))
      (measure_ne_top μ univ))

/-- For `N ≥ 1`, the Rényi entropy of a finite measure relative to a finite reference measure is
never `⊥`. -/
theorem renyiEntropy_ne_bot [IsFiniteMeasure m] [IsFiniteMeasure μ] (hN : 1 ≤ N) :
    renyiEntropy N m μ ≠ ⊥ :=
  renyiEntropy_ne_bot_of_measure_compl_eq_zero hN (A := univ) (by simp) (measure_ne_top m univ)

/-- The uniform law `m(A)⁻¹ m|_A` on a measurable set of finite positive measure has Rényi entropy
`-m(A)^{1/N}`, so the bound `TauCeti.neg_rpow_mul_rpow_le_renyiEntropy` is attained. -/
theorem renyiEntropy_smul_restrict [SigmaFinite m] (hN : 0 < N) {A : Set X} (hA : MeasurableSet A)
    (h₀ : m A ≠ 0) (h₁ : m A ≠ ∞) :
    renyiEntropy N m ((m A)⁻¹ • m.restrict A) = -((m A ^ N⁻¹ : ℝ≥0∞) : EReal) := by
  rw [← withDensity_const, ← withDensity_indicator hA,
    renyiEntropy_withDensity hN (aemeasurable_const.indicator hA)]
  have h : (fun x ↦ A.indicator (fun _ ↦ (m A)⁻¹) x * A.indicator (fun _ ↦ (m A)⁻¹) x ^ (-N⁻¹))
      = A.indicator fun _ ↦ (m A)⁻¹ * ((m A)⁻¹) ^ (-N⁻¹) := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [h, lintegral_indicator_const hA, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv,
    mul_right_comm, ENNReal.inv_mul_cancel h₀ h₁, one_mul]

/-! ### The Boltzmann entropy as the limit `N → ∞` -/

/-- The integrand `U_N(r) = N (r - r · r^{-1/N})` of `N (S_N(μ | m) + μ(X))`, which is
`N (r - r^{1-1/N})` for `r > 0`. -/
private def renyiGap (N r : ℝ) : ℝ := N * (r - r * r ^ (-N⁻¹))

/-- The integrand `U_N(r)` increases with `N > 0`. -/
private theorem renyiGap_le_renyiGap {r : ℝ} (hr : 0 ≤ r) {N N' : ℝ} (hN : 0 < N)
    (hNN' : N ≤ N') : renyiGap N r ≤ renyiGap N' r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [renyiGap]
  have hN' : 0 < N' := hN.trans_le hNN'
  -- The secant slopes from `0` of the convex function `s ↦ (r⁻¹) ^ s` increase.
  have h := (convexOn_rpow_left (inv_pos.2 hr)).secant_mono (a := 0) (x := N'⁻¹) (y := N⁻¹)
    (mem_univ _) (mem_univ _) (mem_univ _) (inv_ne_zero hN'.ne') (inv_ne_zero hN.ne')
    (inv_anti₀ hN hNN')
  simp only [Real.rpow_zero, sub_zero, div_inv_eq_mul, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le] at h
  simp only [renyiGap]
  nlinarith [mul_le_mul_of_nonneg_left h hr.le]

/-- The integrand `U_N(r)` tends to `r log r` as `N → ∞`. -/
private theorem tendsto_renyiGap {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (renyiGap · r) atTop (𝓝 (r * Real.log r)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [renyiGap]
  -- This is the derivative of `s ↦ (r⁻¹) ^ s` at `0`, read off along the slopes at `s = 1 / N`.
  have hd :=
    (Real.hasStrictDerivAt_const_rpow (inv_pos.2 hr) 0).hasDerivAt.tendsto_slope_zero_right
  have h := (hd.comp tendsto_inv_atTop_nhdsGT_zero).const_mul (-r)
  rw [Real.rpow_zero, one_mul, Real.log_inv, neg_mul_neg] at h
  refine h.congr fun N ↦ ?_
  simp only [renyiGap, Function.comp_apply, zero_add, smul_eq_mul, inv_inv, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le]
  ring

/-- If `μ` is carried by `A`, then for `N ≥ 1` the function `U_N(ρ) + 1_B`, with `B` the measurable
hull of `A`, is nonnegative `m`-almost everywhere. -/
private theorem ae_renyiGap_add_indicator_nonneg {A : Set X} (hA : μ Aᶜ = 0) (hN : 1 ≤ N) :
    ∀ᵐ x ∂m, 0 ≤ renyiGap N (μ.rnDeriv m x).toReal + (toMeasurable m A).indicator 1 x := by
  filter_upwards [Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero (ν := m)
    (measure_mono_null (compl_subset_compl.2 (subset_toMeasurable m A)) hA)] with x hx
  by_cases hxB : x ∈ toMeasurable m A
  · -- `U_N(r) ≥ U_1(r) = r - r · r⁻¹ ≥ -1`.
    set r := (μ.rnDeriv m x).toReal
    have hr : 0 ≤ r := ENNReal.toReal_nonneg
    have h₁ : r * r ^ (-(1 : ℝ)⁻¹) ≤ 1 := by
      rw [inv_one, Real.rpow_neg_one]
      rcases hr.eq_or_lt with h₀ | h₀
      · simp [← h₀]
      · rw [mul_inv_cancel₀ h₀.ne']
    have h := renyiGap_le_renyiGap hr one_pos hN
    simp only [renyiGap, one_mul] at h
    rw [indicator_of_mem hxB, Pi.one_apply, renyiGap]
    linarith
  · simp [renyiGap, hxB, hx hxB]

/-- The indicator of the measurable hull of a set of finite `m`-measure is integrable. -/
private theorem integrable_indicator_toMeasurable {A : Set X} (hmA : m A ≠ ∞) :
    Integrable ((toMeasurable m A).indicator (1 : X → ℝ)) m :=
  (integrableOn_const (C := (1 : ℝ)) (by rwa [measure_toMeasurable])).integrable_indicator
    (measurableSet_toMeasurable m A)

/-- Monotone convergence for `∫⁻ (U_N(ρ) + g)⁺ dm` as `N → ∞`. -/
private theorem tendsto_lintegral_renyiGap {g : X → ℝ} (hg : Measurable g) :
    Tendsto (fun N ↦ ∫⁻ x, ENNReal.ofReal (renyiGap N (μ.rnDeriv m x).toReal + g x) ∂m) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal
        ((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal + g x) ∂m)) := by
  have hρm : Measurable fun x ↦ (μ.rnDeriv m x).toReal :=
    (Measure.measurable_rnDeriv μ m).ennreal_toReal
  -- Read the integrals along `max N 1`, where they are monotone in `N`.
  set Φ : ℝ → ℝ≥0∞ :=
    fun N ↦ ∫⁻ x, ENNReal.ofReal (renyiGap (max N 1) (μ.rnDeriv m x).toReal + g x) ∂m
  have hmono {N N' : ℝ} (hNN' : N ≤ N') (x : X) :
      renyiGap (max N 1) (μ.rnDeriv m x).toReal ≤ renyiGap (max N' 1) (μ.rnDeriv m x).toReal :=
    renyiGap_le_renyiGap ENNReal.toReal_nonneg (one_pos.trans_le (le_max_right N 1))
      (max_le_max_right 1 hNN')
  have hΦ_mono : Monotone Φ := fun N N' hNN' ↦ lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (add_le_add_left (hmono hNN' x) _)
  have hmax : Tendsto (fun N : ℝ ↦ max N 1) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ le_max_left N 1) tendsto_id
  have hΦ_nat := lintegral_tendsto_of_tendsto_of_monotone (μ := m)
    (f := fun n : ℕ ↦ fun x ↦ ENNReal.ofReal (renyiGap (max n 1) (μ.rnDeriv m x).toReal + g x))
    (fun n ↦ (Measurable.ennreal_ofReal (by simp only [renyiGap]; fun_prop)).aemeasurable)
    (ae_of_all _ fun x n n' hnn' ↦ ENNReal.ofReal_le_ofReal
      (add_le_add_left (hmono (by exact_mod_cast hnn') x) _))
    (ae_of_all _ fun x ↦ ENNReal.tendsto_ofReal <|
      ((tendsto_renyiGap ENNReal.toReal_nonneg).comp
        (hmax.comp tendsto_natCast_atTop_atTop)).add_const (g x))
  have hsup := tendsto_atTop_iSup hΦ_mono
  rw [tendsto_nhds_unique (hsup.comp tendsto_natCast_atTop_atTop) hΦ_nat] at hsup
  refine hsup.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Φ, max_eq_left hN]

/-- For `N ≥ 1` and `μ` carried by a set `A` of finite `m`-measure, with measurable hull `B`,
`N (S_N(μ | m) + μ(X)) = ∫⁻ (U_N(ρ) + 1_B) dm - m(B) + N μˢ(X)`. -/
private theorem mul_renyiEntropy_add_eq [IsFiniteMeasure μ] [μ.HaveLebesgueDecomposition m]
    {A : Set X} (hA : μ Aᶜ = 0) (hmA : m A ≠ ∞) (hN : 1 ≤ N) :
    (N : EReal) * (renyiEntropy N m μ + μ.real univ) =
      ((∫⁻ x, ENNReal.ofReal (renyiGap N (μ.rnDeriv m x).toReal
          + (toMeasurable m A).indicator 1 x) ∂m : ℝ≥0∞) : EReal)
        - (m.real (toMeasurable m A) : EReal)
        + ((N * (μ.singularPart m).real univ : ℝ) : EReal) := by
  have hN₀ : 0 < N := one_pos.trans_le hN
  set B := toMeasurable m A
  have hB : MeasurableSet B := measurableSet_toMeasurable m A
  set ρ : X → ℝ := fun x ↦ (μ.rnDeriv m x).toReal
  -- The three integrands `ρ`, `ρ · ρ^{-1/N}` and `1_B` are integrable.
  have hg : Integrable (B.indicator (1 : X → ℝ)) m := integrable_indicator_toMeasurable hmA
  have hρl : ∫⁻ x, μ.rnDeriv m x ∂m ≠ ∞ :=
    (Measure.lintegral_rnDeriv_le.trans_lt (measure_lt_top μ univ)).ne
  have hρi : Integrable ρ m :=
    integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv μ m).aemeasurable hρl
  set I := ∫⁻ x, μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹) ∂m
  have hI : I ≠ ∞ := fun h ↦
    renyiEntropy_ne_bot_of_measure_compl_eq_zero hN hA hmA ((renyiEntropy_eq_bot_iff hN₀).2 h)
  have hpow (x : X) : ρ x * ρ x ^ (-N⁻¹) = (μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹)).toReal := by
    rw [← ofReal_toReal_mul_rpow_neg hN₀, ENNReal.toReal_ofReal
      (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _))]
  have hpm : Measurable fun x ↦ μ.rnDeriv m x * μ.rnDeriv m x ^ (-N⁻¹) := by
    have := Measure.measurable_rnDeriv μ m
    fun_prop
  have hpi : Integrable (fun x ↦ ρ x * ρ x ^ (-N⁻¹)) m := by
    simp_rw [hpow]
    exact integrable_toReal_of_lintegral_ne_top hpm.aemeasurable hI
  -- Their integrals are `μ(X) - μˢ(X)`, `I` and `m(B)`.
  have hρint : ∫ x, ρ x ∂m = μ.real univ - (μ.singularPart m).real univ := by
    have h : μ univ = μ.singularPart m univ + ∫⁻ x, μ.rnDeriv m x ∂m := by
      conv_lhs => rw [μ.haveLebesgueDecomposition_add m]
      rw [Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [integral_toReal (Measure.measurable_rnDeriv μ m).aemeasurable (μ.rnDeriv_lt_top m),
      measureReal_def, measureReal_def, h, ENNReal.toReal_add (measure_ne_top _ _) hρl]
    ring
  have hpint : ∫ x, ρ x * ρ x ^ (-N⁻¹) ∂m = I.toReal := by
    simp_rw [hpow]
    refine integral_toReal hpm.aemeasurable (ae_of_all _ fun x ↦ ?_)
    rw [← ofReal_toReal_mul_rpow_neg hN₀]
    exact ENNReal.ofReal_lt_top
  have hFi : Integrable (fun x ↦ renyiGap N (ρ x)) m := (hρi.sub hpi).const_mul N
  have hint : ∫ x, (renyiGap N (ρ x) + B.indicator 1 x) ∂m =
      N * (μ.real univ - (μ.singularPart m).real univ - I.toReal) + m.real B := by
    rw [integral_add hFi hg]
    simp only [renyiGap]
    rw [integral_const_mul, integral_sub hρi hpi, hρint, hpint, integral_indicator_one hB]
  have hhi : Integrable (fun x ↦ renyiGap N (μ.rnDeriv m x).toReal + B.indicator 1 x) m :=
    hFi.add hg
  rw [← ofReal_integral_eq_lintegral_ofReal hhi (ae_renyiGap_add_indicator_nonneg hA hN),
    EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg_of_ae (ae_renyiGap_add_indicator_nonneg hA hN)), hint,
    renyiEntropy_eq_neg_lintegral hN₀, ← EReal.coe_ennreal_toReal hI]
  norm_cast
  ring

/-- As `N → ∞`, `N (S_N(μ | m) + μ(X))` tends to the Boltzmann entropy `Ent_m(μ)`, for a finite
measure `μ` carried by a set `A` of finite `m`-measure.

This is the integrated form of the pointwise limit `N (r - r^{1-1/N}) → r log r`, which is
monotone in `N`. The limit may be `⊤`; in particular it is `⊤` when `μ` is not absolutely
continuous with respect to `m`, since its singular mass contributes `N μˢ(X)`. -/
theorem tendsto_mul_renyiEntropy_add_measureReal_univ_nhds_boltzmannEntropy [IsFiniteMeasure μ]
    [μ.HaveLebesgueDecomposition m] {A : Set X} (hA : μ Aᶜ = 0) (hmA : m A ≠ ∞) :
    Tendsto (fun N : ℝ ↦ (N : EReal) * (renyiEntropy N m μ + μ.real univ)) atTop
      (𝓝 (boltzmannEntropy m μ)) := by
  set B := toMeasurable m A
  have hB : MeasurableSet B := measurableSet_toMeasurable m A
  have hg₀ := ae_renyiGap_add_indicator_nonneg (m := m) hA le_rfl
  have heq := (eventually_ge_atTop 1).mono fun N hN ↦ (mul_renyiEntropy_add_eq hA hmA hN).symm
  by_cases hs : μ.singularPart m = 0
  · -- Without singular part, `Ent_m(μ) = ∫⁻ (ρ log ρ + 1_B) dm - m(B)`.
    have hμm : μ ≪ m := (Measure.singularPart_eq_zero μ m).1 hs
    have hent_nonneg : ∀ᵐ x ∂m,
        0 ≤ (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal + B.indicator 1 x :=
      hg₀.mono fun x hx ↦ ge_of_tendsto ((tendsto_renyiGap ENNReal.toReal_nonneg).add_const _)
        ((eventually_ge_atTop 1).mono fun N hN ↦ hx.trans
          (add_le_add_left (renyiGap_le_renyiGap ENNReal.toReal_nonneg one_pos hN) _))
    have hent : boltzmannEntropy m μ =
        ((∫⁻ x, ENNReal.ofReal ((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal
          + B.indicator 1 x) ∂m : ℝ≥0∞) : EReal) - (m.real B : EReal) := by
      have hρm := (Measure.measurable_rnDeriv μ m).ennreal_toReal
      rw [boltzmannEntropy_of_absolutelyContinuous hμm,
        ← potentialEnergy_of_nonneg_ae hent_nonneg,
        potentialEnergy_add_of_integrable (W := B.indicator 1) (by fun_prop)
          (integrable_indicator_toMeasurable hmA),
        integral_indicator_one hB, EReal.add_sub_cancel_right]
    simp only [hs, measureReal_zero_apply, mul_zero, EReal.coe_zero, add_zero] at heq
    rw [hent]
    refine Tendsto.congr' heq ?_
    exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
      (Or.inr (EReal.coe_ne_top _))).tendsto.comp <| ((continuous_coe_ennreal_ereal.tendsto _).comp
        (tendsto_lintegral_renyiGap (by fun_prop))).prodMk_nhds tendsto_const_nhds
  · -- With singular mass, `Ent_m(μ) = ⊤` and the term `N μˢ(X)` diverges.
    rw [boltzmannEntropy_of_not_absolutelyContinuous (mt (Measure.singularPart_eq_zero μ m).2 hs)]
    set c := (μ.singularPart m).real univ
    have hc : 0 < c := ENNReal.toReal_pos (by simpa using hs) (measure_ne_top _ _)
    refine EReal.tendsto_nhds_top_iff_real.2 fun y ↦ ?_
    filter_upwards [heq, eventually_gt_atTop ((y + m.real B) / c)] with N hN hNy
    rw [← hN]
    have hy : y < N * c - m.real B := by
      rw [div_lt_iff₀ hc] at hNy
      linarith
    have hcoe : ((N * c - m.real B : ℝ) : EReal) =
        0 - (m.real B : EReal) + ((N * c : ℝ) : EReal) := by
      norm_cast
      ring
    calc (y : EReal) < ((N * c - m.real B : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 hy
      _ ≤ _ := by
        rw [hcoe]
        exact add_le_add_left (EReal.sub_le_sub (EReal.coe_ennreal_nonneg _) le_rfl) _

end TauCeti
