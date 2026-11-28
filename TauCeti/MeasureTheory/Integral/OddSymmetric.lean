/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integrals of odd and even functions over symmetric domains

An odd integrand into a real normed space integrates to zero over an interval `[-R, R]`
symmetric about the origin, and more generally against any measure invariant under negation.
In particular a law invariant under negation has mean zero. An even integrand integrates over
`[-R, R]` to twice its integral from `0` to `R`.

No integrability hypothesis is needed. The substitution `t ↦ -t` is used in two ways
(`intervalIntegral.integral_comp_neg`). On `[-R, R]`, which it carries to itself, it identifies the
integral of `g` with that of `t ↦ g (-t)`; for odd `g` this is the negative of the original
integral, and in a real vector space an element equal to its own negative is zero. On `0..R` it
carries the interval to `(-R)..0`, so for even `g` the integrals over `(-R)..0` and `0..R` agree:
this is the reflection `∫ t in 0..-R, g t = -∫ t in 0..R, g t`, and splitting `[-R, R]` at `0`
gives the doubling formula. When `g` fails to be integrable, both sides of each statement are `0`.

Dually, for a negation-invariant measure `μ`, the integral of an integrable even function `φ` over
`{y | 0 ≤ g y}`, for any measurable odd `g : G → ℝ` with null zero locus, equals half of
`∫ y, φ y ∂μ` (`MeasureTheory.setIntegral_setOf_nonneg_of_even`). On a finite-dimensional real
normed space with an additive Haar measure, every nonzero continuous linear functional has null
kernel, yielding the half-space formula `MeasureTheory.setIntegral_halfSpace_of_even`.

## Main results

* `intervalIntegral.integral_eq_zero_of_odd` — `∫ t in -R..R, g t = 0` for odd `g`.
* `intervalIntegral.integral_eq_two_smul_of_even` — `∫ t in -R..R, g t = 2 • ∫ t in 0..R, g t` for
  even `g`.
* `intervalIntegral.integral_zero_neg_of_even` — `∫ t in 0..-R, g t = -∫ t in 0..R, g t` for even
  `g`.
* `MeasureTheory.integral_eq_zero_of_odd` — `∫ x, g x ∂μ = 0` for almost-everywhere odd `g`
  and a measure `μ` invariant under negation.
* `MeasureTheory.setIntegral_setOf_nonneg_of_even` — `∫ y in {y | 0 ≤ g y}, φ y ∂μ =
  (2 : ℝ)⁻¹ • ∫ y, φ y ∂μ` for integrable even `φ`, measurable odd `g` with null zero set, and
  negation-invariant `μ`.
* `MeasureTheory.setIntegral_halfSpace_of_even` — `∫ y in {y | 0 ≤ L y}, φ y ∂μ =
  (2 : ℝ)⁻¹ • ∫ y, φ y ∂μ` for integrable even `φ`, nonzero `L : E →L[ℝ] ℝ`, and additive Haar
  measure `μ`.
-/

public section

namespace intervalIntegral

/-- **An odd integrand integrates to zero over a symmetric interval.** No integrability
hypothesis is needed: the substitution `t ↦ -t` maps `[-R, R]` to itself, so the integral equals
its own negative. -/
@[simp]
theorem integral_eq_zero_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hodd : Function.Odd g) (R : ℝ) :
    ∫ t in (-R)..R, g t = 0 := by
  have hfun : (fun t => g (-t)) = fun t => -g t := funext hodd
  have hcomp : ∫ t in (-R)..R, g (-t) = ∫ t in (-R)..R, g t := by
    simp [intervalIntegral.integral_comp_neg (a := -R) (b := R) g]
  rw [hfun, intervalIntegral.integral_neg] at hcomp
  -- `hcomp` says the integral is its own negative; in a real vector space that forces `0`.
  have htwo : (2 : ℝ) • (∫ t in (-R)..R, g t) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hcomp]
    abel
  simpa using htwo

/-- The integral from `0` to `-R` of an even integrand is the negative of its integral from `0`
to `R`. No integrability hypothesis is needed. -/
theorem integral_zero_neg_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (heven : Function.Even g) (R : ℝ) :
    ∫ t in (0 : ℝ)..-R, g t = -∫ t in (0 : ℝ)..R, g t := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := R) g
  simp only [heven _, neg_zero] at h
  rw [h, intervalIntegral.integral_symm]

open MeasureTheory Set in
/-- **An even integrand integrates over `[-R, R]` to twice its integral from `0` to `R`.** Here
`R : ℝ` is arbitrary, and no integrability hypothesis is needed: since `uIcc 0 R ⊆ uIcc (-R) R`,
if `g` is not interval integrable from `0` to `R` then it is not interval integrable from `-R` to
`R`, and both sides are `0`. -/
theorem integral_eq_two_smul_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (heven : Function.Even g) (R : ℝ) :
    ∫ t in (-R)..R, g t = (2 : ℝ) • ∫ t in (0 : ℝ)..R, g t := by
  by_cases hg : IntervalIntegrable g volume 0 R
  · have h1 : IntervalIntegrable g volume (-R) 0 := by
      have := (hg.comp_sub_left 0).symm
      simpa [heven _] using this
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 hg,
      intervalIntegral.integral_symm 0 (-R), integral_zero_neg_of_even heven, neg_neg, two_smul]
  · rw [intervalIntegral.integral_undef hg, smul_zero]
    refine intervalIntegral.integral_undef fun h ↦ hg (h.mono_set (uIcc_subset_uIcc
      (mem_uIcc.2 ?_) right_mem_uIcc))
    rcases le_total 0 R with hR | hR
    · exact Or.inl ⟨by linarith, hR⟩
    · exact Or.inr ⟨hR, by linarith⟩

end intervalIntegral

namespace MeasureTheory

/-- **An almost-everywhere odd integrand integrates to zero against a measure invariant under
negation.** No integrability hypothesis is needed: the substitution `x ↦ -x` preserves the
measure, so the integral equals its own negative. Pointwise oddness gives the hypothesis via
`Filter.Eventually.of_forall`. -/
theorem integral_eq_zero_of_odd {G E : Type*} [MeasurableSpace G] [InvolutiveNeg G]
    [MeasurableNeg G] [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure G} [μ.IsNegInvariant]
    {g : G → E} (hodd : ∀ᵐ x ∂μ, g (-x) = -g x) : ∫ x, g x ∂μ = 0 := by
  have h := (Measure.measurePreserving_neg μ).integral_comp measurableEmbedding_neg g
  rw [integral_congr_ae hodd, integral_neg] at h
  rw [neg_eq_iff_add_eq_zero, ← two_smul ℝ] at h
  exact (smul_eq_zero.1 h).resolve_left two_ne_zero

/-- Integrating an integrable even function against a negation-invariant measure over
`{y | 0 ≤ g y}`, where `g : G → ℝ` is measurable, odd, and vanishes only on a null set, yields
half its full-space integral. -/
theorem setIntegral_setOf_nonneg_of_even {G F : Type*} [MeasurableSpace G] [InvolutiveNeg G]
    [MeasurableNeg G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure G} [μ.IsNegInvariant] {φ : G → F} (hφ : Integrable φ μ)
    (heven : Function.Even φ) {g : G → ℝ} (hg : Measurable g) (hodd : Function.Odd g)
    (hzero : μ {y | g y = 0} = 0) :
    ∫ y in {y | 0 ≤ g y}, φ y ∂μ = (2 : ℝ)⁻¹ • ∫ y, φ y ∂μ := by
  let N : Set G := {y | g y < 0}
  have hNm : MeasurableSet N := measurableSet_lt hg measurable_const
  have hNc : Nᶜ = {y | 0 ≤ g y} := by ext y; simp [N]
  have hP_union : {y | 0 ≤ g y} = {y | 0 < g y} ∪ {y | g y = 0} := by
    ext y; simp [le_iff_lt_or_eq, eq_comm]
  have heq_PN : ∫ y in Nᶜ, φ y ∂μ = ∫ y in N, φ y ∂μ := by
    rw [hNc, setIntegral_congr_set
      (hP_union ▸ union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr hzero)),
      ← (Measure.measurePreserving_neg μ).setIntegral_preimage_emb
        (MeasurableEquiv.neg G).measurableEmbedding φ {y | 0 < g y}]
    simp [N, hodd _, heven _]
  have hsum := integral_add_compl hNm hφ
  rw [← heq_PN, ← two_smul ℝ] at hsum
  rw [← hNc, ← hsum, inv_smul_smul₀ two_ne_zero]

/-- Integrating an integrable even function against an additive Haar measure over the closed
half-space `{y : E | 0 ≤ L y}` defined by any nonzero continuous linear functional
`L : E →L[ℝ] ℝ` yields half its full-space integral. -/
theorem setIntegral_halfSpace_of_even {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E} [μ.IsAddHaarMeasure]
    {φ : E → F} (hφ : Integrable φ μ) (heven : Function.Even φ)
    {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∫ y in {y : E | 0 ≤ L y}, φ y ∂μ = (2 : ℝ)⁻¹ • ∫ y, φ y ∂μ := by
  have hker : μ {y : E | L y = 0} = 0 := by
    have hneq : LinearMap.ker L.toLinearMap ≠ ⊤ := by
      rw [ne_eq, LinearMap.ker_eq_top]
      exact fun h ↦ hL (ContinuousLinearMap.coe_inj.mp h)
    have hset : ({y : E | L y = 0} : Set E) = (LinearMap.ker L.toLinearMap : Set E) := by
      ext y; simp
    exact hset ▸ Measure.addHaar_submodule μ (LinearMap.ker L.toLinearMap) hneq
  exact setIntegral_setOf_nonneg_of_even hφ heven L.continuous.measurable (fun y ↦ map_neg L y) hker

end MeasureTheory

end
