/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.RunningMaximum
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Integral.Lebesgue.Supremum

/-!
# Polynomial-growth prices along geometric Brownian motion

A uniform bound `|C(s,t)| ≤ A (1 + s^p)` gives a finite square-maximal moment along a
positive geometric Brownian stock on a finite horizon. The exponent `p` may be any real
number: negative moments are available too. The same estimate gives square integrability
at arbitrary random times in the horizon, provided the sampled value is measurable, and
square integrability for the time-product measure.

Apply these results to a candidate price `C` and to `s * ∂C/∂s` to obtain the moment
and expected-energy bounds used in verifying a delta hedge. Measurability is stated
separately; random times need not be stopping times for these estimates. No stochastic
integral, self-financing identity or martingale property is inferred from growth alone.

The maximal estimate reuses
`IsFilteredPreBrownianReal.lintegral_iSup_rpow_geometricBrownianMotion_lt_top`.

## References

* I. Karatzas, S. E. Shreve, *Methods of Mathematical Finance*, Springer, 1998, §2.4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {s A : ℝ} {T : ℝ≥0} {C : ℝ → ℝ → ℝ}

/-- A polynomial-growth price evaluated along a positive geometric Brownian stock has a
finite square-maximal moment on every finite horizon. No measurability of the price is needed
for this lower-integral estimate; applications to `L²` also require measurability. -/
theorem lintegral_iSup_sq_price_geometricBrownianMotion_lt_top
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 < s) (μ σ p : ℝ)
    (hC : ∀ x > 0, ∀ t : ℝ≥0, t ≤ T → |C x t| ≤ A * (1 + x ^ p)) :
    ∫⁻ ω, ⨆ t ≤ T,
      ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t ω) t ^ 2) ∂P < ∞ := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hA : 0 ≤ A := by
    have hg : |C 1 0| ≤ A * (1 + 1) := by
      simpa using hC 1 one_pos 0 (by positivity)
    linarith [abs_nonneg (C 1 0)]
  have hmax := hW.lintegral_iSup_rpow_geometricBrownianMotion_lt_top hcont hs.le μ σ (p * 2)
  have hbound (ω : Ω) (t : ℝ≥0) (ht : t ≤ T) :
      C (geometricBrownianMotion s μ σ W t ω) t ^ 2 ≤
        2 * A ^ 2 * (1 + geometricBrownianMotion s μ σ W t ω ^ (p * 2)) := by
    have hS := geometricBrownianMotion_pos hs μ σ W t ω
    have hg := hC _ hS t ht
    have hr := rpow_nonneg hS.le p
    have hsq := sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA (by positivity)) |>.2 hg
    rw [sq_abs] at hsq
    rw [rpow_mul hS.le, rpow_two]
    nlinarith [sq_nonneg (geometricBrownianMotion s μ σ W t ω ^ p - 1), sq_nonneg A]
  have hadd : ∫⁻ ω, ⨆ t ≤ T,
      ENNReal.ofReal (1 + geometricBrownianMotion s μ σ W t ω ^ (p * 2)) ∂P < ∞ := by
    calc
      _ ≤ ∫⁻ ω, 1 + ⨆ t ≤ T,
          ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω ^ (p * 2)) ∂P := by
        refine lintegral_mono fun ω ↦ iSup₂_le fun t ht ↦ ?_
        rw [ENNReal.ofReal_add zero_le_one
          (rpow_nonneg (geometricBrownianMotion_pos hs μ σ W t ω).le _), ENNReal.ofReal_one]
        exact add_le_add le_rfl (le_iSup₂ (f := fun (t : ℝ≥0) (_ : t ≤ T) ↦
          ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω ^ (p * 2))) t ht)
      _ = 1 + ∫⁻ ω, ⨆ t ≤ T,
          ENNReal.ofReal (geometricBrownianMotion s μ σ W t ω ^ (p * 2)) ∂P := by
        rw [lintegral_add_left measurable_const]
        simp
      _ < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hmax⟩
  exact lintegral_iSup_ofReal_lt_top_of_le_mul (by positivity) hbound hadd

/-- Polynomial growth gives an `L²` value at any random time bounded by the horizon. The
sampled value must be a.e. strongly measurable, but the time need not be a stopping time. -/
theorem memLp_price_geometricBrownianMotion_randomTime
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 < s) (μ σ p : ℝ)
    (hC : ∀ x > 0, ∀ t : ℝ≥0, t ≤ T → |C x t| ≤ A * (1 + x ^ p))
    {τ : Ω → ℝ≥0} (hτ : ∀ᵐ ω ∂P, τ ω ≤ T)
    (hm : AEStronglyMeasurable
      (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ ω) ω) (τ ω)) P) :
    MemLp (fun ω ↦ C (geometricBrownianMotion s μ σ W (τ ω) ω) (τ ω)) 2 P := by
  apply (memLp_two_iff_integrable_sq hm).2
  refine ⟨hm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_sq]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_)
    (hW.lintegral_iSup_sq_price_geometricBrownianMotion_lt_top hcont hs μ σ p hC)
  filter_upwards [hτ] with ω hω
  exact le_iSup₂ (f := fun t _ ↦
    ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t ω) t ^ 2)) (τ ω) hω

/-- Polynomial-growth price coefficients belong to `L²` of every finite time-product
measure supported in the horizon. In particular this supplies expected square-energy bounds
when applied to the coefficient `s * ∂C/∂s`. -/
theorem memLp_price_geometricBrownianMotion_prod
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ W u ω) (Ioi t) t)
    (hs : 0 < s) (μ σ p : ℝ)
    (hC : ∀ x > 0, ∀ t : ℝ≥0, t ≤ T → |C x t| ≤ A * (1 + x ^ p))
    {ν : Measure ℝ≥0} [IsFiniteMeasure ν] (hν : ∀ᵐ t ∂ν, t ≤ T)
    (hm : AEStronglyMeasurable
      (fun z : ℝ≥0 × Ω ↦ C (geometricBrownianMotion s μ σ W z.1 z.2) z.1) (ν.prod P)) :
    MemLp (fun z : ℝ≥0 × Ω ↦ C (geometricBrownianMotion s μ σ W z.1 z.2) z.1)
      2 (ν.prod P) := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  apply (memLp_two_iff_integrable_sq hm).2
  refine ⟨hm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_sq]
  have hmax := hW.lintegral_iSup_sq_price_geometricBrownianMotion_lt_top hcont hs μ σ p hC
  calc
    _ ≤ ∫⁻ z : ℝ≥0 × Ω, ⨆ t ≤ T,
        ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t z.2) t ^ 2) ∂ν.prod P := by
      refine lintegral_mono_ae ?_
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν] with z hz
      exact le_iSup₂ (f := fun t _ ↦
        ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t z.2) t ^ 2)) z.1 hz
    _ ≤ ∫⁻ _ : ℝ≥0, ∫⁻ ω, ⨆ t ≤ T,
        ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t ω) t ^ 2) ∂P ∂ν :=
      lintegral_prod_le _
    _ = ν univ * ∫⁻ ω, ⨆ t ≤ T,
        ENNReal.ofReal (C (geometricBrownianMotion s μ σ W t ω) t ^ 2) ∂P := by
      rw [lintegral_const, mul_comm]
    _ < ∞ := ENNReal.mul_lt_top (measure_lt_top _ _) hmax

end TauCeti.Probability.IsFilteredPreBrownianReal
