/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Bounded approximation of BMO multipliers

Lipschitz postcomposition preserves bounded mean oscillation, with the bound
`‖φ ∘ b‖_{BMO} ≤ 2 Lip(φ) ‖b‖_{BMO}`. In particular, truncating a real BMO function to
`[-n, n]` gives bounded multipliers with a uniform BMO bound.

`TauCeti.MemBMO.exists_bounded_approximation` supplies these multipliers. They eventually agree
with the original function at each point, and converge after scalar multiplication by any
measurable normed-space-valued function `f` for which `b • f` lies in a finite-exponent `Lᵖ`
space. This permits passage from bounded multipliers to BMO multipliers in commutator estimates.
This is not approximation in the BMO seminorm, which need not hold.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.5: approximation of BMO
  multipliers in the Coifman–Rochberg–Weiss commutator theorem.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace LipschitzWith

variable {X F G : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [ProperSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {b : X → F} {φ : F → G} {K : ℝ≥0}

/-- Lipschitz postcomposition increases the BMO seminorm by at most twice the Lipschitz
constant. No normalization of the outer map at zero is needed. -/
theorem bmoSeminorm_comp_le (hφ : LipschitzWith K φ) (hb : LocallyIntegrable b μ) :
    TauCeti.bmoSeminorm (φ ∘ b) μ ≤ 2 * K * TauCeti.bmoSeminorm b μ := by
  have hloc : LocallyIntegrable (φ ∘ b) μ :=
    locallyIntegrableOn_univ.1 ((locallyIntegrableOn_univ.2 hb).comp_lipschitz hφ)
  refine TauCeti.bmoSeminorm_le fun c r => ?_
  have hi := (hloc.integrableOn_isCompact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall
  calc
    ⨍⁻ y in ball c r, ‖φ (b y) - ⨍ z in ball c r, φ (b z) ∂μ‖ₑ ∂μ ≤
        2 * ⨍⁻ y in ball c r, ‖φ (b y) - φ (⨍ z in ball c r, b z ∂μ)‖ₑ ∂μ :=
      TauCeti.setLAverage_enorm_sub_setAverage_le hi _
    _ ≤ 2 * ⨍⁻ y in ball c r, (K : ℝ≥0∞) * ‖b y - ⨍ z in ball c r, b z ∂μ‖ₑ ∂μ := by
      gcongr
      exact .of_forall fun y => by
        simpa only [edist_eq_enorm_sub] using hφ (b y) (⨍ z in ball c r, b z ∂μ)
    _ = 2 * K * ⨍⁻ y in ball c r, ‖b y - ⨍ z in ball c r, b z ∂μ‖ₑ ∂μ := by
      rw [TauCeti.laverage_const_mul ENNReal.coe_ne_top, mul_assoc]
    _ ≤ 2 * K * TauCeti.bmoSeminorm b μ := by
      gcongr
      exact TauCeti.setLAverage_enorm_sub_setAverage_le_bmoSeminorm b μ c r

end LipschitzWith

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [ProperSpace X]
  {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- A Lipschitz function of a BMO function is again BMO. -/
theorem MemBMO.comp_lipschitz {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {b : X → F} (hb : MemBMO b μ) {φ : F → G} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    MemBMO (φ ∘ b) μ := by
  apply memBMO_iff.2
  refine ⟨locallyIntegrableOn_univ.1
    ((locallyIntegrableOn_univ.2 hb.locallyIntegrable).comp_lipschitz hφ), ?_⟩
  exact (hφ.bmoSeminorm_comp_le hb.locallyIntegrable).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hb.bmoSeminorm_lt_top)

/-- Every real BMO multiplier has bounded BMO approximants with uniformly controlled seminorm.
They eventually agree with the multiplier at each point. Multiplication by them converges in
any finite-exponent `Lᵖ` space whenever multiplication by the original multiplier lies there.
No convergence in the BMO seminorm is asserted. -/
theorem MemBMO.exists_bounded_approximation [SecondCountableTopology X]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {b : X → ℝ}
    (hb : MemBMO b μ) :
    ∃ g : ℕ → X → ℝ,
      (∀ n, MemLp (g n) ∞ μ ∧ MemBMO (g n) μ ∧ bmoSeminorm (g n) μ ≤ 2 * bmoSeminorm b μ) ∧
      (∀ x, ∀ᶠ n in atTop, g n x = b x) ∧
      ∀ (f : X → F) (p : ℝ≥0∞), p ≠ ∞ → AEStronglyMeasurable f μ →
        MemLp (fun x => b x • f x) p μ →
        Tendsto (fun n => eLpNorm (fun x => g n x • f x - b x • f x) p μ) atTop (𝓝 0) := by
  let φ (n : ℕ) (t : ℝ) := max (-(n : ℝ)) (min (n : ℝ) t)
  have hφ (n : ℕ) : LipschitzWith 1 (φ n) :=
    (LipschitzWith.id.const_min (n : ℝ)).const_max (-(n : ℝ))
  have hφ0 (n : ℕ) : φ n 0 = 0 := by simp [φ]
  have hnorm (n : ℕ) (t : ℝ) : ‖φ n t‖ ≤ ‖t‖ := by
    simpa [hφ0] using (hφ n).norm_sub_le t 0
  have hlim (t : ℝ) : ∀ᶠ n : ℕ in atTop, φ n t = t := by
    obtain ⟨N, hN⟩ := exists_nat_gt |t|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnt : |t| ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
    dsimp only [φ]
    rw [min_eq_right (abs_le.mp hnt).2, max_eq_right (abs_le.mp hnt).1]
  refine ⟨fun n => φ n ∘ b, ?_, fun x => hlim (b x), ?_⟩
  · intro n
    have hmeas := (hφ n).continuous.comp_aestronglyMeasurable
      hb.locallyIntegrable.aestronglyMeasurable
    refine ⟨memLp_top_of_bound hmeas (n : ℝ) (.of_forall fun x => ?_),
      hb.comp_lipschitz (hφ n), ?_⟩
    · rw [Real.norm_eq_abs, abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    · simpa using (hφ n).bmoSeminorm_comp_le hb.locallyIntegrable
  · intro f p hp hf hbf
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 2) hp
      (.of_forall fun n => ((hφ n).continuous.comp_aestronglyMeasurable
        hb.locallyIntegrable.aestronglyMeasurable).smul hf) hbf
      (.of_forall fun n => .of_forall fun x => ?_)
      (.of_forall fun x => tendsto_const_nhds.congr' ((hlim (b x)).mono fun n hn => by
        simp only [Function.comp_apply, hn]))
    simp only [ENNReal.coe_ofNat]
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖φ n (b x) • f x - b x • f x‖ ≤ ‖φ n (b x) • f x‖ + ‖b x • f x‖ := norm_sub_le _ _
      _ ≤ ‖b x • f x‖ + ‖b x • f x‖ := by simp only [norm_smul]; gcongr; exact hnorm n (b x)
      _ = 2 * ‖b x • f x‖ := (two_mul _).symm

end TauCeti
