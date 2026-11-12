/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Algebra.Order.Group.MinMax
import TauCeti.Data.Real.Truncation
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Bounded approximation of BMO multipliers

Lipschitz postcomposition preserves bounded mean oscillation, with the bound
`‖φ ∘ b‖_{BMO} ≤ 2 Lip(φ) ‖b‖_{BMO}`. In particular, truncating a real BMO function to
`[-n, n]` gives bounded multipliers with a uniform BMO bound.

`TauCeti.MemBMO.exists_memLp_top_bmoSeminorm_le_tendsto_eLpNorm_smul_sub` supplies these
multipliers, whose pointwise norms are bounded by that of the original function. They eventually
agree with the original function at each point, and converge after scalar multiplication by any
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

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [SecondCountableTopology X] {μ : Measure X}

/-- Every real BMO multiplier has bounded BMO approximants with uniformly controlled seminorm.
Their pointwise norms are bounded by that of the multiplier, and they eventually agree with it
at each point. Multiplication by them converges in
any finite-exponent `Lᵖ` space whenever multiplication by the original multiplier lies there.
No convergence in the BMO seminorm is asserted. -/
theorem MemBMO.exists_memLp_top_bmoSeminorm_le_tendsto_eLpNorm_smul_sub
    {b : X → ℝ} (hb : MemBMO b μ) :
    ∃ g : ℕ → X → ℝ,
      (∀ n, MemLp (g n) ∞ μ ∧ MemBMO (g n) μ ∧
        bmoSeminorm (g n) μ ≤ 2 * bmoSeminorm b μ ∧ ∀ x, ‖g n x‖ ≤ ‖b x‖) ∧
      (∀ x, ∀ᶠ n in atTop, g n x = b x) ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (f : X → F) (p : ℝ≥0∞), p ≠ ∞ → AEStronglyMeasurable f μ →
        MemLp (fun x => b x • f x) p μ →
        Tendsto (fun n => eLpNorm (fun x => g n x • f x - b x • f x) p μ) atTop (𝓝 0) := by
  let φ (n : ℕ) (t : ℝ) := max (-(n : ℝ)) (min (n : ℝ) t)
  have hφ (n : ℕ) : LipschitzWith 1 (φ n) :=
    (LipschitzWith.id.const_min (n : ℝ)).const_max (-(n : ℝ))
  have hnorm (n : ℕ) (t : ℝ) : ‖φ n t‖ ≤ ‖t‖ := by
    simpa only [φ, Real.norm_eq_abs] using abs_max_min_le_abs n.cast_nonneg t
  have hlim (t : ℝ) : ∀ᶠ n : ℕ in atTop, φ n t = t := by
    simpa only [φ, min_comm] using Real.eventually_max_neg_min_eq t
  refine ⟨fun n => φ n ∘ b, ?_, fun x => hlim (b x), ?_⟩
  · intro n
    have hmeas := (hφ n).continuous.comp_aestronglyMeasurable
      hb.locallyIntegrable.aestronglyMeasurable
    have hsemi : bmoSeminorm (φ n ∘ b) μ ≤ 2 * bmoSeminorm b μ := by
      simpa using (hφ n).bmoSeminorm_comp_le hb.locallyIntegrable.aestronglyMeasurable
    refine ⟨memLp_top_of_bound hmeas (n : ℝ) (.of_forall fun x => ?_),
      memBMO_iff.2 ⟨hb.locallyIntegrable.mono hmeas (.of_forall fun x => hnorm n (b x)),
        hsemi.trans_lt (ENNReal.mul_lt_top (by finiteness) hb.bmoSeminorm_lt_top)⟩,
      hsemi, fun x => hnorm n (b x)⟩
    simpa only [φ, Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (n.cast_nonneg : (0 : ℝ) ≤ n)]
      using abs_max_min_le (n : ℝ) (b x)
  · intro F _ _ f p hp hf hbf
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
