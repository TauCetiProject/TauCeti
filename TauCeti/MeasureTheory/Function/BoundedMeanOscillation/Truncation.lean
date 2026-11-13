/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping
public import TauCeti.Data.Real.Truncation

/-!
# Bounded approximation of BMO multipliers

Lipschitz postcomposition preserves bounded and vanishing mean oscillation, with the bound
`‖φ ∘ b‖_{BMO} ≤ 2 Lip(φ) ‖b‖_{BMO}`. In particular, clipping a real BMO function to
`[-M, M]` gives bounded multipliers with a uniform BMO bound (`TauCeti.bmoSeminorm_max_min_le`),
and preserves BMO and VMO for nonnegative heights (`TauCeti.MemBMO.max_min`,
`TauCeti.MemVMO.max_min`). The VMO modulus has the same uniform bound
(`TauCeti.vmoModulus_max_min_le`).

These explicit multipliers have pointwise norm at most `|M|` (`TauCeti.abs_max_min_le`),
and for nonnegative heights at most the original norm (`TauCeti.abs_max_min_le_abs`). They are
essentially bounded (`MeasureTheory.AEStronglyMeasurable.memLp_top_max_min`) and eventually agree
with the original function at each point as natural heights tend to infinity
(`Real.eventually_max_neg_min_eq`). Their scalar products converge in finite-exponent `Lᵖ`
spaces whenever the original product lies there (`TauCeti.tendsto_eLpNorm_max_min_smul_sub`).
These facts permit passage from bounded multipliers to BMO multipliers in commutator estimates.
This is not approximation in the BMO seminorm, which need not hold.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.5: approximation of BMO
  multipliers in the Coifman–Rochberg–Weiss commutator theorem.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] {μ : Measure X} {b : X → ℝ}

/-- Symmetric clipping at any real height increases the BMO seminorm by at most a factor of
two. No finiteness assumption on the measure is needed. -/
theorem bmoSeminorm_max_min_le (hb : AEStronglyMeasurable b μ) (M : ℝ) :
    bmoSeminorm (fun x ↦ max (-M) (min M (b x))) μ ≤ 2 * bmoSeminorm b μ := by
  have hφ : LipschitzWith 1 (fun t : ℝ ↦ max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  simpa [Function.comp_def] using hφ.bmoSeminorm_comp_le hb

/-- Symmetric clipping at any real height increases the VMO modulus by at most a factor of
two, uniformly in the radius. -/
theorem vmoModulus_max_min_le (hb : AEStronglyMeasurable b μ) (M r : ℝ) :
    vmoModulus (fun x ↦ max (-M) (min M (b x))) μ r ≤ 2 * vmoModulus b μ r := by
  have hφ : LipschitzWith 1 (fun t : ℝ ↦ max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  simpa [Function.comp_def] using hφ.vmoModulus_comp_le hb r

/-- Clipping a real BMO function at a nonnegative height preserves BMO, for any measure. -/
theorem MemBMO.max_min [SecondCountableTopology X] (hb : MemBMO b μ) {M : ℝ} (hM : 0 ≤ M) :
    MemBMO (fun x ↦ max (-M) (min M (b x))) μ := by
  have hcont : Continuous (fun t : ℝ ↦ max (-M) (min M t)) := by fun_prop
  apply memBMO_iff.2
  refine ⟨hb.locallyIntegrable.mono
    (hcont.comp_aestronglyMeasurable hb.locallyIntegrable.aestronglyMeasurable)
    (.of_forall fun x ↦ abs_max_min_le_abs hM (b x)), ?_⟩
  exact (bmoSeminorm_max_min_le hb.locallyIntegrable.aestronglyMeasurable M).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hb.bmoSeminorm_lt_top)

/-- Clipping a real VMO function at a nonnegative height preserves VMO, for any measure. -/
theorem MemVMO.max_min [SecondCountableTopology X] (hb : MemVMO b μ) {M : ℝ} (hM : 0 ≤ M) :
    MemVMO (fun x ↦ max (-M) (min M (b x))) μ := by
  apply memVMO_iff_tendsto.2
  refine ⟨hb.memBMO.max_min hM, ?_⟩
  have hlim := ENNReal.Tendsto.const_mul hb.tendsto_vmoModulus
    (Or.inr (show (2 : ℝ≥0∞) ≠ ∞ from by finiteness))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hlim) (fun _ ↦ zero_le)
  exact fun r ↦ vmoModulus_max_min_le hb.memBMO.locallyIntegrable.aestronglyMeasurable M r

end TauCeti
