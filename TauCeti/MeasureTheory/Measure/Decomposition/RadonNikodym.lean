/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Normalizing by a Radon–Nikodym derivative

Let `μ ≪ ν` and let `k = dμ/dν`. A function `f` with `‖f‖ ≤ c k` at `ν`-almost every point has a
density with respect to `μ`: the quotient `f / k` is bounded by `c` at `μ`-almost every point
(`MeasureTheory.Measure.ae_enorm_inv_toReal_rnDeriv_smul_le`), and `k (f / k) = f` at `ν`-almost
every point (`MeasureTheory.Measure.toReal_rnDeriv_smul_inv_smul_ae_eq`), since `f` vanishes where
`k` does. This is how a density with respect to a reference measure `ν` dominating several
measures becomes a density with respect to one of them.

The Radon–Nikodym derivative of a locally finite measure is locally integrable
(`MeasureTheory.Measure.locallyIntegrable_toReal_rnDeriv`).

## Main results

* `MeasureTheory.Measure.locallyIntegrable_toReal_rnDeriv`: `dμ/dν` is locally integrable.
* `MeasureTheory.Measure.ae_enorm_inv_toReal_rnDeriv_smul_le`: `‖f / k‖ ≤ c` `μ`-a.e.
* `MeasureTheory.Measure.toReal_rnDeriv_smul_inv_smul_ae_eq`: `k (f / k) = f` `ν`-a.e.
-/

public section

open Filter
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α G : Type*} [MeasurableSpace α] {μ ν : Measure α} [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f : α → G} {c : ℝ≥0∞}

/-- The Radon–Nikodym derivative of a locally finite measure is locally integrable. -/
theorem locallyIntegrable_toReal_rnDeriv [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal) ν := fun x =>
  let ⟨U, hU, hμU⟩ := μ.finiteAt_nhds x
  ⟨U, hU, integrableOn_toReal_rnDeriv hμU.ne⟩

/-- If `‖f‖ ≤ c k` at `ν`-almost every point, with `k = dμ/dν` and `μ ≪ ν`, then `f / k` is
bounded by `c` at `μ`-almost every point. -/
theorem ae_enorm_inv_toReal_rnDeriv_smul_le (hμν : μ ≪ ν)
    (hf : ∀ᵐ x ∂ν, ‖f x‖ₑ ≤ c * μ.rnDeriv ν x) :
    ∀ᵐ x ∂μ, ‖(μ.rnDeriv ν x).toReal⁻¹ • f x‖ₑ ≤ c := by
  refine hμν.ae_le (hf.mono fun x hx => ?_)
  rcases eq_or_ne (μ.rnDeriv ν x).toReal 0 with h0 | h0
  · simp [h0]
  have hk := ENNReal.toReal_ne_zero.1 h0
  rw [enorm_smul, Real.enorm_eq_ofReal (inv_nonneg.2 ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hk.1 hk.2), ENNReal.ofReal_toReal hk.2]
  calc (μ.rnDeriv ν x)⁻¹ * ‖f x‖ₑ ≤ (μ.rnDeriv ν x)⁻¹ * (c * μ.rnDeriv ν x) := by gcongr
    _ = c := by rw [mul_comm c, ← mul_assoc, ENNReal.inv_mul_cancel hk.1 hk.2, one_mul]

/-- If `‖f‖ ≤ c k` at `ν`-almost every point, with `k = dμ/dν`, then `k (f / k) = f` at
`ν`-almost every point. -/
theorem toReal_rnDeriv_smul_inv_smul_ae_eq [SigmaFinite μ]
    (hf : ∀ᵐ x ∂ν, ‖f x‖ₑ ≤ c * μ.rnDeriv ν x) :
    (fun x => (μ.rnDeriv ν x).toReal • ((μ.rnDeriv ν x).toReal⁻¹ • f x)) =ᵐ[ν] f := by
  filter_upwards [hf, rnDeriv_lt_top μ ν] with x hx hk
  rcases eq_or_ne (μ.rnDeriv ν x).toReal 0 with h0 | h0
  · have : μ.rnDeriv ν x = 0 := (ENNReal.toReal_eq_zero_iff _).1 h0 |>.resolve_right hk.ne
    have : f x = 0 := by simpa [this] using hx
    simp [h0, this]
  · exact smul_inv_smul₀ h0 _

end MeasureTheory.Measure
