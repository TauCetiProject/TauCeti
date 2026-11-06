/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Prices reconstructed from bounded weighted log-spot maps

A bounded parabolic Hölder map `u(y,t)` represents a price of linear growth by
`C(s,t) = (1+s) u(log s,t)` for positive spot. `weightedLogSpotPrice` performs this
reconstruction, using the canonical clamped extension in time. It preserves continuity
on the closed time slab and twice continuous spatial differentiability, and has explicit
linear-growth bounds for both the price and its dollar delta `s C_s`.

The pricing-operator identity transports the backward equation for the bounded map to
the financial pricing equation. This is a change-of-variables result, not an existence
or stochastic replication theorem. In particular, no ellipticity or moment hypotheses
are needed here. Terminal data are transported pointwise, without a smoothness claim
at zero spot.

## References

* P. Wilmott, S. Howison, J. Dewynne, *The Mathematics of Financial Derivatives*,
  Cambridge University Press, 1995, §5.4.
-/

public section
noncomputable section

open Real Set Filter Topology
open scoped NNReal
open TauCeti.ParabolicSpaceTime TauCeti.ParabolicC2HolderSpace

namespace TauCeti.Finance

variable {α : ℝ≥0} {a b : ℝ} {hab : a < b}

/-- The price represented by a bounded weighted log-spot map. Time is clamped to `[a,b]`;
the financial interpretation of this total function is restricted to positive spots. -/
def weightedLogSpotPrice (u : ParabolicC2HolderSpace α ℝ ℝ hab) (s t : ℝ) : ℝ :=
  (1 + s) * timeExtension hab.le u (log s) t

/-- Reconstruction in terms of the canonical time extension at any time. -/
theorem weightedLogSpotPrice_def (u : ParabolicC2HolderSpace α ℝ ℝ hab) (s t : ℝ) :
    weightedLogSpotPrice u s t = (1 + s) * timeExtension hab.le u (log s) t := (rfl)

/-- Reconstruction at a time in the closed slab. -/
@[simp]
theorem weightedLogSpotPrice_of_mem (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) (t : Icc a b) :
    weightedLogSpotPrice u s t = (1 + s) * u (slabMk (log s) t) := by
  rw [weightedLogSpotPrice_def, timeExtension_of_mem]

/-- Weighting and unweighting in log-spot coordinates are inverse operations. -/
@[simp]
theorem weightedLogSpotPrice_exp_div (u : ParabolicC2HolderSpace α ℝ ℝ hab) (y t : ℝ) :
    weightedLogSpotPrice u (exp y) t / (1 + exp y) = timeExtension hab.le u y t := by
  rw [weightedLogSpotPrice_def, log_exp, mul_div_cancel_left₀ _ (by positivity)]

/-- The reconstructed price has linear growth, uniformly over all times. -/
theorem abs_weightedLogSpotPrice_le (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    |weightedLogSpotPrice u s t| ≤ ‖u‖ * (1 + s) := by
  rw [weightedLogSpotPrice_def, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + s), mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((norm_timeExtension_le hab.le (valueL u) t (log s)).trans (norm_valueL_le u))
    (by positivity)

/-- The reconstructed price is jointly continuous at positive spot, including the time
endpoints. The canonical time extension is continuous even outside the slab. -/
theorem continuousOn_weightedLogSpotPrice (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn (Function.uncurry (weightedLogSpotPrice u)) (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have hc := continuous_timeExtension hab.le (valueL u).continuous
  intro p hp
  apply ContinuousAt.continuousWithinAt
  exact (continuous_const.add continuous_fst).continuousAt.mul
    (hc.continuousAt.comp (continuous_snd.continuousAt.prodMk
      ((continuousAt_log (ne_of_gt hp.1)).comp continuous_fst.continuousAt)))

/-- Every spatial slice of the price is twice continuously differentiable at positive spot. -/
theorem contDiffOn_weightedLogSpotPrice (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (t : Icc a b) : ContDiffOn ℝ 2 (fun s => weightedLogSpotPrice u s t) (Ioi 0) := by
  simp_rw [weightedLogSpotPrice_of_mem]
  exact (contDiffOn_const.add contDiffOn_id).mul
    ((u.contDiff_spatialSlice t).comp_contDiffOn
      (contDiffOn_log.mono (fun _ hx => ne_of_gt hx)))

/-- The spot derivative, expressed through the bounded spatial gradient in log spot. -/
theorem hasDerivAt_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) :
    HasDerivAt (fun x => weightedLogSpotPrice u x t)
      (u (slabMk (log s) t) + (1 + s) / s *
        spatialFDerivL u (slabMk (log s) t) 1) s := by
  have h := (u.hasSpatialFDerivAt t (log s)).hasDerivAt.comp s (hasDerivAt_log hs.ne')
  convert ((hasDerivAt_id s).const_add 1).mul h using 1
  · ext x
    simp [weightedLogSpotPrice_of_mem]
  · simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- The ordinary spot derivative in terms of the value and spatial gradient fields. -/
theorem deriv_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) :
    deriv (fun x => weightedLogSpotPrice u x t) s =
      u (slabMk (log s) t) + (1 + s) / s * spatialFDerivL u (slabMk (log s) t) 1 :=
  (hasDerivAt_weightedLogSpotPrice_spot u hs t).deriv

/-- The second spot derivative in terms of the spatial gradient and Hessian fields. -/
theorem deriv_deriv_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) :
    deriv (deriv fun x => weightedLogSpotPrice u x t) s =
      ((s - 1) * spatialFDerivL u (slabMk (log s) t) 1 +
        (1 + s) * spatialSecondFDerivL u (slabMk (log s) t) 1 1) / s ^ 2 := by
  have hv := (u.hasSpatialFDerivAt t (log s)).hasDerivAt.comp s (hasDerivAt_log hs.ne')
  have hd : HasDerivAt (fun x => spatialFDerivL u (slabMk (log x) t) 1)
      (spatialSecondFDerivL u (slabMk (log s) t) 1 1 / s) s := by
    convert ((u.hasSpatialSecondFDerivAt t (log s)).hasDerivAt.clm_apply
      (hasDerivAt_const (log s) (1 : ℝ))).comp s (hasDerivAt_log hs.ne') using 1
    · rfl
    · simp [div_eq_mul_inv]
  have heq : (deriv fun x => weightedLogSpotPrice u x t) =ᶠ[𝓝 s]
      fun x => u (slabMk (log x) t) + (1 + x) / x *
        spatialFDerivL u (slabMk (log x) t) 1 := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact deriv_weightedLogSpotPrice_spot u hx t
  rw [heq.deriv_eq]
  convert (hv.add ((((hasDerivAt_id s).const_add 1).div
    (hasDerivAt_id s) hs.ne').mul hd)).deriv using 1
  · rfl
  · simp only [Pi.div_apply, id_eq]
    field_simp
    ring

/-- The dollar delta has linear growth with an explicit bound from the value and gradient
norms. This bound is suitable for moment-based integrability criteria. -/
theorem abs_mul_deriv_weightedLogSpotPrice_le (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) :
    |s * deriv (fun x => weightedLogSpotPrice u x t) s| ≤
      (‖valueL u‖ + ‖spatialFDerivL u‖) * (1 + s) := by
  rw [deriv_weightedLogSpotPrice_spot u hs t]
  have heq : s * (u (slabMk (log s) t) + (1 + s) / s *
      spatialFDerivL u (slabMk (log s) t) 1) =
      s * u (slabMk (log s) t) + (1 + s) * spatialFDerivL u (slabMk (log s) t) 1 := by
    field_simp
  rw [heq]
  have hv : |u (slabMk (log s) t)| ≤ ‖valueL u‖ := (valueL u).norm_coe_le_norm _
  have hd : |spatialFDerivL u (slabMk (log s) t) 1| ≤ ‖spatialFDerivL u‖ := by
    simpa using (spatialFDerivL u (slabMk (log s) t)).le_of_opNorm_le
      ((spatialFDerivL u).norm_coe_le_norm _) (1 : ℝ)
  calc
    _ ≤ |s * u (slabMk (log s) t)| +
        |(1 + s) * spatialFDerivL u (slabMk (log s) t) 1| := abs_add_le _ _
    _ ≤ s * ‖valueL u‖ + (1 + s) * ‖spatialFDerivL u‖ := by
      simp only [abs_mul, abs_of_pos hs, abs_of_pos (by positivity : 0 < 1 + s)]
      gcongr
    _ ≤ _ := by nlinarith [norm_nonneg (valueL u)]

/-- The time derivative within the closed slab, including its one-sided endpoint values. -/
theorem hasDerivWithinAt_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) (t : Icc a b) :
    HasDerivWithinAt (weightedLogSpotPrice u s)
      ((1 + s) * timeDerivL u (slabMk (log s) t)) (Icc a b) t := by
  convert (u.hasTimeDerivWithinAt (log s) t).const_mul (1 + s) using 1
  ext v
  simp only [weightedLogSpotPrice_def]

/-- The within-slab time derivative equals the recorded time derivative field, also at endpoints. -/
@[simp]
theorem derivWithin_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) (t : Icc a b) :
    derivWithin (weightedLogSpotPrice u s) (Icc a b) t =
      (1 + s) * timeDerivL u (slabMk (log s) t) :=
  (hasDerivWithinAt_weightedLogSpotPrice_time u s t).derivWithin
    (uniqueDiffOn_Icc hab t t.2)

/-- Terminal data in weighted log-spot coordinates become the specified payoff. -/
theorem weightedLogSpotPrice_terminal (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {h : ℝ → ℝ}
    (hu : ∀ y, u (slabMk y ⟨b, right_mem_Icc.mpr hab.le⟩) = h (exp y) / (1 + exp y))
    {s : ℝ} (hs : 0 < s) : weightedLogSpotPrice u s b = h s := by
  rw [weightedLogSpotPrice_of_mem u s ⟨b, right_mem_Icc.mpr hab.le⟩, hu, exp_log hs]
  exact mul_div_cancel₀ _ (by positivity)

/-- The financial pricing operator is the bounded weighted log-spot operator multiplied by
`1+s`. Time differentiation is within the closed slab, so the identity uses the recorded
derivative fields even at endpoints. Rate and volatility values are arbitrary. -/
theorem pde_weightedLogSpotPrice (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) (σ r : ℝ) :
    derivWithin (weightedLogSpotPrice u s) (Icc a b) t +
        σ ^ 2 * s ^ 2 / 2 * deriv (deriv fun x => weightedLogSpotPrice u x t) s +
        r * (s * deriv (fun x => weightedLogSpotPrice u x t) s - weightedLogSpotPrice u s t) =
      (1 + s) * (timeDerivL u (slabMk (log s) t) +
        σ ^ 2 / 2 * spatialSecondFDerivL u (slabMk (log s) t) 1 1 +
        (r + σ ^ 2 / 2 * ((s - 1) / (s + 1))) *
          spatialFDerivL u (slabMk (log s) t) 1 -
        r / (1 + s) * u (slabMk (log s) t)) := by
  rw [derivWithin_weightedLogSpotPrice_time, deriv_deriv_weightedLogSpotPrice_spot u hs,
    deriv_weightedLogSpotPrice_spot u hs, weightedLogSpotPrice_of_mem]
  field_simp
  ring

end TauCeti.Finance
