/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Probability.Finance.LogSpot
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

private theorem contDiffOn_spatialSlice_comp_log (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (t : Icc a b) : ContDiffOn ℝ 2 (fun x => u (slabMk (log x) t)) (Ioi 0) :=
  (u.contDiff_spatialSlice t).comp_contDiffOn
    (contDiffOn_log.mono (fun _ hx => ne_of_gt hx))

/-- Every spatial slice of the price is twice continuously differentiable at positive spot. -/
theorem contDiffOn_weightedLogSpotPrice (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (t : Icc a b) : ContDiffOn ℝ 2 (fun s => weightedLogSpotPrice u s t) (Ioi 0) := by
  simp_rw [weightedLogSpotPrice_of_mem]
  exact (contDiffOn_const.add contDiffOn_id).mul
    (contDiffOn_spatialSlice_comp_log u t)

/-- The spot derivative, expressed through the bounded spatial gradient in log spot. -/
theorem hasDerivAt_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 < s) (t : Icc a b) :
    HasDerivAt (fun x => weightedLogSpotPrice u x t)
      (u (slabMk (log s) t) + (1 + s) / s *
        spatialFDerivL u (slabMk (log s) t) 1) s := by
  have h := (u.hasDerivAt_spatialSlice t (log s)).comp s (hasDerivAt_log hs.ne')
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
  let v : ℝ → ℝ := fun y => u (slabMk y t)
  let f : ℝ → ℝ := fun x => v (log x)
  have hv' : deriv v = fun y => spatialFDerivL u (slabMk y t) 1 :=
    funext (u.deriv_spatialSlice t)
  have h₁ {x : ℝ} (hx : 0 < x) :
      x * deriv f x = spatialFDerivL u (slabMk (log x) t) 1 := by
    simpa only [u.deriv_spatialSlice] using mul_deriv_comp_log (v := fun y => u (slabMk y t)) hx.ne'
  have h₂ := sq_mul_deriv_deriv_comp_log
    (by rw [hv']; exact (u.hasDerivAt_spatialFDerivL_apply t (log s) 1).differentiableAt)
    hs.ne'
  rw [hv', u.deriv_spatialFDerivL_apply] at h₂
  have hf : ContDiffOn ℝ 2 f (Ioi 0) := contDiffOn_spatialSlice_comp_log u t
  have hfs := hf.contDiffAt (Ioi_mem_nhds hs)
  have hd := (hfs.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have heq : (deriv fun x => weightedLogSpotPrice u x t) =ᶠ[𝓝 s]
      fun x => f x + (1 + x) * deriv f x := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [deriv_weightedLogSpotPrice_spot u hx t, ← h₁ hx]
    dsimp only [f, v]
    field_simp [ne_of_gt hx]
  have hprod : HasDerivAt (fun x => f x + (1 + x) * deriv f x)
      (deriv f s + (deriv f s + (1 + s) * deriv (deriv f) s)) s := by
    simpa only [id_eq, one_mul] using
      (hfs.differentiableAt two_ne_zero).hasDerivAt.fun_add
          (((hasDerivAt_id s).const_add 1).fun_mul hd.hasDerivAt)
  rw [heq.deriv_eq, hprod.deriv]
  apply (eq_div_iff (pow_ne_zero 2 hs.ne')).2
  dsimp only [f, v]
  linear_combination (1 + s) * h₂ + 2 * s * h₁ hs

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
  have hC := contDiffOn_weightedLogSpotPrice u t
  have hCs := hC.contDiffAt (Ioi_mem_nhds hs)
  -- Freeze time: the existing identity supplies the spatial operator without imposing
  -- ordinary time differentiability on the clamped extension at the slab endpoints.
  have h := pde_comp_exp_div_one_add_exp
    (C := fun x _ => weightedLogSpotPrice u x t) (y := log s) (t := (t : ℝ)) σ r
    (by
      rw [exp_log hs]
      filter_upwards [Ioi_mem_nhds hs] with x hx
      exact (hC.contDiffAt (Ioi_mem_nhds hx)).differentiableAt two_ne_zero)
    (by
      rw [exp_log hs]
      exact (hCs.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  simp_rw [weightedLogSpotPrice_exp_div, timeExtension_of_mem] at h
  have hv : deriv (fun y => u (slabMk y t)) =
      fun y => spatialFDerivL u (slabMk y t) 1 :=
    funext (u.deriv_spatialSlice t)
  rw [hv, u.deriv_spatialFDerivL_apply] at h
  simp only [deriv_const, zero_add, exp_log hs] at h
  rw [derivWithin_weightedLogSpotPrice_time]
  have hw : (1 + s) ≠ 0 := by positivity
  rw [eq_div_iff hw] at h
  linear_combination -h

end TauCeti.Finance
