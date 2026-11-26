/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Trace
import TauCeti.Probability.Finance.LogSpot
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Topology.Order.Interval.Basic

/-!
# Prices reconstructed from bounded weighted log-spot maps

A bounded parabolic Hölder map `u(y,t)` represents a price of linear growth by
`C(s,t) = (1+s) u(log s,t)` for positive spot. `weightedLogSpotPrice` performs this
reconstruction, using the canonical clamped extension in time. It preserves continuity
on the closed time slab, twice continuous spatial differentiability, and joint continuity
of the first and second spot derivatives and of the within-slab time derivative on
`(0, ∞) × [a, b]`, with explicit linear-growth bounds for both the price and its dollar
delta `s C_s` as well as their combined exposure `|C| + |s C_s|`.

Before maturity (`t ∈ [a, b)`), the within-slab time derivative agrees with the time
derivative within `[a, ∞)` (the right derivative at `t = a`), and on the open horizon
(`t ∈ (a, b)`) with the ordinary time derivative. The pricing-operator identity transports
the backward equation for the bounded map to the financial pricing equation. This is a
change-of-variables result, not an existence or stochastic replication theorem. In
particular, no ellipticity or moment hypotheses are needed here. Terminal data are
transported pointwise, without a smoothness claim at zero spot.

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

@[simp]
theorem weightedLogSpotPrice_zero :
    weightedLogSpotPrice (0 : ParabolicC2HolderSpace α ℝ ℝ hab) = 0 := by
  ext s t
  simp [weightedLogSpotPrice_def, timeExtension_def]

@[simp]
theorem weightedLogSpotPrice_add (u v : ParabolicC2HolderSpace α ℝ ℝ hab) :
    weightedLogSpotPrice (u + v) = weightedLogSpotPrice u + weightedLogSpotPrice v := by
  ext s t
  simp [weightedLogSpotPrice_def, timeExtension_def, mul_add]

@[simp]
theorem weightedLogSpotPrice_sub (u v : ParabolicC2HolderSpace α ℝ ℝ hab) :
    weightedLogSpotPrice (u - v) = weightedLogSpotPrice u - weightedLogSpotPrice v := by
  ext s t
  simp [weightedLogSpotPrice_def, timeExtension_def, mul_sub]

@[simp]
theorem weightedLogSpotPrice_neg (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    weightedLogSpotPrice (-u) = -weightedLogSpotPrice u := by
  ext s t
  simp [weightedLogSpotPrice_def, timeExtension_def]

@[simp]
theorem weightedLogSpotPrice_smul (c : ℝ) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    weightedLogSpotPrice (c • u) = c • weightedLogSpotPrice u := by
  ext s t
  simp [weightedLogSpotPrice_def, timeExtension_def]
  ring

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
    (uniqueDiffOn_Icc hab t t.property)

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

/-! ### Joint continuity, pre-maturity time derivatives, and combined linear growth -/

private theorem continuousOn_log_slabMk_univ (hab : a < b) :
    ContinuousOn (fun p : ℝ × ℝ ↦ slabMk (log p.1) (projIcc a b hab.le p.2))
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  continuous_slabMk.comp_continuousOn <|
    ((continuousOn_log.mono fun _ hx ↦ ne_of_gt hx).comp continuousOn_fst
      fun _ hp ↦ (mem_prod.1 hp).1).prodMk
      ((continuous_projIcc (h := hab.le)).continuousOn.comp continuousOn_snd (mapsTo_univ _ _))

private theorem weightedLogSpotPrice_eq_projIcc (u : ParabolicC2HolderSpace α ℝ ℝ hab) (t : ℝ) :
    (fun x ↦ weightedLogSpotPrice u x t) =
      fun x ↦ weightedLogSpotPrice u x (projIcc a b hab.le t) := by
  ext x
  rw [weightedLogSpotPrice_def, timeExtension_def, weightedLogSpotPrice_of_mem]

private theorem continuousOn_spatialFDerivL_log_slabMk_univ
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦ spatialFDerivL u (slabMk (log p.1) (projIcc a b hab.le p.2)) 1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  ((spatialFDerivL u).continuous.clm_apply continuous_const).comp_continuousOn
    (continuousOn_log_slabMk_univ hab)

/-- The spot derivative of the reconstructed price is jointly continuous at positive spot,
for all times (including the slab endpoints). -/
theorem continuousOn_deriv_weightedLogSpotPrice_spot (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun x ↦ weightedLogSpotPrice u x p.2) p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have hu : Continuous fun q ↦ u q := (valueL u).continuous
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦
      u (slabMk (log p.1) (projIcc a b hab.le p.2)) +
        (1 + p.1) / p.1 * spatialFDerivL u (slabMk (log p.1) (projIcc a b hab.le p.2)) 1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    (hu.comp_continuousOn (continuousOn_log_slabMk_univ hab)).add
      (((continuousOn_const.add continuousOn_fst).div continuousOn_fst
        fun _ hp ↦ ne_of_gt (mem_prod.1 hp).1).mul
        (continuousOn_spatialFDerivL_log_slabMk_univ u))
  refine hc.congr ?_
  rintro ⟨s, t⟩ ⟨hs, -⟩
  dsimp only
  rw [weightedLogSpotPrice_eq_projIcc u t, deriv_weightedLogSpotPrice_spot u hs]

/-- The second spot derivative of the reconstructed price is jointly continuous at positive spot,
for all times (including the slab endpoints). -/
theorem continuousOn_deriv_deriv_weightedLogSpotPrice_spot
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (deriv fun x ↦ weightedLogSpotPrice u x p.2) p.1)
      (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  have huxx : Continuous fun q ↦ spatialSecondFDerivL u q 1 1 :=
    (((ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).comp
      (ContinuousLinearMap.apply ℝ (ℝ →L[ℝ] ℝ) (1 : ℝ))).continuous).comp
      (spatialSecondFDerivL u).continuous
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦
      ((p.1 - 1) * spatialFDerivL u (slabMk (log p.1) (projIcc a b hab.le p.2)) 1 +
        (1 + p.1) * spatialSecondFDerivL u (slabMk (log p.1) (projIcc a b hab.le p.2)) 1 1) /
      p.1 ^ 2) (Ioi 0 ×ˢ (univ : Set ℝ)) :=
    (((continuousOn_fst.sub continuousOn_const).mul
        (continuousOn_spatialFDerivL_log_slabMk_univ u)).add
      ((continuousOn_const.add continuousOn_fst).mul
        (huxx.comp_continuousOn (continuousOn_log_slabMk_univ hab)))).div
      (continuousOn_fst.pow 2) fun _ hp ↦ pow_ne_zero 2 (ne_of_gt (mem_prod.1 hp).1)
  refine hc.congr ?_
  rintro ⟨s, t⟩ ⟨hs, -⟩
  dsimp only
  rw [weightedLogSpotPrice_eq_projIcc u t, deriv_deriv_weightedLogSpotPrice_spot u hs]

/-- The within-slab time derivative of the reconstructed price is jointly continuous on
`(0, ∞) × [a, b]`. -/
theorem continuousOn_derivWithin_weightedLogSpotPrice_time
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (weightedLogSpotPrice u p.1) (Icc a b) p.2)
      (Ioi 0 ×ˢ Icc a b) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦
      (1 + p.1) * timeDerivL u (slabMk (log p.1) (projIcc a b hab.le p.2)))
      (Ioi 0 ×ˢ Icc a b) :=
    (continuousOn_const.add continuousOn_fst).mul
      ((timeDerivL u).continuous.comp_continuousOn
        ((continuousOn_log_slabMk_univ hab).mono (prod_mono_right (subset_univ _))))
  refine hc.congr ?_
  rintro ⟨s, t⟩ ⟨_, ht⟩
  dsimp only
  rw [derivWithin_weightedLogSpotPrice_time u s ⟨t, ht⟩, projIcc_of_mem hab.le ht]

/-- Strictly before maturity (`t ∈ [a, b)`), the reconstructed price has a time derivative within
`[a, ∞)` given by the recorded time-derivative field, including the right derivative at `t = a`. -/
theorem hasDerivWithinAt_Ici_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ico a b) :
    HasDerivWithinAt (weightedLogSpotPrice u s)
      ((1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ico_subset_Icc_self ht⟩)) (Ici a) t :=
  (hasDerivWithinAt_weightedLogSpotPrice_time u s ⟨t, Ico_subset_Icc_self ht⟩).congr_set
    (Icc_eventuallyEq_Ici ht.2)

/-- Strictly before maturity (`t ∈ [a, b)`), the time derivative within `[a, ∞)` agrees with the
within-slab time derivative. -/
theorem derivWithin_Ici_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ico a b) :
    derivWithin (weightedLogSpotPrice u s) (Ici a) t =
      (1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ico_subset_Icc_self ht⟩) :=
  ((derivWithin_congr_set (Icc_eventuallyEq_Ici ht.2)).symm.trans
    (derivWithin_weightedLogSpotPrice_time u s ⟨t, Ico_subset_Icc_self ht⟩))

/-- The time derivative within `[a, ∞)` is jointly continuous on `(0, ∞) × [a, b)`. -/
theorem continuousOn_derivWithin_Ici_weightedLogSpotPrice_time
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    ContinuousOn (fun p : ℝ × ℝ ↦ derivWithin (weightedLogSpotPrice u p.1) (Ici a) p.2)
      (Ioi 0 ×ˢ Ico a b) :=
  ((continuousOn_derivWithin_weightedLogSpotPrice_time u).mono
    (prod_mono_right Ico_subset_Icc_self)).congr fun _ hp ↦
      (derivWithin_congr_set (Icc_eventuallyEq_Ici hp.2.2)).symm

/-- On the open horizon `t ∈ (a, b)`, the reconstructed price has an ordinary time derivative
given by the recorded time-derivative field. -/
theorem hasDerivAt_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (weightedLogSpotPrice u s)
      ((1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht⟩)) t :=
  (hasDerivWithinAt_weightedLogSpotPrice_time u s ⟨t, Ioo_subset_Icc_self ht⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- On the open horizon `t ∈ (a, b)`, the reconstructed price is differentiable in time. -/
theorem differentiableAt_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ioo a b) :
    DifferentiableAt ℝ (weightedLogSpotPrice u s) t :=
  (hasDerivAt_weightedLogSpotPrice_time u s ht).differentiableAt

/-- On the open horizon `t ∈ (a, b)`, the ordinary time derivative equals
`(1 + s) ∂ₜu(log s, t)`. -/
theorem deriv_weightedLogSpotPrice_time (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    (s : ℝ) {t : ℝ} (ht : t ∈ Ioo a b) :
    deriv (weightedLogSpotPrice u s) t =
      (1 + s) * timeDerivL u (slabMk (log s) ⟨t, Ioo_subset_Icc_self ht⟩) :=
  (hasDerivAt_weightedLogSpotPrice_time u s ht).deriv

/-- **Combined linear-growth bound for price and dollar delta.** For `s ≥ 0` and all `t : ℝ`,
`|C(s, t)| + |s C_s(s, t)| ≤ 2 ‖u‖ (1 + s)`. The factor `2` is sharp (attained as `s → ∞` by
`u ≡ 1`, for which `C(s, t) = 1 + s` and `s C_s(s, t) = s`). -/
theorem abs_weightedLogSpotPrice_add_abs_mul_deriv_le (u : ParabolicC2HolderSpace α ℝ ℝ hab)
    {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    |weightedLogSpotPrice u s t| + |s * deriv (fun x ↦ weightedLogSpotPrice u x t) s| ≤
      2 * ‖u‖ * (1 + s) := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · have h₀ := abs_weightedLogSpotPrice_le u le_rfl t
    simp only [zero_mul, abs_zero, add_zero] at h₀ ⊢
    linarith [norm_nonneg u]
  · rw [congrFun (weightedLogSpotPrice_eq_projIcc u t) s, weightedLogSpotPrice_eq_projIcc u t]
    set τ := projIcc a b hab.le t
    have h₁ : |weightedLogSpotPrice u s τ| ≤ ‖valueL u‖ * (1 + s) := by
      rw [weightedLogSpotPrice_of_mem, abs_mul, abs_of_pos (by positivity : 0 < 1 + s), mul_comm]
      exact mul_le_mul_of_nonneg_right ((valueL u).norm_coe_le_norm _) (by positivity)
    have h₂ := abs_mul_deriv_weightedLogSpotPrice_le u hs τ
    have hnorm : 2 * ‖valueL u‖ + ‖spatialFDerivL u‖ ≤ 2 * ‖u‖ := by
      linarith [u.norm_eq, norm_nonneg (spatialFDerivL u), norm_nonneg (spatialSecondFDerivL u),
        norm_nonneg (timeDerivL u)]
    refine (add_le_add h₁ h₂).trans ?_
    calc
      ‖valueL u‖ * (1 + s) + (‖valueL u‖ + ‖spatialFDerivL u‖) * (1 + s) =
          (2 * ‖valueL u‖ + ‖spatialFDerivL u‖) * (1 + s) := by ring
      _ ≤ 2 * ‖u‖ * (1 + s) := mul_le_mul_of_nonneg_right hnorm (by positivity)

end TauCeti.Finance
