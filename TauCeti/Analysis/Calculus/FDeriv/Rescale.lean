/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Rescaling a map to its derivative

The maps `v ↦ t⁻¹ • (f (t • v) - f 0)` extend at `t = 0` by the derivative of `f` at the
origin. The extension is jointly continuous at every `(0, v)` under mere differentiability
at the origin, not only separately continuous in the two variables. On a small ball, all
rescalings with `‖t‖ ≤ 1` satisfy one linear norm bound. These facts allow local coordinate
changes to be deformed to their linearizations without leaving a prescribed neighborhood.

The continuity proof uses `HasFDerivWithinAt.lim`, the rescaled-difference characterization
of the derivative in Mathlib.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The rescaled difference of `f` at the origin, extended at scale zero by a continuous
linear map `A`. When `A` is the derivative, this extension is jointly continuous at scale zero. -/
noncomputable def derivativeRescale (f : E → F) (A : E →L[𝕜] F) (t : 𝕜) (v : E) : F := by
  classical
  exact if t = 0 then A v else t⁻¹ • (f (t • v) - f 0)

/-- At scale zero the rescaling is the prescribed linear map. -/
@[simp]
theorem derivativeRescale_zero (f : E → F) (A : E →L[𝕜] F) (v : E) :
    derivativeRescale f A 0 v = A v := by
  simp [derivativeRescale]

/-- At a nonzero scale the rescaling is the usual difference quotient. -/
theorem derivativeRescale_of_ne_zero (f : E → F) (A : E →L[𝕜] F) {t : 𝕜} (ht : t ≠ 0)
    (v : E) : derivativeRescale f A t v = t⁻¹ • (f (t • v) - f 0) := by
  simp [derivativeRescale, ht]

/-- At scale one the rescaling is the original map minus its value at the origin. -/
@[simp]
theorem derivativeRescale_one (f : E → F) (A : E →L[𝕜] F) (v : E) :
    derivativeRescale f A 1 v = f v - f 0 := by
  simp [derivativeRescale]

/-- Every rescaling fixes the origin. -/
@[simp]
theorem derivativeRescale_apply_zero (f : E → F) (A : E →L[𝕜] F) (t : 𝕜) :
    derivativeRescale f A t 0 = 0 := by
  simp [derivativeRescale]

variable {f : E → F} {A : E →L[𝕜] F}

/-- Differentiability at the origin makes the rescaling jointly continuous at scale zero. -/
theorem _root_.HasFDerivAt.continuousAt_derivativeRescale_zero
    (hf : HasFDerivAt f A 0) (v : E) :
    ContinuousAt (fun p : 𝕜 × E ↦ derivativeRescale f A p.1 p.2) (0, v) := by
  classical
  have hmul : Continuous (fun p : 𝕜 × E ↦ p.1 • p.2) := continuous_fst.smul continuous_snd
  have hd : Tendsto (fun p : 𝕜 × E ↦ p.1 • p.2) (𝓝 (0, v)) (𝓝 0) := by
    simpa using hmul.tendsto (0, v)
  have hcd : Tendsto (fun p : 𝕜 × E ↦ p.1⁻¹ • (p.1 • p.2))
      (𝓝[{p : 𝕜 × E | p.1 ≠ 0}] (0, v)) (𝓝 v) := by
    apply ((continuous_snd.tendsto (0, v)).mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with p hp
    simp [hp]
  have hlim : Tendsto (fun p : 𝕜 × E ↦ p.1⁻¹ • (f (p.1 • p.2) - f 0))
      (𝓝[{p : 𝕜 × E | p.1 ≠ 0}] (0, v)) (𝓝 (A v)) := by
    simpa only [zero_add] using (hf.hasFDerivWithinAt (s := univ)).lim
      (hd.mono_left nhdsWithin_le_nhds) (by simp) hcd
  rw [ContinuousAt, derivativeRescale_zero, ← nhdsWithin_univ]
  unfold derivativeRescale
  apply Filter.Tendsto.if_nhdsWithin
  · simpa only [univ_inter] using
      ((A.continuous.comp' continuous_snd).tendsto (0, v)).mono_left
        (nhdsWithin_le_nhds (s := {p : 𝕜 × E | p.1 = 0}))
  · simpa only [univ_inter] using hlim

/-- Away from scale zero, continuity of the original map suffices. -/
theorem continuousAt_derivativeRescale {t : 𝕜} {v : E} (ht : t ≠ 0)
    (hf : ContinuousAt f (t • v)) :
    ContinuousAt (fun p : 𝕜 × E ↦ derivativeRescale f A p.1 p.2) (t, v) := by
  have hmul : Continuous (fun p : 𝕜 × E ↦ p.1 • p.2) := continuous_fst.smul continuous_snd
  have hcont : ContinuousAt (fun p : 𝕜 × E ↦ p.1⁻¹ • (f (p.1 • p.2) - f 0)) (t, v) :=
    (continuous_fst.continuousAt.inv₀ ht).smul
      ((hf.comp' (f := fun p : 𝕜 × E ↦ p.1 • p.2) hmul.continuousAt).sub continuousAt_const)
  apply hcont.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (compl_singleton_mem_nhds ht)]
    with p hp
  exact derivativeRescale_of_ne_zero f A hp p.2

/-- A map differentiable at the origin has one linear bound for all its small rescalings.
No continuity away from the origin or finite dimensionality is required. -/
theorem _root_.HasFDerivAt.exists_norm_derivativeRescale_le
    (hf : HasFDerivAt f A 0) :
    ∃ L > 0, ‖A‖ ≤ L ∧ ∃ δ > 0, ∀ t : 𝕜, ‖t‖ ≤ 1 → ∀ v : E, ‖v‖ ≤ δ →
      ‖derivativeRescale f A t v‖ ≤ L * ‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := hf.isBigO_sub.exists_pos
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  have hA : ‖A‖ ≤ max C (‖A‖ + 1) := le_trans (by linarith) (le_max_right _ _)
  refine ⟨max C (‖A‖ + 1), lt_max_of_lt_right (by positivity), hA, r / 2, by positivity,
    fun t ht v hv ↦ ?_⟩
  by_cases ht0 : t = 0
  · subst t
    rw [derivativeRescale_zero]
    exact (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  · rw [derivativeRescale_of_ne_zero f A ht0, norm_smul]
    have htv : ‖t • v‖ < r := by
      rw [norm_smul]
      calc
        ‖t‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht (norm_nonneg v)
        _ < r := by linarith
    have hb : ‖f (t • v) - f 0‖ ≤ C * ‖t • v‖ := by
      simpa only [sub_zero] using hball (by simpa [dist_zero_right] using htv)
    calc
      ‖t⁻¹‖ * ‖f (t • v) - f 0‖ ≤ ‖t⁻¹‖ * (C * ‖t • v‖) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = C * ‖v‖ := by rw [norm_smul, norm_inv]; field_simp
      _ ≤ max C (‖A‖ + 1) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)

/-- Small rescaled balls stay in any prescribed target neighborhood, uniformly for `‖t‖ ≤ 1`.
The original small ball can simultaneously be confined to a prescribed source neighborhood. -/
theorem _root_.HasFDerivAt.exists_derivativeRescale_closedBall_subset
    (hf : HasFDerivAt f A 0) {U : Set E} (hU : U ∈ 𝓝 0) {V : Set F} (hV : V ∈ 𝓝 0) :
    ∃ L > 0, ‖A‖ ≤ L ∧ ∃ δ > 0,
      Metric.closedBall 0 δ ⊆ U ∧ Metric.closedBall 0 (L * δ) ⊆ V ∧
      ∀ t : 𝕜, ‖t‖ ≤ 1 → ∀ v : E, ‖v‖ ≤ δ →
        ‖derivativeRescale f A t v‖ ≤ L * ‖v‖ := by
  obtain ⟨L, hL, hA, d, hd, hbound⟩ := hf.exists_norm_derivativeRescale_le
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨s, hs, hsV⟩ := Metric.mem_nhds_iff.mp hV
  let δ := min d (min (r / 2) (s / (2 * L)))
  have hδ : 0 < δ := lt_min hd (lt_min (by positivity) (by positivity))
  have hδd : δ ≤ d := min_le_left _ _
  have hδr : δ < r := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hδs : L * δ < s := by
    have hle : δ ≤ s / (2 * L) := (min_le_right _ _).trans (min_le_right _ _)
    have := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hle
    nlinarith
  exact ⟨L, hL, hA, δ, hδ, (Metric.closedBall_subset_ball hδr).trans hrU,
    (Metric.closedBall_subset_ball hδs).trans hsV,
    fun t ht v hv ↦ hbound t ht v (hv.trans hδd)⟩

end TauCeti
