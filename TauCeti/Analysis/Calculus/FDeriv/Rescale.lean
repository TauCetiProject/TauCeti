/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Rescaling a map to its derivative

The maps `v ↦ t⁻¹ • (f (t • v) - f 0)` extend at `t = 0` by the derivative of `f` at the
origin. The extension is jointly continuous at every `(0, v)` under mere differentiability
at the origin, not only separately continuous in the two variables. On a small ball, all
rescalings with `‖t‖ ≤ 1` satisfy one linear norm bound. These facts allow local coordinate
changes to be deformed to their linearizations without leaving a prescribed neighborhood.

The continuity proof uses `HasFDerivWithinAt.lim`, the rescaled-difference characterization
of the derivative in Mathlib.

For a family of real maps `f p` indexed by a topological space `P`, whose derivatives depend
jointly continuously on the parameter and the point near the origin, the rescalings
`derivativeRescale (f p) (f' p 0) t v` are jointly continuous in `(p, t, v)`
(`TauCeti.continuousAt_parametric_derivativeRescale_zero`), and on a compact parameter space they
satisfy one linear bound uniformly in `p` (`TauCeti.exists_parametric_norm_derivativeRescale_le`).
Both rest on the mean value estimate `TauCeti.norm_derivativeRescale_sub_le`, which bounds the
distance of a rescaling from the derivative by the oscillation of the derivative near the origin,
made locally uniform in the parameter by
`TauCeti.exists_pos_eventually_norm_derivativeRescale_sub_le`.
-/

public section

open Filter Set Topology

namespace TauCeti

section NontriviallyNormedField

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

/-- Away from scale zero, the rescalings of a family of maps are jointly continuous in the
parameter, the scale and the point wherever the family is jointly continuous. -/
theorem continuousAt_parametric_derivativeRescale {P : Type*} [TopologicalSpace P]
    {f : P → E → F} {A : P → E →L[𝕜] F} {p : P} {t : 𝕜} {v : E} (ht : t ≠ 0)
    (hf : ContinuousAt (fun x : P × E ↦ f x.1 x.2) (p, t • v))
    (hf₀ : ContinuousAt (fun q ↦ f q 0) p) :
    ContinuousAt (fun q : P × 𝕜 × E ↦ derivativeRescale (f q.1) (A q.1) q.2.1 q.2.2)
      (p, t, v) := by
  have hg : Continuous fun q : P × 𝕜 × E ↦ (q.1, q.2.1 • q.2.2) := by fun_prop
  have hcont : ContinuousAt (fun q : P × 𝕜 × E ↦ q.2.1⁻¹ • (f q.1 (q.2.1 • q.2.2) - f q.1 0))
      (p, t, v) :=
    (continuous_snd.fst.continuousAt.inv₀ ht).smul
      ((hf.comp_of_eq hg.continuousAt rfl).sub (hf₀.comp_of_eq continuous_fst.continuousAt rfl))
  apply hcont.congr_of_eventuallyEq
  filter_upwards [continuous_snd.fst.continuousAt.preimage_mem_nhds
    (compl_singleton_mem_nhds ht)] with q hq
  exact derivativeRescale_of_ne_zero (f q.1) (A q.1) hq q.2.2

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

end NontriviallyNormedField

section Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If the derivative of `f` stays within `η` of its value at the origin on the ball of radius
`r`, then every rescaling `derivativeRescale f (f' 0) t v` with `t • v` in that ball is within
`η * ‖v‖` of `f' 0 v`. -/
theorem norm_derivativeRescale_sub_le {f : E → F} {f' : E → E →L[ℝ] F} {r η : ℝ}
    (hf : ∀ z ∈ Metric.ball (0 : E) r, HasFDerivAt f (f' z) z)
    (hη : ∀ z ∈ Metric.ball (0 : E) r, ‖f' z - f' 0‖ ≤ η) {t : ℝ} {v : E}
    (htv : ‖t • v‖ < r) :
    ‖derivativeRescale f (f' 0) t v - f' 0 v‖ ≤ η * ‖v‖ := by
  have h0 : (0 : E) ∈ Metric.ball (0 : E) r :=
    Metric.mem_ball_self ((norm_nonneg _).trans_lt htv)
  have hη₀ : 0 ≤ η := (norm_nonneg _).trans (hη 0 h0)
  by_cases ht : t = 0
  · simpa [ht] using mul_nonneg hη₀ (norm_nonneg v)
  · have htv' : t • v ∈ Metric.ball (0 : E) r := by simpa using htv
    -- The mean value inequality on the ball, between the origin and `t • v`.
    have hmv := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz ↦ (hf z hz).hasFDerivWithinAt) hη h0 htv'
    rw [sub_zero] at hmv
    have hrw : derivativeRescale f (f' 0) t v - f' 0 v =
        t⁻¹ • (f (t • v) - f 0 - f' 0 (t • v)) := by
      rw [derivativeRescale_of_ne_zero f _ ht, map_smul, smul_sub (t⁻¹) (f (t • v) - f 0),
        inv_smul_smul₀ ht]
    rw [norm_smul] at hmv
    rw [hrw, norm_smul, norm_inv]
    calc ‖t‖⁻¹ * ‖f (t • v) - f 0 - f' 0 (t • v)‖ ≤ ‖t‖⁻¹ * (η * (‖t‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hmv (by positivity)
      _ = η * ‖v‖ := by field_simp [norm_ne_zero_iff.mpr ht]

variable {P : Type*} [TopologicalSpace P] {f : P → E → F} {f' : P → E → E →L[ℝ] F}
  {U : Set E}

/-- **Local uniform rescaling estimate.** For a family of maps whose derivatives near the origin
depend jointly continuously on the parameter and the point at `(p₀, 0)`, every tolerance `η > 0`
admits a radius `r > 0` such that, for all parameters near `p₀`, the rescalings with `t • v` in
the ball of radius `r` are within `η * ‖v‖` of the derivative at the origin. -/
theorem exists_pos_eventually_norm_derivativeRescale_sub_le (hU : U ∈ 𝓝 0)
    (hf : ∀ p, ∀ z ∈ U, HasFDerivAt (f p) (f' p z) z) {p₀ : P}
    (hf' : ContinuousAt (fun x : P × E ↦ f' x.1 x.2) (p₀, 0)) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ᶠ p in 𝓝 p₀, ∀ (t : ℝ) (v : E), ‖t • v‖ < r →
      ‖derivativeRescale (f p) (f' p 0) t v - f' p 0 v‖ ≤ η * ‖v‖ := by
  -- Near `(p₀, 0)` the derivative is within `η / 2` of `f' p₀ 0`, on a product neighbourhood.
  have h := hf'.eventually (Metric.ball_mem_nhds (f' p₀ 0) (half_pos hη))
  rw [nhds_prod_eq] at h
  obtain ⟨W, hW, Z, hZ, hWZ⟩ := Filter.eventually_prod_iff.1 h
  obtain ⟨r, hr, hrZ⟩ := Metric.mem_nhds_iff.1 (inter_mem hZ hU)
  have hclose (p : P) (hp : W p) (z : E) (hz : z ∈ Metric.ball (0 : E) r) :
      ‖f' p z - f' p₀ 0‖ < η / 2 := by
    simpa [dist_eq_norm] using hWZ hp (hrZ hz).1
  refine ⟨r, hr, hW.mono fun p hp t v htv ↦ norm_derivativeRescale_sub_le
    (fun z hz ↦ hf p z (hrZ hz).2) (fun z hz ↦ ?_) htv⟩
  calc ‖f' p z - f' p 0‖ ≤ ‖f' p z - f' p₀ 0‖ + ‖f' p₀ 0 - f' p 0‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖f' p z - f' p₀ 0‖ + ‖f' p 0 - f' p₀ 0‖ := by rw [norm_sub_rev (f' p₀ 0)]
    _ ≤ η := by linarith [hclose p hp z hz, hclose p hp 0 (Metric.mem_ball_self hr)]

/-- A family of maps whose derivatives near the origin depend jointly continuously on the
parameter and the point has rescalings `derivativeRescale (f p) (f' p 0) t v` which are jointly
continuous in `(p, t, v)` at scale zero. -/
theorem continuousAt_parametric_derivativeRescale_zero (hU : U ∈ 𝓝 0)
    (hf : ∀ p, ∀ z ∈ U, HasFDerivAt (f p) (f' p z) z) {p₀ : P}
    (hf' : ContinuousAt (fun x : P × E ↦ f' x.1 x.2) (p₀, 0)) (v : E) :
    ContinuousAt (fun q : P × ℝ × E ↦ derivativeRescale (f q.1) (f' q.1 0) q.2.1 q.2.2)
      (p₀, 0, v) := by
  have hD0 : ContinuousAt (fun q : P × ℝ × E ↦ f' q.1 0 q.2.2) (p₀, 0, v) :=
    (hf'.comp_of_eq (continuous_fst.prodMk continuous_const).continuousAt rfl).clm_apply
      continuous_snd.snd.continuousAt
  rw [ContinuousAt, derivativeRescale_zero]
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- The rescaling is within `η * (‖v‖ + 1) = ε / 2` of its derivative part near `(p₀, 0, v)`,
  -- and the derivative part is within `ε / 2` of `f' p₀ 0 v`.
  set η := ε / (2 * (‖v‖ + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨r, hr, hp⟩ := exists_pos_eventually_norm_derivativeRescale_sub_le hU hf hf' hη
  have hsmul : Tendsto (fun q : P × ℝ × E ↦ q.2.1 • q.2.2) (𝓝 (p₀, 0, v)) (𝓝 0) := by
    have h : Continuous fun q : P × ℝ × E ↦ q.2.1 • q.2.2 := by fun_prop
    simpa using h.tendsto (p₀, 0, v)
  have e1 : ∀ᶠ q : P × ℝ × E in 𝓝 (p₀, 0, v), ∀ (t : ℝ) (w : E), ‖t • w‖ < r →
      ‖derivativeRescale (f q.1) (f' q.1 0) t w - f' q.1 0 w‖ ≤ η * ‖w‖ :=
    (continuous_fst.tendsto (p₀, (0 : ℝ), v)).eventually hp
  have e2 : ∀ᶠ q : P × ℝ × E in 𝓝 (p₀, 0, v), ‖q.2.1 • q.2.2‖ < r := by
    simpa using hsmul.eventually (Metric.ball_mem_nhds 0 hr)
  have e3 : ∀ᶠ q : P × ℝ × E in 𝓝 (p₀, 0, v), ‖q.2.2‖ < ‖v‖ + 1 := by
    have h : ∀ᶠ q : P × ℝ × E in 𝓝 (p₀, 0, v), q.2.2 ∈ Metric.ball v 1 :=
      continuous_snd.snd.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds v zero_lt_one)
    filter_upwards [h] with q hq
    rw [Metric.mem_ball, dist_eq_norm] at hq
    linarith [norm_le_norm_add_norm_sub' q.2.2 v]
  have e4 : ∀ᶠ q : P × ℝ × E in 𝓝 (p₀, 0, v), ‖f' q.1 0 q.2.2 - f' p₀ 0 v‖ < ε / 2 := by
    simpa [dist_eq_norm] using hD0.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  filter_upwards [e1, e2, e3, e4] with q hq hqr hqv hqD
  rw [dist_eq_norm]
  calc ‖derivativeRescale (f q.1) (f' q.1 0) q.2.1 q.2.2 - f' p₀ 0 v‖
      ≤ ‖derivativeRescale (f q.1) (f' q.1 0) q.2.1 q.2.2 - f' q.1 0 q.2.2‖ +
          ‖f' q.1 0 q.2.2 - f' p₀ 0 v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < η * (‖v‖ + 1) + ε / 2 :=
        add_lt_add ((hq _ _ hqr).trans_lt (mul_lt_mul_of_pos_left hqv hη)) hqD
    _ = ε := by rw [hη_def]; field_simp; ring

/-- On a compact parameter space, a family of maps whose derivatives near the origin depend
jointly continuously on the parameter and the point has one linear bound for all small
rescalings, uniformly in the parameter. -/
theorem exists_parametric_norm_derivativeRescale_le [CompactSpace P] (hU : U ∈ 𝓝 0)
    (hf : ∀ p, ∀ z ∈ U, HasFDerivAt (f p) (f' p z) z)
    (hf' : ∀ p, ContinuousAt (fun x : P × E ↦ f' x.1 x.2) (p, 0)) :
    ∃ L > 0, (∀ p, ‖f' p 0‖ ≤ L) ∧ ∃ δ > 0, ∀ p, ∀ t : ℝ, ‖t‖ ≤ 1 → ∀ v : E, ‖v‖ ≤ δ →
      ‖derivativeRescale (f p) (f' p 0) t v‖ ≤ L * ‖v‖ := by
  have hc : Continuous fun p ↦ f' p 0 :=
    continuous_iff_continuousAt.2 fun p ↦
      (hf' p).comp_of_eq (continuous_id.prodMk continuous_const).continuousAt rfl
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  -- By the tube lemma, one ball around the origin keeps every derivative within `1` of its value
  -- at the origin, for every parameter.
  have htube : ∀ᶠ z in 𝓝 (0 : E), ∀ p ∈ (univ : Set P), z ∈ U ∧ ‖f' p z - f' p 0‖ < 1 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun p _ ↦ ?_
    have hg : ContinuousAt (fun x : E × P ↦ f' x.2 x.1 - f' x.2 0) (0, p) :=
      ((hf' p).comp_of_eq continuous_swap.continuousAt rfl).sub
        (hc.continuousAt.comp continuous_snd.continuousAt)
    have hlt := hg.eventually (Metric.ball_mem_nhds _ zero_lt_one)
    simp only [sub_self, dist_zero_right] at hlt
    filter_upwards [hlt, continuous_fst.continuousAt.preimage_mem_nhds (x := ((0 : E), p)) hU]
      with x hx hxU using ⟨hxU, hx⟩
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.1 htube
  refine ⟨max M 0 + 1, by positivity, fun p ↦ ((hM p trivial).trans (le_max_left _ _)).trans
    (le_add_of_nonneg_right zero_le_one), r / 2, half_pos hr, fun p t ht v hv ↦ ?_⟩
  have htv : ‖t • v‖ < r := by
    rw [norm_smul]
    calc ‖t‖ * ‖v‖ ≤ 1 * (r / 2) := mul_le_mul ht hv (norm_nonneg _) zero_le_one
      _ < r := by linarith
  have hmain := norm_derivativeRescale_sub_le (f := f p)
    (fun z hz ↦ hf p z (hrb hz p trivial).1) (fun z hz ↦ (hrb hz p trivial).2.le) htv
  calc ‖derivativeRescale (f p) (f' p 0) t v‖
      ≤ ‖derivativeRescale (f p) (f' p 0) t v - f' p 0 v‖ + ‖f' p 0 v‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 * ‖v‖ + max M 0 * ‖v‖ := by
        gcongr
        exact ((f' p 0).le_opNorm v).trans (mul_le_mul_of_nonneg_right
          ((hM p trivial).trans (le_max_left _ _)) (norm_nonneg v))
    _ = (max M 0 + 1) * ‖v‖ := by ring

end Real

end TauCeti
