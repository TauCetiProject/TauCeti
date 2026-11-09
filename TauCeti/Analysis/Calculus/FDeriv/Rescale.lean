/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
# Rescaling a map to its derivative

The maps `v ↦ t⁻¹ • (f (t • v) - f 0)` extend at `t = 0` by the derivative of `f` at the
origin. The extension is jointly continuous at every `(0, v)` under mere differentiability
at the origin, not only separately continuous in the two variables. On a small ball, all
rescalings with `‖t‖ ≤ 1` satisfy one linear norm bound. These facts allow local coordinate
changes to be deformed to their linearizations without leaving a prescribed neighborhood.

The continuity proof uses `HasFDerivWithinAt.lim`, the rescaled-difference characterization
of the derivative in Mathlib.

For a family of maps `f p` over a parameter space, differentiable near the origin with
derivatives jointly continuous in the parameter and the point, the rescalings are jointly
continuous in the parameter as well (`TauCeti.continuousOn_derivativeRescale_family`), and over a
compact parameter space one linear bound and one radius serve the whole family
(`TauCeti.exists_forall_norm_derivativeRescale_le_family`). Both rest on the mean value
inequality, which bounds the distance of a rescaling from a fixed linear map by the oscillation
of the derivatives along a segment (`TauCeti.norm_derivativeRescale_sub_le`).
-/

open Function Metric

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

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- If the derivatives of `f` along the segment from `0` to `t • v` stay within `C` of a
continuous linear map `φ`, the rescaling differs from `φ` by at most `C ‖v‖` at `v`. -/
theorem norm_derivativeRescale_sub_le {f : E → F} {D : E → E →L[ℝ] F} {φ : E →L[ℝ] F} {C : ℝ}
    {t : ℝ} {v : E} (hf : ∀ z ∈ segment ℝ 0 (t • v), HasFDerivAt f (D z) z)
    (hC : ∀ z ∈ segment ℝ 0 (t • v), ‖D z - φ‖ ≤ C) :
    ‖derivativeRescale f (D 0) t v - φ v‖ ≤ C * ‖v‖ := by
  have h0 : (0 : E) ∈ segment ℝ 0 (t • v) := left_mem_segment ℝ _ _
  by_cases ht : t = 0
  · subst t
    rw [derivativeRescale_zero, ← sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hC 0 h0) (norm_nonneg v))
  · have hmv := (convex_segment (0 : E) (t • v)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun z hz ↦ (hf z hz).hasFDerivWithinAt) hC h0 (right_mem_segment ℝ _ _)
    rw [sub_zero, map_smul, norm_smul] at hmv
    rw [derivativeRescale_of_ne_zero f _ ht, ← inv_smul_smul₀ ht (φ v), ← smul_sub, norm_smul,
      norm_inv]
    calc ‖t‖⁻¹ * ‖f (t • v) - f 0 - t • φ v‖ ≤ ‖t‖⁻¹ * (C * (‖t‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hmv (by positivity)
      _ = C * ‖v‖ := by field_simp

variable {P : Type*} [TopologicalSpace P] {f : P → E → F} {D : P → E → E →L[ℝ] F} {r : ℝ}

/-- At scale zero, the rescalings of the family tend to the derivative at the origin, uniformly
in the parameter: the derivatives along the short segment from `0` to `t • v` stay close to
`D p₀ 0` for `p` near `p₀`. -/
private theorem tendsto_derivativeRescale_family_zero
    (hf : ∀ p, ∀ y ∈ ball (0 : E) r, HasFDerivAt (f p) (D p y) y)
    (hD : ContinuousOn (uncurry D) (univ ×ˢ ball 0 r)) {p₀ : P} {v₀ : E}
    (hv₀ : v₀ ∈ ball (0 : E) r) :
    Tendsto (fun q : P × ℝ × E ↦ derivativeRescale (f q.1) (D q.1 0) q.2.1 q.2.2)
      (𝓝[univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)] (p₀, 0, v₀)) (𝓝 (D p₀ 0 v₀)) := by
  have hr : 0 < r := pos_of_mem_ball hv₀
  set φ := D p₀ 0
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ : ∃ η > 0, η * (‖v₀‖ + 1) < ε / 2 :=
    ⟨ε / (4 * (‖v₀‖ + 1)), by positivity, by field_simp; linarith⟩
  -- Near `(p₀, 0)` the derivatives are `η`-close to `φ`, on a product neighbourhood `N × W`.
  have hDc : ∀ᶠ z : P × E in 𝓝 (p₀, 0), ‖D z.1 z.2 - φ‖ < η := by
    have h := (hD (p₀, 0) ⟨mem_univ _, mem_ball_self hr⟩).tendsto
    rw [nhdsWithin_eq_nhds.2 ((isOpen_univ.prod isOpen_ball).mem_nhds
      ⟨mem_univ _, mem_ball_self hr⟩)] at h
    exact (Metric.tendsto_nhds.1 h η hη).mono fun z hz ↦ by rw [dist_eq_norm] at hz; exact hz
  obtain ⟨N, hN, W, hW, hNW⟩ := mem_nhds_prod_iff.1 hDc
  obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.1 hW
  have hsmul0 : Tendsto (fun q : P × ℝ × E ↦ q.2.1 • q.2.2) (𝓝 (p₀, 0, v₀)) (𝓝 0) := by
    have hc : Continuous fun q : P × ℝ × E ↦ q.2.1 • q.2.2 := by fun_prop
    exact hc.tendsto' _ _ (by simp)
  have hv : Tendsto (fun q : P × ℝ × E ↦ q.2.2) (𝓝 (p₀, 0, v₀)) (𝓝 v₀) :=
    (continuous_snd.comp continuous_snd).tendsto _
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds ((continuous_fst.tendsto _).eventually hN),
    nhdsWithin_le_nhds (hsmul0.eventually (ball_mem_nhds 0 hρ)),
    nhdsWithin_le_nhds (hv.eventually (ball_mem_nhds v₀ one_pos)),
    nhdsWithin_le_nhds ((φ.continuous.tendsto v₀).comp hv |>.eventually
      (ball_mem_nhds (φ v₀) (half_pos hε)))]
    with q ⟨_, ht, hvr⟩ hp hρ' hv1 hφ
  obtain ⟨p, t, v⟩ := q
  simp only [comp_apply] at ht hvr hp hρ' hv1 hφ ⊢
  -- The mean value inequality along the segment from `0` to `t • v` bounds the rescaling.
  have hseg : segment ℝ 0 (t • v) ⊆ ball 0 ρ ∩ ball 0 r :=
    (convex_ball (0 : E) ρ |>.inter (convex_ball 0 r)).segment_subset
      ⟨mem_ball_self hρ, mem_ball_self hr⟩
      ⟨hρ', (balanced_ball_zero (𝕜 := ℝ)).smul_mem (mem_closedBall_zero_iff.1 ht) hvr⟩
  have hb := norm_derivativeRescale_sub_le (f := f p) (D := D p) (φ := φ) (C := η)
    (fun z hz ↦ hf p z (hseg hz).2) fun z hz ↦
      le_of_lt (hNW (mk_mem_prod hp (hρW (hseg hz).1)))
  have hv1' : ‖v‖ < ‖v₀‖ + 1 := by
    have := norm_le_norm_add_norm_sub' v v₀
    rw [dist_eq_norm] at hv1
    linarith
  rw [dist_eq_norm] at hφ ⊢
  calc ‖derivativeRescale (f p) (D p 0) t v - φ v₀‖
      ≤ ‖derivativeRescale (f p) (D p 0) t v - φ v‖ + ‖φ v - φ v₀‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_le_of_lt (hb.trans ?_) hφ
        nlinarith [norm_nonneg v]
    _ = ε := add_halves ε

/-- **Rescaling a family to its derivatives.** Let `f p` be a family of maps, differentiable on
the ball of radius `r` with derivatives `D p y` jointly continuous in `p` and `y`, and let `f`
itself be jointly continuous there. Then the rescalings `derivativeRescale (f p) (D p 0) t v`
are jointly continuous in `p`, the scale `t` with `‖t‖ ≤ 1`, and `v` in the ball, including at
scale zero. -/
theorem continuousOn_derivativeRescale_family
    (hf : ∀ p, ∀ y ∈ ball (0 : E) r, HasFDerivAt (f p) (D p y) y)
    (hfc : ContinuousOn (uncurry f) (univ ×ˢ ball 0 r))
    (hD : ContinuousOn (uncurry D) (univ ×ˢ ball 0 r)) :
    ContinuousOn (fun q : P × ℝ × E ↦ derivativeRescale (f q.1) (D q.1 0) q.2.1 q.2.2)
      (univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)) := by
  rintro ⟨p₀, t₀, v₀⟩ ⟨-, ht₀, hv₀⟩
  have hr : 0 < r := pos_of_mem_ball hv₀
  by_cases ht0 : t₀ = 0
  · subst t₀
    simpa only [ContinuousWithinAt, derivativeRescale_zero] using
      tendsto_derivativeRescale_family_zero hf hD hv₀
  -- Away from scale zero the rescaling is a difference quotient of the jointly continuous `f`.
  have hcont : ContinuousWithinAt
      (fun q : P × ℝ × E ↦ q.2.1⁻¹ • (f q.1 (q.2.1 • q.2.2) - f q.1 0))
      (univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)) (p₀, t₀, v₀) := by
    have h₁ : ContinuousWithinAt (fun q : P × ℝ × E ↦ f q.1 (q.2.1 • q.2.2))
        (univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)) (p₀, t₀, v₀) :=
      (hfc.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).smul
        (continuous_snd.comp continuous_snd))).continuousOn
        fun q (hq : q ∈ univ ×ˢ (closedBall (0 : ℝ) 1 ×ˢ ball (0 : E) r)) ↦
          ⟨mem_univ _, (balanced_ball_zero (𝕜 := ℝ)).smul_mem
            (mem_closedBall_zero_iff.1 hq.2.1) hq.2.2⟩) _ ⟨mem_univ _, ht₀, hv₀⟩
    have h₂ : ContinuousWithinAt (fun q : P × ℝ × E ↦ f q.1 0)
        (univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)) (p₀, t₀, v₀) :=
      (hfc.comp (continuous_fst.prodMk continuous_const).continuousOn
        fun _ _ ↦ ⟨mem_univ _, mem_ball_self hr⟩) _ ⟨mem_univ _, ht₀, hv₀⟩
    have h₀ : ContinuousWithinAt (fun q : P × ℝ × E ↦ q.2.1)
        (univ ×ˢ (closedBall 0 1 ×ˢ ball 0 r)) (p₀, t₀, v₀) :=
      (continuous_fst.comp continuous_snd).continuousWithinAt
    exact (h₀.inv₀ ht0).smul (h₁.sub h₂)
  refine hcont.congr_of_eventuallyEq ?_ (derivativeRescale_of_ne_zero _ _ ht0 _)
  filter_upwards [nhdsWithin_le_nhds ((continuous_fst.comp continuous_snd).continuousAt
    |>.preimage_mem_nhds (compl_singleton_mem_nhds ht0))] with q hq
  exact derivativeRescale_of_ne_zero _ _ hq _

/-- **One linear bound for a compact family of rescalings.** Over a compact parameter space, a
family of maps differentiable on the ball of radius `r`, with derivatives jointly continuous in
the parameter and the point, has one bound `L` on the derivatives at the origin and one radius
`ρ` such that every rescaling with `‖t‖ ≤ 1` is bounded by `L ‖v‖` for `‖v‖ < ρ`. -/
theorem exists_forall_norm_derivativeRescale_le_family [CompactSpace P] (hr : 0 < r)
    (hf : ∀ p, ∀ y ∈ ball (0 : E) r, HasFDerivAt (f p) (D p y) y)
    (hD : ContinuousOn (uncurry D) (univ ×ˢ ball 0 r)) :
    ∃ L > 0, ∃ ρ ∈ Ioc 0 r, ∀ p, ‖D p 0‖ ≤ L ∧ ∀ t : ℝ, ‖t‖ ≤ 1 → ∀ v : E, ‖v‖ < ρ →
      ‖derivativeRescale (f p) (D p 0) t v‖ ≤ L * ‖v‖ := by
  have hD0 : Continuous fun p ↦ D p 0 :=
    hD.comp_continuous (continuous_id.prodMk continuous_const)
      fun _ ↦ ⟨mem_univ _, mem_ball_self hr⟩
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hD0.continuousOn
  have hev : ∀ᶠ z in 𝓝 (0 : E), ∀ p ∈ (univ : Set P), ‖D p z‖ < max B 0 + 1 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun p _ ↦ ?_
    have h := (hD (p, 0) ⟨mem_univ _, mem_ball_self hr⟩).tendsto
    rw [nhdsWithin_eq_nhds.2 ((isOpen_univ.prod isOpen_ball).mem_nhds
      ⟨mem_univ _, mem_ball_self hr⟩)] at h
    have h' : Tendsto (fun z : E × P ↦ ‖D z.2 z.1‖) (𝓝 (0, p)) (𝓝 ‖D p 0‖) :=
      (continuous_norm.tendsto _).comp (h.comp (continuous_swap.tendsto (0, p)))
    exact h'.eventually (gt_mem_nhds ((hB p (mem_univ _)).trans_lt
      (by linarith [le_max_left B 0])))
  obtain ⟨ρ, hρ, hρD⟩ := Metric.mem_nhds_iff.1 hev
  refine ⟨max B 0 + 1, by positivity, min ρ r, ⟨lt_min hρ hr, min_le_right _ _⟩, fun p ↦
    ⟨(hB p (mem_univ _)).trans (by linarith [le_max_left B 0]), fun t ht v hv ↦ ?_⟩⟩
  have htv : t • v ∈ ball (0 : E) (min ρ r) := by
    rw [mem_ball_zero_iff, norm_smul]
    nlinarith [norm_nonneg v, norm_nonneg t]
  have hseg : segment ℝ 0 (t • v) ⊆ ball 0 (min ρ r) :=
    (convex_ball (0 : E) _).segment_subset (mem_ball_self (lt_min hρ hr)) htv
  have := norm_derivativeRescale_sub_le (f := f p) (D := D p) (φ := 0) (C := max B 0 + 1)
    (fun z hz ↦ hf p z (ball_subset_ball (min_le_right _ _) (hseg hz)))
    fun z hz ↦ by
      simpa using (hρD (ball_subset_ball (min_le_left _ _) (hseg hz)) p (mem_univ _)).le
  simpa using this

end TauCeti
