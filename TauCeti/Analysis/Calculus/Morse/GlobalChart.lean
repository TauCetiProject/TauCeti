/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GraphChart
public import TauCeti.Analysis.Calculus.Morse.LocalToGlobal
public import TauCeti.Analysis.Calculus.Morse.Stable
-- Private: the gradient and the Fréchet derivative have the same norm.
import TauCeti.Analysis.Calculus.Gradient

/-!
# Global stable and unstable sets are embedded `C¹` submanifolds

Let `x` be a nondegenerate critical point of a globally `C²` function `f` on a
finite-dimensional real inner product space whose gradient is globally Lipschitz. This file
shows that the stable and unstable sets of `x` under the negative-gradient flow are embedded
`C¹` submanifolds of the ambient space: every point of the stable set has a `C¹` ambient chart,
with `C¹` inverse, carrying the stable set onto the stable Hessian subspace, and likewise for
the unstable set. Their dimensions are `finrank E - morseIndex f x` and `morseIndex f x`
(`IsNondegenerateCriticalPoint.finrank_stableLinearSubspace_add_morseIndex` and
`finrank_unstableLinearSubspace`).

The proof has two steps.

* **Near `x` the stable set is the local stable disk.** Since a nondegenerate critical point is
  isolated, `‖∇ f‖` is bounded below by some `c > 0` on a thin annulus around `x`. A trajectory
  that crosses the annulus loses at least `c` times its width in value
  (`Flow.IsNegativeGradient.dist_le_of_mem_stableSet`), so a point of the stable set close to
  `x` and with value close to `f x` never leaves the ball: it belongs to the confined local
  stable set of the Lyapunov--Perron construction.
* **Transport along the flow.** A point `y` of the stable set reaches, at some time `T`, the
  neighbourhood of `x` where the previous step applies and where the local straightening chart
  of `IsNondegenerateCriticalPoint.exists_localStableSet_chart` is defined. Composing that chart
  with the time-`T` flow, a `C¹` diffeomorphism of the ambient space, straightens the stable
  set around `y`.

Without the first step the transported chart would only straighten the part of the stable set
lying in the transported local disk; points of the stable set accumulating from far along the
flow could otherwise break embeddedness. For a gradient flow they cannot.

## Main declarations

* `IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_stableSet` and
  `IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_unstableSet`: near a
  nondegenerate critical point, stable and unstable trajectories stay in a given ball.
* `IsNondegenerateCriticalPoint.exists_stableSet_chart`: every point of the global stable set
  has a `C¹` straightening chart onto the stable Hessian subspace.
* `IsNondegenerateCriticalPoint.exists_unstableSet_chart`: the same for the unstable set and the
  unstable Hessian subspace.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open Filter Metric Set Topology
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {x : E}

namespace IsNondegenerateCriticalPoint

/-- Around a nondegenerate critical point the gradient is bounded below on thin annuli: inside
any given radius there is an annulus `ρ / 2 < dist w x < ρ` on which `c ≤ ‖∇ f w‖` for some
positive `c`. -/
private theorem exists_forall_le_norm_gradient (h : IsNondegenerateCriticalPoint f x) {r : ℝ}
    (hr : 0 < r) :
    ∃ ρ > 0, ρ ≤ r ∧ ∃ c > 0, ∀ w, ρ / 2 < dist w x → dist w x < ρ → c ≤ ‖∇ f w‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((h.contDiffAt.eventually (by simp)).and
      (eventually_nhdsWithin_iff.1 h.eventually_fderiv_ne_zero))
  set ρ := min r (ε / 2)
  have hρ : 0 < ρ := lt_min hr (half_pos hε)
  have hρε : ρ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hK : IsCompact (closedBall x ρ \ ball x (ρ / 2)) :=
    (isCompact_closedBall x ρ).diff isOpen_ball
  have hball' : ∀ w ∈ closedBall x ρ \ ball x (ρ / 2), w ∈ ball x ε :=
    fun w hw ↦ mem_ball.2 ((mem_closedBall.1 hw.1).trans_lt hρε)
  obtain ⟨c, hc, hcK⟩ := hK.exists_forall_le' (f := fun w ↦ ‖fderiv ℝ f w‖)
    (fun w hw ↦ ((hball w (hball' w hw)).1.continuousAt_fderiv two_ne_zero).norm
      |>.continuousWithinAt)
    (fun w hw ↦ norm_pos_iff.2 <| (hball w (hball' w hw)).2 fun hwx ↦ hw.2 <| by
      rw [mem_singleton_iff.1 hwx]
      exact mem_ball_self (half_pos hρ))
  refine ⟨ρ, hρ, min_le_left _ _, c, hc, fun w h₁ h₂ ↦ ?_⟩
  rw [norm_gradient_eq_norm_fderiv]
  exact hcK w ⟨mem_closedBall.2 h₂.le, fun hw ↦ lt_asymm h₁ (mem_ball.1 hw)⟩

variable {φ : _root_.Flow ℝ E}

/-- **Near a nondegenerate critical point, stable trajectories stay close.** For every radius
`r > 0`, every point near the critical point `x` whose negative-gradient trajectory converges to
`x` remains within distance `r` of `x` at all nonnegative times. Thus, near `x`, the stable set
coincides with the local stable set of trajectories confined to a ball. -/
theorem eventually_forall_dist_le_of_mem_stableSet (h : IsNondegenerateCriticalPoint f x)
    (hφ : Flow.IsNegativeGradient φ f) (hd : Differentiable ℝ f) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝 x, z ∈ Flow.stableSet φ x → ∀ t, 0 ≤ t → dist (φ t z) x ≤ r := by
  obtain ⟨ρ, hρ, hρr, c, hc, hgrad⟩ := h.exists_forall_le_norm_gradient hr
  have hgap : f x < f x + c * (ρ - ρ / 2) := lt_add_of_pos_right _ (by nlinarith)
  filter_upwards [ball_mem_nhds x (half_pos hρ),
    (hd.continuous.tendsto x).eventually_lt_const hgap] with z hzb hzf hz t ht
  exact (hφ.dist_le_of_mem_stableSet hz (fun _ ↦ hd _) hd.continuous.continuousAt hc.le hgrad
    (mem_ball.1 hzb).le hzf ht).trans hρr

/-- **Near a nondegenerate critical point, unstable trajectories stay close in backward time.**
The backward-time counterpart of
`IsNondegenerateCriticalPoint.eventually_forall_dist_le_of_mem_stableSet`. -/
theorem eventually_forall_dist_le_of_mem_unstableSet (h : IsNondegenerateCriticalPoint f x)
    (hφ : Flow.IsNegativeGradient φ f) (hd : Differentiable ℝ f) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ z in 𝓝 x, z ∈ Flow.unstableSet φ x → ∀ t, t ≤ 0 → dist (φ t z) x ≤ r := by
  obtain ⟨ρ, hρ, hρr, c, hc, hgrad⟩ := h.exists_forall_le_norm_gradient hr
  have hgap : f x - c * (ρ - ρ / 2) < f x := sub_lt_self _ (by nlinarith)
  filter_upwards [ball_mem_nhds x (half_pos hρ),
    (hd.continuous.tendsto x).eventually_const_lt hgap] with z hzb hzf hz t ht
  exact (hφ.dist_le_of_mem_unstableSet hz (fun _ ↦ hd _) hd.continuous.continuousAt hc.le hgrad
    (mem_ball.1 hzb).le hzf ht).trans hρr

variable [CompleteSpace E] {K : ℝ≥0}

omit [FiniteDimensional ℝ E] in
/-- Transport of a local straightening chart along the negative-gradient flow. Let `S` be an
invariant set which, on an open set `V` of points `w` with displacement `w - x` in the source of
a `C¹` chart `q` with `C¹` inverse, is cut out by `q (w - x) ∈ L`. If the trajectory of `y`
reaches `V` and the source of `q` at time `T`, then composing `q` with the time-`T` flow gives a
`C¹` chart around `y` cutting out `S` by the same condition. -/
private theorem exists_chart_of_isInvariant (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    {S : Set E} (hS : IsInvariant (negativeGradientFlow f hf) S) {q : OpenPartialHomeomorph E E}
    (hqC : ∀ z ∈ q.source, ContDiffAt ℝ 1 q z) (hqCs : ∀ z ∈ q.target, ContDiffAt ℝ 1 q.symm z)
    {L : Set E} {V : Set E} (hVo : IsOpen V)
    (hVS : ∀ w ∈ V, w - x ∈ q.source → (w ∈ S ↔ q (w - x) ∈ L)) {y : E} {T : ℝ}
    (hT : negativeGradientFlow f hf T y ∈ V ∧ negativeGradientFlow f hf T y - x ∈ q.source) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ S ↔ e z ∈ L := by
  set φ := negativeGradientFlow f hf
  let Ψ : E ≃ₜ E := (φ.toHomeomorph T).trans (Homeomorph.subRight x)
  let e := (Ψ.toOpenPartialHomeomorph.restrOpen _
    ((φ.toHomeomorph T).continuous.isOpen_preimage V hVo)).trans q
  have hesource : e.source = {z | φ T z ∈ V ∧ φ T z - x ∈ q.source} := by
    ext z
    simp [e, Ψ]
  have he : (e : E → E) = q ∘ fun z ↦ φ T z - x := by
    ext z
    simp [e, Ψ]
  have hes : (e.symm : E → E) = (fun z ↦ φ (-T) (z + x)) ∘ q.symm := by
    ext z
    simp [e, Ψ]
  refine ⟨e, by rw [hesource]; exact hT, fun z hz ↦ ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hesource] at hz
    rw [he]
    exact (hqC _ hz.2).comp z
      (((contDiff_negativeGradientFlow_apply f hf hfs T).sub contDiff_const).contDiffAt)
  · rw [OpenPartialHomeomorph.trans_target] at hz
    rw [hes]
    exact ((contDiff_negativeGradientFlow_apply f hf hfs (-T)).comp
      (contDiff_id.add contDiff_const)).contDiffAt.comp z (hqCs z hz.1)
  · rw [hesource] at hz
    rw [he]
    have hinv : z ∈ S ↔ φ T z ∈ S :=
      ⟨fun hz ↦ hS T hz, fun hz ↦ by
        simpa only [← _root_.Flow.map_add, neg_add_cancel, _root_.Flow.map_zero_apply] using
          hS (-T) hz⟩
    exact hinv.trans (hVS _ hz.1 hz.2)

/-- **The stable set of a Morse critical point is an embedded `C¹` submanifold.** For a globally
`C²` function with globally Lipschitz gradient, every point `y` of the stable set of a
nondegenerate critical point `x` under the negative-gradient flow has a `C¹` ambient chart,
with `C¹` inverse, carrying the stable set onto the stable Hessian subspace, whose dimension is
`finrank E - morseIndex f x`. -/
theorem exists_stableSet_chart (h : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {y : E}
    (hy : y ∈ Flow.stableSet (negativeGradientFlow f hf) x) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.stableSet (negativeGradientFlow f hf) x ↔
        e z ∈ h.contDiffAt.stableLinearSubspace := by
  obtain ⟨r, hr, ρ, hρ, q, hqs, -, -, -, hqC, hqCs, hqset, hconv⟩ :=
    h.exists_localStableSet_chart
  obtain ⟨V, hVconf, hVo, hxV⟩ := _root_.mem_nhds_iff.1
    (h.eventually_forall_dist_le_of_mem_stableSet (isNegativeGradient_negativeGradientFlow f hf)
      (hfs.differentiable (by norm_num)) hr)
  have hxq : x - x ∈ q.source := by simpa [hqs] using hρ
  obtain ⟨T, hT⟩ := ((Flow.mem_stableSet.1 hy).eventually ((hVo.inter
    (q.open_source.preimage (continuous_sub_right x))).mem_nhds ⟨hxV, hxq⟩)).exists
  refine exists_chart_of_isInvariant hfs hf (Flow.isInvariant_stableSet _ x) hqC hqCs hVo
    (fun w hwV hwq ↦ ?_) hT
  have hxw : x + (w - x) = w := add_sub_cancel x w
  rw [SetLike.mem_coe, ← hqset _ hwq, h.mem_localStableSet_iff_negativeGradientFlow hf, hxw]
  refine ⟨fun hw ↦ ⟨fun t ht ↦ ?_, ?_⟩, fun hmem ↦ ?_⟩
  · rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact hVconf hwV hw t ht
  · rw [hqs] at hwq
    exact (mem_ball_zero_iff.1 hwq).le
  · have := image_add_localInvariantSet_Ici_subset_stableSet hf h.stableProjection hconv
      ⟨w - x, (mem_localInvariantSet_Ici_iff_negativeGradientFlow hf _).2 (by rwa [hxw]), rfl⟩
    simpa only [hxw] using this

/-- **The unstable set of a Morse critical point is an embedded `C¹` submanifold.** The
backward-time counterpart of `IsNondegenerateCriticalPoint.exists_stableSet_chart`: every point
of the unstable set has a `C¹` ambient chart, with `C¹` inverse, carrying the unstable set onto
the unstable Hessian subspace, whose dimension is the Morse index. -/
theorem exists_unstableSet_chart (h : IsNondegenerateCriticalPoint f x) (hfs : ContDiff ℝ 2 f)
    (hf : LipschitzWith K (∇ f)) {y : E}
    (hy : y ∈ Flow.unstableSet (negativeGradientFlow f hf) x) :
    ∃ e : OpenPartialHomeomorph E E, y ∈ e.source ∧
      (∀ z ∈ e.source, ContDiffAt ℝ 1 e z) ∧
      (∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z) ∧
      ∀ z ∈ e.source, z ∈ Flow.unstableSet (negativeGradientFlow f hf) x ↔
        e z ∈ h.contDiffAt.unstableLinearSubspace := by
  obtain ⟨r, hr, ρ, hρ, q, hqs, -, -, -, hqC, hqCs, hqset, hconv⟩ :=
    h.exists_localUnstableSet_chart
  obtain ⟨V, hVconf, hVo, hxV⟩ := _root_.mem_nhds_iff.1
    (h.eventually_forall_dist_le_of_mem_unstableSet
      (isNegativeGradient_negativeGradientFlow f hf) (hfs.differentiable (by norm_num)) hr)
  have hxq : x - x ∈ q.source := by simpa [hqs] using hρ
  obtain ⟨T, hT⟩ := ((Flow.mem_unstableSet.1 hy).eventually ((hVo.inter
    (q.open_source.preimage (continuous_sub_right x))).mem_nhds ⟨hxV, hxq⟩)).exists
  refine exists_chart_of_isInvariant hfs hf (Flow.isInvariant_unstableSet _ x) hqC hqCs hVo
    (fun w hwV hwq ↦ ?_) hT
  have hxw : x + (w - x) = w := add_sub_cancel x w
  rw [SetLike.mem_coe, ← hqset _ hwq, h.mem_localUnstableSet_iff_negativeGradientFlow hf, hxw]
  refine ⟨fun hw ↦ ⟨fun t ht ↦ ?_, ?_⟩, fun hmem ↦ ?_⟩
  · rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact hVconf hwV hw t ht
  · rw [hqs] at hwq
    exact (mem_ball_zero_iff.1 hwq).le
  · have := image_add_localInvariantSet_Iic_subset_unstableSet hf h.unstableProjection hconv
      ⟨w - x, (mem_localInvariantSet_Iic_iff_negativeGradientFlow hf _).2 (by rwa [hxw]), rfl⟩
    simpa only [hxw] using this

end IsNondegenerateCriticalPoint

end TauCeti
