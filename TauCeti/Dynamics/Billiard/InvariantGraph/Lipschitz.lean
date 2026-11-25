/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.RotationNumber
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Invariant graphs of the billiard map are Lipschitz

Let `χ` be a `C²` strictly convex billiard table with period `L` and next-collision map
`B(s, v) = (t(s, v), w(s, v))` on the strip `ℝ × (-1, 1)`, and let `ψ` be an invariant graph
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph`). This file proves that `ψ` is Lipschitz,
with Lipschitz constant at most the largest of the ratios `|∂_v w / ∂_v t|` of `B` at the points
`(s, ψ(s))` of the graph and the same ratios at the points `(s, -ψ(s))` of the reversed graph; the
latter are, up to sign, the ratios `∂_w v / ∂_w s` of `B⁻¹` at the points of the graph, since
`B⁻¹ = ι ∘ B ∘ ι` up to a period for the time reversal `ι(s, v) = (s, -v)`. More precisely, `ψ`
is `K`-Lipschitz as soon as all these ratios `∂_v w / ∂_v t`, without absolute values, are at least
`-K` (`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.lipschitzWith_of_forall_le`). The ratios
are continuous and `L`-periodic along the graph, so such a bound exists
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.exists_lipschitzWith`).

The route is Birkhoff's comparison of the graph with the image of a vertical. Let `p = B(s', ψ(s'))`
be a point of the graph, with first coordinate `x₀`. The image `v ↦ B(s', v)` of the vertical
through `(s', ψ(s'))` passes through `p`. For `v < ψ(s')` its point `B(s', v) = (z, w(s', v))` lies
to the right of `p`, and the graph lies above it there: the point `(z, ψ(z))` of the graph is the
image of a state `(s, ψ(s))` with `s > s'`, and the inverse map, which on the vertical through `z`
is `w ↦ t(z, -w) - L`, is strictly increasing in `w`
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.nextTangential_lt_apply_nextParam`). So the
right difference quotients of `ψ` at `x₀` are, along `z = t(s', v)` with `v ↑ ψ(s')`, larger than
those of the image curve, which tend to `∂_v w / ∂_v t` at `(s', ψ(s'))`. This bounds the lower
right Dini derivative of `ψ` from below; applied to the reversed graph `-ψ`, it bounds the upper
right Dini derivative from above, and a continuous function with bounded right Dini derivatives is
Lipschitz (`image_le_of_liminf_slope_right_le_deriv_boundary`).

## References

* Michael-R. Herman, *Sur les courbes invariantes par les difféomorphismes de l'anneau*, Vol. 1,
  Astérisque 103–104, 1983, Chapitre I, 2.2 and 5.2.
-/

public section

noncomputable section

open Function Set Filter Topology NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} {χ : StrictConvexBilliardTable o}

/-- The ratio `∂_v w / ∂_v t` of the partial derivatives in `v` of the next tangential component
`w(s, v)` and the next collision parameter `t(s, v)`: the slope at `B(s, v)` of the image under
the next-collision map `B` of the vertical through `(s, v)`. -/
def verticalImageSlope (χ : StrictConvexBilliardTable o) (s v : ℝ) : ℝ :=
  deriv (χ.nextTangential s) v / deriv (χ.nextParam s) v

theorem verticalImageSlope_def (s v : ℝ) :
    χ.verticalImageSlope s v = deriv (χ.nextTangential s) v / deriv (χ.nextParam s) v :=
  (rfl)

/-- The slope of the image of the vertical is `L`-periodic in `s`. -/
theorem verticalImageSlope_add_period {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.verticalImageSlope (s + χ.period) v = χ.verticalImageSlope s v := by
  have hnhds := Ioo_mem_nhds hv.1 hv.2
  have hT : χ.nextParam (s + χ.period) =ᶠ[𝓝 v] fun u ↦ χ.nextParam s u + χ.period :=
    Filter.eventuallyEq_of_mem hnhds fun u hu ↦ χ.nextParam_add_period hu
  have hW : χ.nextTangential (s + χ.period) =ᶠ[𝓝 v] χ.nextTangential s :=
    Filter.eventuallyEq_of_mem hnhds fun u hu ↦ χ.nextTangential_add_period hu
  rw [verticalImageSlope_def, verticalImageSlope_def, hT.deriv_eq, hW.deriv_eq, deriv_add_const]

/-- Along a continuous curve `s ↦ (s, φ(s))` in the open strip, the slope of the image of the
vertical is continuous, for a `C²` table. -/
theorem continuous_verticalImageSlope (hχ : ContDiff ℝ 2 χ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφI : ∀ s, φ s ∈ Ioo (-1) 1) : Continuous fun s ↦ χ.verticalImageSlope s (φ s) := by
  simp only [verticalImageSlope_def]
  refine Continuous.div ?_ ?_ fun s ↦ (χ.deriv_nextParam_neg (hφI s)).ne
  · exact continuous_deriv_slice_right_graph (u := fun x : ℝ × ℝ ↦ χ.nextTangential x.1 x.2) hφ
      fun s ↦ χ.contDiffAt_nextTangential (hχ.contDiffAt.of_le (by norm_num))
        (hχ.contDiffAt.of_le (by norm_num)) (hφI s)
  · exact continuous_deriv_slice_right_graph (u := fun x : ℝ × ℝ ↦ χ.nextParam x.1 x.2) hφ
      fun s ↦ χ.contDiffAt_nextParam (hχ.contDiffAt.of_le (by norm_num))
        (hχ.contDiffAt.of_le (by norm_num)) (hφI s)

namespace IsInvariantGraph

variable {ψ : ℝ → ℝ} (h : χ.IsInvariantGraph ψ)
include h

/-- **The graph lies above the image of a vertical, to the right.** Let `(s', ψ(s'))` be a point
of an invariant graph of a `C²` table and `v < ψ(s')` a height in `(-1, 1)`. The image
`B(s', v) = (z, w(s', v))` of the point below it lies strictly below the graph: `w(s', v) < ψ(z)`.
-/
theorem nextTangential_lt_apply_nextParam (hχ : ContDiff ℝ 2 χ) {s' v : ℝ}
    (hv : v ∈ Ioo (-1) 1) (hvψ : v < ψ s') :
    χ.nextTangential s' v < ψ (χ.nextParam s' v) := by
  set z := χ.nextParam s' v
  obtain ⟨s, hs⟩ := h.surjective_graphLift hχ z
  -- The state of the graph above `z` comes from a state `s > s'`.
  have hzx : χ.graphLift ψ s' < z := by
    rw [graphLift_def]
    exact χ.strictAntiOn_nextParam s' hv (h.mem_Ioo s') hvψ
  have hss' : s' < s := (h.strictMono_graphLift hχ).lt_iff_lt.1 (hs ▸ hzx)
  -- On the vertical through `z`, the inverse map is strictly increasing in the height.
  have h₁ : χ.nextParam z (-ψ z) = s + χ.period := by
    have := h.graphLift_neg_graphLift s
    rwa [hs, graphLift_def, Pi.neg_apply] at this
  have h₂ : χ.nextParam z (-χ.nextTangential s' v) = s' + χ.period :=
    χ.nextParam_nextParam_neg_nextTangential hv
  have hw := χ.nextTangential_mem_Ioo (s := s') hv
  have hψz := h.mem_Ioo z
  by_contra! hle
  have := (χ.strictAntiOn_nextParam z).antitoneOn ⟨neg_lt_neg hw.2, neg_lt.1 hw.1⟩
    ⟨neg_lt_neg hψz.2, neg_lt.1 hψz.1⟩ (neg_le_neg hle)
  linarith

/-- **Lower bound on the right Dini derivative.** At the point `x₀ = t(s', ψ(s'))` of an invariant
graph of a `C²` table, the right difference quotients of `ψ` exceed every `r` below the slope
`∂_v w / ∂_v t` of the image of the vertical at `(s', ψ(s'))`, for points `z` arbitrarily close to
`x₀` on the right. -/
theorem frequently_lt_slope (hχ : ContDiff ℝ 2 χ) (s' : ℝ) {r : ℝ}
    (hr : r < χ.verticalImageSlope s' (ψ s')) :
    ∃ᶠ z in 𝓝[>] (χ.graphLift ψ s'), r < slope ψ (χ.graphLift ψ s') z := by
  rw [graphLift_def]
  set v₀ := ψ s'
  have hv₀ := h.mem_Ioo s'
  set T := χ.nextParam s'
  set W := χ.nextTangential s'
  have hT := χ.hasDerivAt_nextParam (s := s') hv₀
  have hT' : deriv T v₀ ≠ 0 := (χ.deriv_nextParam_neg hv₀).ne
  rw [← hT.deriv] at hT
  have hW := χ.hasDerivAt_nextTangential (s := s') hχ.contDiffAt hχ.contDiffAt hv₀
  -- The difference quotients of the image curve tend to `∂_v w / ∂_v t`.
  have hlim : Tendsto (fun v ↦ slope W v₀ v / slope T v₀ v) (𝓝[<] v₀)
      (𝓝 (χ.verticalImageSlope s' v₀)) :=
    ((hasDerivAt_iff_tendsto_slope.1 hW).mono_left (nhdsWithin_mono _ fun _ h ↦ ne_of_lt h)).div
      ((hasDerivAt_iff_tendsto_slope.1 hT).mono_left (nhdsWithin_mono _ fun _ h ↦ ne_of_lt h)) hT'
  -- Points `T v` with `v < v₀` lie to the right of `x₀ = T v₀`.
  have hTlim : Tendsto T (𝓝[<] v₀) (𝓝[>] (T v₀)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hT.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) <| by
        filter_upwards [Ioo_mem_nhdsLT hv₀.1] with v hv
        exact χ.strictAntiOn_nextParam s' ⟨hv.1, hv.2.trans hv₀.2⟩ hv₀ hv.2
  refine hTlim.frequently (Eventually.frequently ?_)
  filter_upwards [hlim.eventually (lt_mem_nhds hr), Ioo_mem_nhdsLT hv₀.1] with v hv hv'
  have hvI : v ∈ Ioo (-1) 1 := ⟨hv'.1, hv'.2.trans hv₀.2⟩
  have hTv : T v₀ < T v := χ.strictAntiOn_nextParam s' hvI hv₀ hv'.2
  have hgraph := h.nextTangential_lt_apply_nextParam hχ hvI hv'.2
  have hx₀ : ψ (T v₀) = W v₀ := (h.nextTangential_eq s').symm
  rw [slope_def_field, slope_def_field, div_div_div_cancel_right₀ (sub_ne_zero.2 hv'.2.ne)]
    at hv
  rw [slope_def_field, hx₀]
  refine hv.trans ((div_lt_div_iff_of_pos_right (sub_pos.2 hTv)).2 ?_)
  linarith

/-- If the slopes of the images of the verticals along an invariant graph are at least `-K`, the
graph drops by at most `K (b - a)` from `a` to `b ≥ a`. -/
private theorem sub_le_mul_of_forall_le (hχ : ContDiff ℝ 2 χ) {K : ℝ}
    (hK : ∀ s, -K ≤ χ.verticalImageSlope s (ψ s)) {a b : ℝ} (hab : a ≤ b) :
    ψ a - ψ b ≤ K * (b - a) := by
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := -ψ) (a := a) (b := b)
    h.continuous.neg.continuousOn (B := fun x ↦ -ψ a + K * (x - a)) (B' := fun _ ↦ K)
    (by simp) (by fun_prop) (fun x _ ↦ ?_) (fun x _ r hr ↦ ?_) ⟨hab, le_rfl⟩
  · simp only [Pi.neg_apply] at key
    linarith
  · simpa using ((hasDerivAt_id x).sub_const a |>.const_mul K |>.const_add (-ψ a)).hasDerivWithinAt
  · obtain ⟨s', rfl⟩ := h.surjective_graphLift hχ x
    refine (h.frequently_lt_slope hχ s' (r := -r) (by linarith [hK s'])).mono fun z hz ↦ ?_
    simp only [slope_neg_fun, Pi.neg_apply]
    linarith

/-- **Invariant graphs are Lipschitz, with explicit constant.** An invariant graph `ψ` of a `C²`
table is `K`-Lipschitz as soon as the slopes `∂_v w / ∂_v t` of the images of the verticals are at
least `-K` at the points `(s, ψ(s))` of the graph and at the points `(s, -ψ(s))` of the reversed
graph. This holds when `K` bounds the absolute values of these slopes, which at the points of the
reversed graph are the corresponding slopes for the inverse map at the points of the graph. -/
theorem lipschitzWith_of_forall_le (hχ : ContDiff ℝ 2 χ) {K : ℝ≥0}
    (hK : ∀ s, -(K : ℝ) ≤ χ.verticalImageSlope s (ψ s))
    (hK' : ∀ s, -(K : ℝ) ≤ χ.verticalImageSlope s (-ψ s)) : LipschitzWith K ψ := by
  have hneg := h.neg hχ
  have key {a b : ℝ} (hab : a ≤ b) : |ψ b - ψ a| ≤ K * (b - a) := by
    have h₁ := h.sub_le_mul_of_forall_le hχ hK hab
    have h₂ := hneg.sub_le_mul_of_forall_le hχ hK' hab
    simp only [Pi.neg_apply] at h₂
    exact abs_le.2 ⟨by linarith, by linarith⟩
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_sub_comm x, abs_of_nonneg (sub_nonneg.2 hxy)]
    exact key hxy
  · rw [abs_of_nonneg (sub_nonneg.2 hxy)]
    exact key hxy

/-- **Invariant graphs are Lipschitz.** Every invariant graph of a `C²` table is Lipschitz: the
slopes of the images of the verticals are continuous and `L`-periodic along the graph and along
the reversed graph, hence bounded. -/
theorem exists_lipschitzWith (hχ : ContDiff ℝ 2 χ) : ∃ K, LipschitzWith K ψ := by
  have hbdd {φ : ℝ → ℝ} (hφ : χ.IsInvariantGraph φ) :
      ∃ m, ∀ s, m ≤ χ.verticalImageSlope s (φ s) := by
    have hper : Periodic (fun s ↦ χ.verticalImageSlope s (φ s)) χ.period := fun s ↦ by
      simp only [hφ.periodic s, verticalImageSlope_add_period (hφ.mem_Ioo s)]
    obtain ⟨m, hm⟩ := (hper.compact_of_continuous χ.period_pos.ne'
      (continuous_verticalImageSlope hχ hφ.continuous hφ.mem_Ioo)).bddBelow
    exact ⟨m, fun s ↦ hm (mem_range_self s)⟩
  obtain ⟨m, hm⟩ := hbdd h
  obtain ⟨m', hm'⟩ := hbdd (h.neg hχ)
  simp only [Pi.neg_apply] at hm'
  refine ⟨Real.toNNReal (max (-m) (-m')), h.lipschitzWith_of_forall_le hχ (fun s ↦ ?_)
    (fun s ↦ ?_)⟩
  · have := Real.le_coe_toNNReal (max (-m) (-m'))
    linarith [hm s, le_max_left (-m) (-m')]
  · have := Real.le_coe_toNNReal (max (-m) (-m'))
    linarith [hm' s, le_max_right (-m) (-m')]

end IsInvariantGraph

end StrictConvexBilliardTable

end TauCeti
