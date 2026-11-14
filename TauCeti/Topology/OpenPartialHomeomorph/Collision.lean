/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Order.LocalExtr

/-!
# Inverse radii at a minimal collision

Two distinct preimages minimizing the maximum of their norms have equal norms when they admit
open partial homeomorphism branches. The maximum of the inverse-branch norms has a local
minimum at their common image. Minimality is an explicit hypothesis; these results do not
assert existence of a minimizing collision.

The target needs only a topology. The equal-radius argument uses a real normed space, while
the local-minimum result only uses its normed additive group structure. These are the local
topological steps before applying Gauss' identity to inverse exponential branches.

## Main results

* `TauCeti.norm_eq_of_minimal_collision`: the preimages have equal norms.
* `TauCeti.isLocalMin_max_inverse_norm_of_minimal_collision`: inverse radii have a local minimum.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Theorem 1.36.
* Related public formalizations:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

section EqualRadius

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local inverse at the shorter member of a collision would lift a small
inward displacement of the longer member, contradicting minimality. -/
private theorem not_norm_lt_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hwv : ‖w‖ < ‖v‖) (heq : f v = f w) (hne : v ≠ w)
    (hf : ContinuousAt f v)
    (e : OpenPartialHomeomorph F X) (hw : w ∈ e.source)
    (he : EqOn f e e.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) : False := by
  obtain ⟨U, V, hU, hV, hvU, hwV, hdisj⟩ := t2_separation hne
  let W := V ∩ e.source ∩ Metric.ball (0 : F) ‖v‖
  have hwW : w ∈ W := ⟨⟨hwV, hw⟩, by simpa only [Metric.mem_ball, dist_zero_right] using hwv⟩
  have hW : IsOpen W := (hV.inter e.open_source).inter Metric.isOpen_ball
  have hpre : ∀ᶠ x in 𝓝 v, f x ∈ e '' W := by
    apply hf.preimage_mem_nhds
    rw [heq, he hw]
    exact e.image_mem_nhds hw (hW.mem_nhds hwW)
  -- The shorter preimage makes the radius positive. Closure of this open ball
  -- supplies an inward point in every prescribed neighborhood of the longer one.
  have hvpos : 0 < ‖v‖ := (norm_nonneg w).trans_lt hwv
  have hvcl : v ∈ closure (Metric.ball (0 : F) ‖v‖) := by
    rw [closure_ball (0 : F) hvpos.ne']
    simp only [Metric.mem_closedBall, dist_zero_right, le_refl]
  obtain ⟨x, hx, hxball⟩ := mem_closure_iff_nhds.mp hvcl _
    (inter_mem (hU.mem_nhds hvU) hpre)
  obtain ⟨y, hyW, hy⟩ := hx.2
  have hxv : ‖x‖ < ‖v‖ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxball
  have hyv : ‖y‖ < ‖v‖ := by simpa only [Metric.mem_ball, dist_zero_right] using hyW.2
  have hxy : x ≠ y := by
    intro h
    exact Set.disjoint_left.mp hdisj hx.1 (h.symm ▸ hyW.1.1)
  have hbound := hmin x
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxv.le.trans hv)
    y (by simpa only [Metric.mem_closedBall, dist_zero_right] using hyv.le.trans hv)
    (hy.symm.trans (he hyW.1.2).symm) hxy
  exact (not_lt_of_ge hbound) ((max_lt hxv hyv).trans_le (le_max_left _ _))

/-- The two preimages at a first collision have equal radius when both admit
local inverse branches. -/
theorem norm_eq_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) (heq : f v = f w) (hne : v ≠ w)
    (ev ew : OpenPartialHomeomorph F X) (hvs : v ∈ ev.source) (hws : w ∈ ew.source)
    (hev : EqOn f ev ev.source) (hew : EqOn f ew ew.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) : ‖v‖ = ‖w‖ := by
  have hfv : ContinuousAt f v := (ev.continuousAt hvs).congr
    (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).symm
  have hfw : ContinuousAt f w := (ew.continuousAt hws).congr
    (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).symm
  apply le_antisymm
  · by_contra h
    exact not_norm_lt_of_minimal_collision hv (lt_of_not_ge h) heq hne hfv ew hws hew hmin
  · by_contra h
    apply not_norm_lt_of_minimal_collision hw (lt_of_not_ge h) heq.symm hne.symm
      hfw ev hvs hev
    simpa only [max_comm ‖w‖ ‖v‖] using hmin

omit [NormedSpace ℝ F] in
/-- At a first collision, the maximum of the two inverse-branch radii has a
local minimum at the common endpoint. -/
theorem isLocalMin_max_inverse_norm_of_minimal_collision
    {f : F → X} {r : ℝ} {v w : F}
    (hv : ‖v‖ ≤ r) (hw : ‖w‖ ≤ r) (heq : f v = f w) (hne : v ≠ w)
    (ev ew : OpenPartialHomeomorph F X) (hvs : v ∈ ev.source) (hws : w ∈ ew.source)
    (hev : EqOn f ev ev.source) (hew : EqOn f ew ew.source)
    (hmin : ∀ x ∈ Metric.closedBall 0 r, ∀ y ∈ Metric.closedBall 0 r,
      f x = f y → x ≠ y → max ‖v‖ ‖w‖ ≤ max ‖x‖ ‖y‖) :
    IsLocalMin (fun q ↦ max ‖ev.symm q‖ ‖ew.symm q‖) (f v) := by
  have hvt : f v ∈ ev.target := (hev hvs).symm ▸ ev.map_source hvs
  have hwt : f v ∈ ew.target := heq.symm ▸ (hew hws).symm ▸ ew.map_source hws
  have hiv : ev.symm (f v) = v := by rw [hev hvs, ev.left_inv hvs]
  have hiw : ew.symm (f v) = w := by rw [heq, hew hws, ew.left_inv hws]
  have hnear : ∀ᶠ q in 𝓝 (f v), ev.symm q ≠ ew.symm q :=
    ((ev.continuousAt_symm hvt).ne_iff_eventually_ne
      (ew.continuousAt_symm hwt)).mp (by rwa [hiv, hiw])
  simp only [IsLocalMin, IsMinFilter, hiv, hiw]
  filter_upwards [hnear, ev.open_target.mem_nhds hvt, ew.open_target.mem_nhds hwt]
    with q hne' hqv hqw
  by_cases hvq : ‖ev.symm q‖ ≤ r
  · by_cases hwq : ‖ew.symm q‖ ≤ r
    · apply hmin (ev.symm q) (by simpa using hvq) (ew.symm q) (by simpa using hwq)
      · rw [hev (ev.map_target hqv), hew (ew.map_target hqw),
          ev.right_inv hqv, ew.right_inv hqw]
      · exact hne'
    · exact (max_le hv hw).trans ((le_of_not_ge hwq).trans (le_max_right _ _))
  · exact (max_le hv hw).trans ((le_of_not_ge hvq).trans (le_max_left _ _))

end EqualRadius

end TauCeti
