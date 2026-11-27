/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.ApproximateTangentSpace
public import TauCeti.Geometry.MeasureTheory.Rectifiable.Tangent.Submodule
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Examples.Geometry.MeasureTheory.ApproximateTangentSpace
import TauCeti.Analysis.Normed.Module.FiniteDimension.Closedness
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Check: the union of the two coordinate axes

Let `M = L₁ ∪ L₂` be the union of two distinct lines through `0` in a finite-dimensional real
inner product space `V`, for instance the two coordinate axes of `ℝ²`, and `k = 1`.

* *At the origin.* `M` is a cone, so the blow-ups of `H¹⌞M` at `0` are `H¹⌞M` itself
  (`blowUp_euclideanHausdorffMeasure_restrict_union`), which is not a multiple of `H¹` on a line:
  `H¹⌞M` has no approximate tangent line at `0` in the integral formulation
  (`not_hasApproxTangentSpace_zero`). In the density formulation of Tau Ceti's
  `TauCeti.IsApproximateTangentPlane`, `M` has no approximate tangent line at `0` either
  (`not_exists_isApproximateTangentPlane_zero`), since the line not contained in a candidate `P`
  lies outside a cone about `P` and has density one
  (`TauCeti.not_densityZeroOutsideCones_of_not_le`).
* *Away from the origin.* At every other point `x` of `L₁` the tangent line is `L₁`, in both
  formulations (`hasApproxTangentSpace_of_mem`, `isApproximateTangentPlane_iff_of_mem`), because
  near `x` the set `M` coincides with `L₁`.

So the almost-everywhere existence theorem
(`TauCeti.CountablyRectifiable.ae_existsUnique_isApproximateTangentPlane`) could not hold at every
point. The statements for the coordinate axes of `ℝ²` are `not_hasApproxTangentSpace_axes_zero`,
`not_exists_isApproximateTangentPlane_axes_zero`, `hasApproxTangentSpace_axes_of_mem_xAxis` and
`isApproximateTangentPlane_axes_iff_of_mem_xAxis`, and their `y`-axis versions.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent spaces).
-/

open MeasureTheory Measure Set Metric Module Filter Topology
open scoped ENNReal NNReal

public noncomputable section

namespace TauCeti.Examples.CoordinateAxes

open TauCeti

section Lines

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {L L₁ L₂ T : Submodule ℝ V}

variable [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] in
/-- A union of two subspaces is a cone, so its `k`-dimensional blow-ups at `0` are the
restriction of `μHE[k]` to it. -/
theorem blowUp_euclideanHausdorffMeasure_restrict_union {k : ℕ} {r : ℝ} (hr : 0 < r) :
    (μHE[k].restrict ((L₁ : Set V) ∪ L₂)).blowUp k 0 r = μHE[k].restrict ((L₁ : Set V) ∪ L₂) := by
  rw [blowUp_restrict hr.ne', blowUp_euclideanHausdorffMeasure hr]
  congr 1
  ext z
  simp [Submodule.smul_mem_iff _ hr.ne']

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Reduction at the vertex: since two distinct lines cannot both lie in a line `T`, the union
`L₁ ∪ L₂` is `L ∪ L'` for lines `L` and `L'` that meet only at `0`, with `L` not contained in
`T`. -/
private theorem exists_union_eq_of_not_le (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) (hT : finrank ℝ T = 1) :
    ∃ L L' : Submodule ℝ V, finrank ℝ L = 1 ∧ finrank ℝ L' = 1 ∧ Disjoint L L' ∧ ¬ L ≤ T ∧
      (L : Set V) ∪ L' = (L₁ : Set V) ∪ L₂ := by
  have a₁ := Submodule.isAtom_iff_finrank_eq_one.2 h₁
  have a₂ := Submodule.isAtom_iff_finrank_eq_one.2 h₂
  have aT := Submodule.isAtom_iff_finrank_eq_one.2 hT
  rcases not_and_or.1 fun h : L₁ ≤ T ∧ L₂ ≤ T ↦
    hne (((aT.le_iff_eq a₁.ne_bot).1 h.1).trans ((aT.le_iff_eq a₂.ne_bot).1 h.2).symm) with h | h
  · exact ⟨L₁, L₂, h₁, h₂, a₁.disjoint_of_ne a₂ hne, h, rfl⟩
  · exact ⟨L₂, L₁, h₂, h₁, a₂.disjoint_of_ne a₁ hne.symm, h, union_comm _ _⟩

/-- **No approximate tangent line at the vertex, density formulation.** The union of two distinct
lines through `0` has no approximate tangent `1`-plane at `0`. -/
theorem not_exists_isApproximateTangentPlane_zero (h₁ : finrank ℝ L₁ = 1)
    (h₂ : finrank ℝ L₂ = 1) (hne : L₁ ≠ L₂) :
    ¬ ∃ P : Submodule ℝ V, IsApproximateTangentPlane 1 ((L₁ : Set V) ∪ L₂) 0 P := by
  rintro ⟨P, hP⟩
  obtain ⟨L, _, -, -, -, hLP, hM⟩ := exists_union_eq_of_not_le h₁ h₂ hne hP.finrank_eq
  rw [← hM] at hP
  exact not_densityZeroOutsideCones_of_not_le
    (fun z hz ↦ (zero_add z).symm ▸ subset_union_left hz) hLP hP.densityZeroOutsideCones

/-- The canonical approximate tangent line of the union of two distinct lines at `0` is the
default `⊥`. -/
theorem approximateTangentPlane_zero (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) : approximateTangentPlane 1 ((L₁ : Set V) ∪ L₂) 0 = ⊥ :=
  approximateTangentPlane_eq_bot_of_not_exists (not_exists_isApproximateTangentPlane_zero h₁ h₂ hne)

omit [MeasurableSpace V] [BorelSpace V] in
/-- Near a point `x ≠ 0` of `L₁`, the union `L₁ ∪ L₂` of two distinct lines coincides with `L₁`. -/
private theorem union_eventuallyEq (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) {x : V} (hx : x ∈ L₁) (hx0 : x ≠ 0) :
    ((L₁ : Set V) ∪ L₂ : Set V) =ᶠ[𝓝 x] (L₁ : Set V) := by
  have hx₂ : x ∉ L₂ := fun hx₂ ↦ hx0 <| Submodule.disjoint_def.1
    ((Submodule.isAtom_iff_finrank_eq_one.2 h₁).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.2 h₂) hne) x hx hx₂
  filter_upwards [L₂.isClosed_of_finiteDimensional.isOpen_compl.mem_nhds hx₂] with y hy
  simp only [mem_compl_iff, SetLike.mem_coe] at hy
  simp [hy]

/-- **The tangent line away from the vertex, density formulation.** At a point `x ≠ 0` of `L₁`,
the approximate tangent `1`-planes of `L₁ ∪ L₂` are exactly `L₁`. -/
theorem isApproximateTangentPlane_iff_of_mem (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) {x : V} (hx : x ∈ L₁) (hx0 : x ≠ 0) {Q : Submodule ℝ V} :
    IsApproximateTangentPlane 1 ((L₁ : Set V) ∪ L₂) x Q ↔ Q = L₁ := by
  rw [IsApproximateTangentPlane.congr_nhds (union_eventuallyEq h₁ h₂ hne hx hx0), ← h₁]
  exact L₁.isApproximateTangentPlane_iff hx

/-- No approximate tangent line at the vertex, integral formulation, for a line `L₁` that is not
contained in the candidate `T`. -/
private theorem not_hasApproxTangentSpace_zero_of_not_le (h₁ : finrank ℝ L₁ = 1)
    (h₂ : finrank ℝ L₂ = 1) (h₁₂ : Disjoint L₁ L₂) (hT : finrank ℝ T = 1) (hLT : ¬ L₁ ≤ T)
    (θ : ℝ≥0) : ¬ (μHE[1].restrict ((L₁ : Set V) ∪ L₂)).HasApproxTangentSpace 0 T θ := by
  intro h
  have : IsLocallyFiniteMeasure (μHE[1].restrict (L₁ : Set V)) := h₁ ▸ inferInstance
  have : IsLocallyFiniteMeasure (μHE[1].restrict (L₂ : Set V)) := h₂ ▸ inferInstance
  have := isLocallyFiniteMeasure_of_le (restrict_union_le (μ := μHE[1]) (L₁ : Set V) L₂)
  obtain ⟨v, hvL, hvT⟩ := IsConcreteLE.not_le_iff_exists.mp hLT
  have hv0 : v ≠ 0 := fun hv ↦ hvT (hv ▸ T.zero_mem)
  have hdT := Submodule.infDist_pos_of_notMem hvT
  have hd₂ := Submodule.infDist_pos_of_notMem
    fun hv₂ ↦ hv0 (Submodule.disjoint_def.1 h₁₂ v hvL hv₂)
  set d := min (infDist v (T : Set V)) (infDist v (L₂ : Set V)) / 2
  have hd : 0 < d := by positivity
  have hdT' : d < infDist v (T : Set V) := by
    simp only [d]; linarith [min_le_left (infDist v (T : Set V)) (infDist v (L₂ : Set V))]
  have hd₂' : d < infDist v (L₂ : Set V) := by
    simp only [d]; linarith [min_le_right (infDist v (T : Set V)) (infDist v (L₂ : Set V))]
  -- the closed ball of radius `d` about `v` misses `T` and `L₂`
  have hdisj {S : Submodule ℝ V} (hS : d < infDist v (S : Set V)) :
      closedBall v d ∩ (S : Set V) = ∅ := by
    refine eq_empty_of_forall_notMem fun z ⟨hz, hzS⟩ ↦ ?_
    have := infDist_le_dist_of_mem (x := v) hzS
    rw [mem_closedBall, dist_comm] at hz
    linarith
  have hT0 : μHE[finrank ℝ T].restrict (T : Set V) (closedBall v d) = 0 := by
    rw [Measure.restrict_apply measurableSet_closedBall, hdisj hdT', measure_empty]
  have hlim := h.tendsto_blowUp_apply measurableSet_ball isBounded_ball
    (measure_mono_null (frontier_ball_subset_sphere.trans sphere_subset_closedBall) hT0)
  rw [measure_mono_null ball_subset_closedBall hT0, mul_zero, hT] at hlim
  -- the blow-up masses of `ball v d` are the constant length `2d` of a segment of `L₁`
  have hconst : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (μHE[1].restrict ((L₁ : Set V) ∪ L₂)).blowUp 1 0 r (ball v d) =
        volume (ball (0 : EuclideanSpace ℝ (Fin 1)) d) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hseg := Submodule.euclideanHausdorffMeasure_restrict_apply_ball hvL d
    rw [h₁] at hseg
    have hb : ball v d ∩ (L₂ : Set V) = ∅ :=
      eq_empty_of_subset (inter_subset_inter_left _ ball_subset_closedBall) (hdisj hd₂')
    rw [blowUp_euclideanHausdorffMeasure_restrict_union hr, ← hseg,
      Measure.restrict_apply measurableSet_ball, Measure.restrict_apply measurableSet_ball,
      inter_union_distrib_left, hb, union_empty]
  exact (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 1)) hd).ne'
    (tendsto_nhds_unique (tendsto_const_nhds.congr' (hconst.mono fun _ h ↦ h.symm)) hlim)

/-- **No approximate tangent line at the vertex, integral formulation.** The blow-ups of `H¹⌞M` at
`0`, for `M` the union of two distinct lines through `0`, are `H¹⌞M` itself, which is not a
multiple of `H¹` on a line: `H¹⌞M` has no approximate tangent line at `0`. -/
theorem not_hasApproxTangentSpace_zero (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) (hT : finrank ℝ T = 1) (θ : ℝ≥0) :
    ¬ (μHE[1].restrict ((L₁ : Set V) ∪ L₂)).HasApproxTangentSpace 0 T θ := by
  obtain ⟨L, L', hL, hL', hLL', hLT, hM⟩ := exists_union_eq_of_not_le h₁ h₂ hne hT
  rw [← hM]
  exact not_hasApproxTangentSpace_zero_of_not_le hL hL' hLL' hT hLT θ

/-- **The tangent line away from the vertex, integral formulation.** At a point `x ≠ 0` of `L₁`,
`H¹⌞(L₁ ∪ L₂)` has approximate tangent space `L₁` with multiplicity `1`. -/
theorem hasApproxTangentSpace_of_mem (h₁ : finrank ℝ L₁ = 1) (h₂ : finrank ℝ L₂ = 1)
    (hne : L₁ ≠ L₂) {x : V} (hx : x ∈ L₁) (hx0 : x ≠ 0) :
    (μHE[1].restrict ((L₁ : Set V) ∪ L₂)).HasApproxTangentSpace x L₁ 1 := by
  -- near `x` the union coincides with `L₁`, so the two measures agree on a neighbourhood of `x`
  obtain ⟨U, hUM, hU, hxU⟩ := _root_.eventually_nhds_iff.1 (union_eventuallyEq h₁ h₂ hne hx hx0)
  have hrestr : (μHE[1].restrict ((L₁ : Set V) ∪ L₂)).restrict U =
      (μHE[1].restrict (L₁ : Set V)).restrict U := by
    rw [Measure.restrict_restrict hU.measurableSet, Measure.restrict_restrict hU.measurableSet]
    exact congrArg _ (ext fun y ↦ and_congr_right fun hy ↦ hUM y hy)
  rw [hasApproxTangentSpace_congr_restrict (hU.mem_nhds hxU) hrestr]
  have h := L₁.toAffineSubspace.hasApproxTangentSpace_smul_euclideanHausdorffMeasure_restrict
    (by simpa using hx) one_ne_zero
  rwa [Submodule.toAffineSubspace_direction, h₁, one_smul, Submodule.coe_toAffineSubspace] at h

end Lines

section Axes

open TauCeti.Examples.ApproxTangentSpace

/-- The `y`-axis `ℝ e₁` of the plane. -/
def yAxis : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ℝ ∙ EuclideanSpace.single 1 1

/-- The `y`-axis is the span of `e₁`. -/
theorem yAxis_eq_span : yAxis = ℝ ∙ EuclideanSpace.single 1 1 :=
  (rfl)

/-- The `y`-axis is a line. -/
theorem finrank_yAxis : finrank ℝ yAxis = 1 :=
  finrank_span_singleton (by simp)

/-- The two coordinate axes are distinct. -/
theorem xAxis_ne_yAxis : xAxis ≠ yAxis := by
  intro h
  have : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈ yAxis :=
    h ▸ xAxis_eq_span ▸ Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (yAxis_eq_span ▸ this)
  simpa using congrArg (· 0) ha

/-- The union of the coordinate axes of `ℝ²`. -/
def axes : Set (EuclideanSpace ℝ (Fin 2)) :=
  (xAxis : Set (EuclideanSpace ℝ (Fin 2))) ∪ yAxis

/-- The union of the coordinate axes is `xAxis ∪ yAxis`. -/
theorem axes_eq : axes = (xAxis : Set (EuclideanSpace ℝ (Fin 2))) ∪ yAxis :=
  (rfl)

/-- The blow-ups of `H¹⌞M` at `0`, for `M` the union of the coordinate axes, are `H¹⌞M`. -/
theorem blowUp_axes {r : ℝ} (hr : 0 < r) :
    (μHE[1].restrict axes).blowUp 1 0 r = μHE[1].restrict axes := by
  rw [axes_eq]
  exact blowUp_euclideanHausdorffMeasure_restrict_union hr

/-- `H¹⌞M`, for `M` the union of the coordinate axes of `ℝ²`, has no approximate tangent line at
the origin. -/
theorem not_hasApproxTangentSpace_axes_zero {T : Submodule ℝ (EuclideanSpace ℝ (Fin 2))}
    (hT : finrank ℝ T = 1) (θ : ℝ≥0) :
    ¬ (μHE[1].restrict axes).HasApproxTangentSpace 0 T θ := by
  rw [axes_eq]
  exact not_hasApproxTangentSpace_zero finrank_xAxis finrank_yAxis xAxis_ne_yAxis hT θ

/-- The union of the coordinate axes of `ℝ²` has no approximate tangent `1`-plane at the origin,
in the density formulation. -/
theorem not_exists_isApproximateTangentPlane_axes_zero :
    ¬ ∃ P : Submodule ℝ (EuclideanSpace ℝ (Fin 2)), IsApproximateTangentPlane 1 axes 0 P := by
  rw [axes_eq]
  exact not_exists_isApproximateTangentPlane_zero finrank_xAxis finrank_yAxis xAxis_ne_yAxis

/-- At a point `x ≠ 0` of the `x`-axis, `H¹⌞M` has approximate tangent space the `x`-axis with
multiplicity `1`. -/
theorem hasApproxTangentSpace_axes_of_mem_xAxis {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ xAxis)
    (hx0 : x ≠ 0) : (μHE[1].restrict axes).HasApproxTangentSpace x xAxis 1 := by
  rw [axes_eq]
  exact hasApproxTangentSpace_of_mem finrank_xAxis finrank_yAxis xAxis_ne_yAxis hx hx0

/-- At a point `x ≠ 0` of the `y`-axis, `H¹⌞M` has approximate tangent space the `y`-axis with
multiplicity `1`. -/
theorem hasApproxTangentSpace_axes_of_mem_yAxis {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ yAxis)
    (hx0 : x ≠ 0) : (μHE[1].restrict axes).HasApproxTangentSpace x yAxis 1 := by
  rw [axes_eq, union_comm]
  exact hasApproxTangentSpace_of_mem finrank_yAxis finrank_xAxis xAxis_ne_yAxis.symm hx hx0

/-- At a point `x ≠ 0` of the `x`-axis, the approximate tangent `1`-planes of the union of the
axes are exactly the `x`-axis. -/
theorem isApproximateTangentPlane_axes_iff_of_mem_xAxis {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ xAxis) (hx0 : x ≠ 0) {Q : Submodule ℝ (EuclideanSpace ℝ (Fin 2))} :
    IsApproximateTangentPlane 1 axes x Q ↔ Q = xAxis := by
  rw [axes_eq]
  exact isApproximateTangentPlane_iff_of_mem finrank_xAxis finrank_yAxis xAxis_ne_yAxis hx hx0

/-- At a point `x ≠ 0` of the `y`-axis, the approximate tangent `1`-planes of the union of the
axes are exactly the `y`-axis. -/
theorem isApproximateTangentPlane_axes_iff_of_mem_yAxis {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ yAxis) (hx0 : x ≠ 0) {Q : Submodule ℝ (EuclideanSpace ℝ (Fin 2))} :
    IsApproximateTangentPlane 1 axes x Q ↔ Q = yAxis := by
  rw [axes_eq, union_comm]
  exact isApproximateTangentPlane_iff_of_mem finrank_yAxis finrank_xAxis xAxis_ne_yAxis.symm hx
    hx0

end Axes

end TauCeti.Examples.CoordinateAxes
