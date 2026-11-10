/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-!
# Vector fields read in a chart

A vector field `w` on the model space `E` of a manifold `M`, read in the extended chart at a point
`x` and extended by zero outside the chart domain, is a vector field `chartField x w` on `M`. It is
smooth when `w` is smooth and supported in a compact subset of the chart target, and a straight
segment in the chart along which `w` is constant is an integral curve of it.

The basic case is a constant field `v` cut off by a bump function `ρ` in the chart at `x`: the
field `bumpChartField x ρ v` is compactly supported, and near `x` its flow lines are the straight
lines in direction `v`. These are the coordinate motions used to move points of a manifold, as in
Milnor's proof of the homogeneity lemma.

## Main declarations

* `TauCeti.chartField`: a vector field on the model space, read in the extended chart at a point
  and extended by zero; `TauCeti.contMDiff_chartField` shows it is smooth when the field is
  supported in a compact subset of the chart target, and `TauCeti.hasMFDerivAt_chartField` that
  straight segments along which the field is constant are its integral curves.
* `TauCeti.bumpChartField`: a constant field cut off by a bump function, read in the chart;
  `TauCeti.bumpChartField_extChartAt_symm` and
  `TauCeti.bumpChartField_extChartAt_symm_of_mem_ball` give its values in the chart;
  `TauCeti.contMDiff_bumpChartField`, `TauCeti.bumpChartField_eq_zero` and
  `TauCeti.isMIntegralCurveOn_bumpChartField` record its smoothness, compact support and straight
  flow lines near the centre; `TauCeti.maximalIntegralCurve_bumpChartField_extChartAt_symm`
  identifies its maximal integral curves there with straight lines in the chart.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma; the flow of a cut-off constant vector field is the one used
  there.
-/

public section

noncomputable section

open Set Filter Metric Topology VectorField
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-! ### Vector fields read in a chart -/

section ChartField

variable {x z : M} {w : (p : E) → TangentSpace 𝓘(ℝ, E) p}

/-- A vector field `w` on the model space, read in the extended chart at `x` and extended by zero
outside the chart domain. -/
def chartField (x : M) (w : (p : E) → TangentSpace 𝓘(ℝ, E) p) (z : M) :
    TangentSpace I z :=
  letI := Classical.dec (z ∈ (extChartAt I x).source)
  if z ∈ (extChartAt I x).source then mpullback I 𝓘(ℝ, E) (extChartAt I x) w z else 0

/-- On the chart domain, the chart field is the pullback of `w` by the extended chart. -/
theorem chartField_of_mem (hz : z ∈ (extChartAt I x).source) :
    chartField (I := I) x w z = mpullback I 𝓘(ℝ, E) (extChartAt I x) w z := by
  simp only [chartField, hz, ↓reduceIte]

/-- Outside the chart domain, the chart field vanishes. -/
theorem chartField_of_notMem (hz : z ∉ (extChartAt I x).source) :
    chartField (I := I) x w z = 0 := by
  simp only [chartField, hz, ↓reduceIte]

/-- If `w` vanishes outside `K ⊆ target`, the chart field vanishes outside the preimage of
`K`. -/
theorem chartField_eq_zero {K : Set E}
    (hwK : ∀ p ∉ K, w p = 0) (hz : z ∉ (extChartAt I x).symm '' K) :
    chartField (I := I) x w z = 0 := by
  by_cases hs : z ∈ (extChartAt I x).source
  · have hK : extChartAt I x z ∉ K := fun h ↦ hz ⟨_, h, (extChartAt I x).left_inv hs⟩
    rw [chartField_of_mem hs, mpullback_apply, hwK _ hK, map_zero]
  · exact chartField_of_notMem hs

variable [IsManifold I 1 M]

/-- At a point `p` of the chart target with `w p = d`, the chart field at `(extChartAt I x).symm p`
is the image of `d` under the derivative of the inverse chart. -/
theorem chartField_extChartAt_symm {p : E} {d : TangentSpace 𝓘(ℝ, E) p}
    (hp : p ∈ (extChartAt I x).target) (hwp : w p = d) :
    chartField (I := I) x w ((extChartAt I x).symm p) =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p d := by
  have hs := (extChartAt I x).map_target hp
  rw [chartField_of_mem hs, mpullback_apply, (isInvertible_mfderiv_extChartAt hs).inverse_apply_eq]
  have key : mfderiv I 𝓘(ℝ, E) (extChartAt I x) ((extChartAt I x).symm p)
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p d) = d :=
    DFunLike.congr_fun (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hp) d
  exact ((congrArg (fun a ↦ (w a : E)) ((extChartAt I x).right_inv hp)).trans hwp).trans key.symm

/-- A segment in a chart, along which `w` is the constant `d`, is an integral curve of the chart
field at every time at which it stays in an open set where `w = d`. -/
theorem hasMFDerivAt_chartField {c d : E} {V : Set E}
    (hV : IsOpen V) (hVt : V ⊆ (extChartAt I x).target) (hwV : ∀ p ∈ V, w p = d) {t : ℝ}
    (ht : c + t • d ∈ V) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ ↦ (extChartAt I x).symm (c + s • d)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (chartField (I := I) x w ((extChartAt I x).symm (c + t • d)))) := by
  have hrange : range I ∈ 𝓝 (c + t • d) :=
    mem_of_superset (hV.mem_nhds ht) (hVt.trans (extChartAt_target_subset_range x))
  have hsymm :=
    (mdifferentiableWithinAt_extChartAt_symm (hVt ht)).hasMFDerivWithinAt.hasMFDerivAt hrange
  have hseg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ ↦ c + s • d) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight d) := by
    have h := ((hasDerivAt_id t).smul_const d).const_add c
    rw [one_smul] at h
    exact hasMFDerivAt_iff_hasFDerivAt.2 h
  have hder : (1 : ℝ →L[ℝ] ℝ).smulRight
      (chartField (I := I) x w ((extChartAt I x).symm (c + t • d))) =
      (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (c + t • d)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight d) := by
    rw [chartField_extChartAt_symm (hVt ht) (hwV _ ht)]
    ext1
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      one_smul]
    congr 1
    -- `smulRight` is evaluated in `E` rather than in the tangent space at `c + t • d`.
    exact (by simp : ((1 : ℝ →L[ℝ] ℝ).smulRight d) 1 = d).symm
  rw [hder]
  exact hsymm.comp t hseg

/-- The chart field of a `C^m` vector field supported in a compact subset of the chart target is
a `C^m` vector field on `M`, provided `M` is `C^(m + 1)`. -/
theorem contMDiff_chartField [CompleteSpace E] [T2Space M] {n m : ℕ∞ω}
    [IsManifold I n M] (hmn : m + 1 ≤ n)
    (hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent m (fun p ↦ (⟨p, w p⟩ : TangentBundle 𝓘(ℝ, E) E)))
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I x).target) (hwK : ∀ p ∉ K, w p = 0) :
    ContMDiff I I.tangent m (fun z ↦ (⟨z, chartField x w z⟩ : TangentBundle I M)) := by
  intro z
  by_cases hz : z ∈ (extChartAt I x).symm '' K
  · -- Near the support, the chart field is the pullback of `w` by the chart.
    obtain ⟨p, hp, rfl⟩ := hz
    have hs := (extChartAt I x).map_target (hKt hp)
    refine (ContMDiffAt.mpullback_vectorField_preimage (hw _)
      (contMDiffAt_extChartAt' (by rwa [← extChartAt_source (I := I)]))
      (isInvertible_mfderiv_extChartAt hs) hmn).congr_of_eventuallyEq ?_
    filter_upwards [extChartAt_source_mem_nhds' hs] with y hy
    rw [chartField_of_mem hy]
  · -- Away from the compact support, the chart field is the zero section.
    have hL : IsClosed ((extChartAt I x).symm '' K) :=
      (hK.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hKt)).isClosed
    refine (Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _) z).congr_of_eventuallyEq ?_
    filter_upwards [hL.isOpen_compl.mem_nhds hz] with y hy
    rw [chartField_eq_zero hwK hy]
    rfl


end ChartField

/-! ### Cut-off constant fields -/

section BumpChartField

variable {x z : M} {ρ : ContDiffBump (extChartAt I x x)}

variable [FiniteDimensional ℝ E]

variable (x ρ) in
/-- The constant vector field `v` on the model space, cut off by the bump function `ρ` and read in
the chart at `x`. -/
def bumpChartField (v : E) (z : M) : TangentSpace I z :=
  chartField x (fun p : E ↦ ((ρ p : ℝ) • v : E)) z

/-- The cut-off field `bumpChartField x ρ v` is the chart field of `p ↦ ρ p • v`. -/
theorem bumpChartField_def (v : E) (z : M) :
    bumpChartField x ρ v z = chartField x (fun p : E ↦ ((ρ p : ℝ) • v : E)) z :=
  (rfl)

variable (v : E)

private theorem smul_eq_zero_of_notMem_closedBall {p : E}
    (hp : p ∉ closedBall (extChartAt I x x) ρ.rOut) : ((ρ p : ℝ) • v : E) = 0 := by
  have hρp : ρ p = 0 := Function.notMem_support.1 fun h ↦
    hp (ball_subset_closedBall (ρ.support_eq ▸ h))
  rw [hρp, zero_smul]

/-- The cut-off field `bumpChartField x ρ v` vanishes outside the image under the inverse chart of
the closed outer ball of `ρ`. -/
theorem bumpChartField_eq_zero
    (hz : z ∉ (extChartAt I x).symm '' closedBall (extChartAt I x x) ρ.rOut) :
    bumpChartField x ρ v z = 0 :=
  chartField_eq_zero (fun _ hp ↦ smul_eq_zero_of_notMem_closedBall v hp) hz

variable [IsManifold I 1 M]

/-- On the chart target, the cut-off field `bumpChartField x ρ v` is the image of `ρ p • v` under
the derivative of the inverse chart. -/
theorem bumpChartField_extChartAt_symm {p : E} (hp : p ∈ (extChartAt I x).target) :
    bumpChartField x ρ v ((extChartAt I x).symm p) =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p ((ρ p : ℝ) • v) :=
  chartField_extChartAt_symm hp rfl

/-- On the inner ball of `ρ`, where `ρ = 1`, the cut-off field `bumpChartField x ρ v` is the image
of `v` under the derivative of the inverse chart. -/
theorem bumpChartField_extChartAt_symm_of_mem_ball
    (hρ : closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) {p : E}
    (hp : p ∈ ball (extChartAt I x x) ρ.rIn) :
    bumpChartField x ρ v ((extChartAt I x).symm p) =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) p v := by
  rw [bumpChartField_extChartAt_symm v
    (hρ (closedBall_subset_closedBall ρ.rIn_lt_rOut.le (ball_subset_closedBall hp))),
    ρ.one_of_mem_closedBall (ball_subset_closedBall hp), one_smul]

/-- The cut-off field `bumpChartField x ρ v` is `C^m` when `M` is `C^(m + 1)` and the closed outer
ball of `ρ` lies in the chart target. -/
theorem contMDiff_bumpChartField [T2Space M] {n : ℕ∞ω} {m : ℕ∞} [IsManifold I n M]
    (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) :
    ContMDiff I I.tangent m fun z ↦ (⟨z, bumpChartField x ρ v z⟩ : TangentBundle I M) := by
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent m
      (fun p ↦ (⟨p, ((ρ p : ℝ) • v : E)⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.2 (ρ.contDiff.smul contDiff_const)
  exact contMDiff_chartField hmn hw (isCompact_closedBall _ _) hρ fun _ hp ↦
    smul_eq_zero_of_notMem_closedBall v hp

/-- A straight segment `s ↦ c + s • v` in the chart, for times at which it stays in the inner ball
of `ρ`, is an integral curve of the cut-off field `bumpChartField x ρ v`. -/
theorem isMIntegralCurveOn_bumpChartField
    (hρ : closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) {c : E} {J : Set ℝ}
    (hJ : ∀ s ∈ J, c + s • v ∈ ball (extChartAt I x x) ρ.rIn) :
    IsMIntegralCurveOn (fun s ↦ (extChartAt I x).symm (c + s • v)) (bumpChartField x ρ v) J :=
  fun s hs ↦ (hasMFDerivAt_chartField isOpen_ball
    ((ball_subset_closedBall.trans (closedBall_subset_closedBall ρ.rIn_lt_rOut.le)).trans hρ)
    (fun p hp ↦ by
      -- `TangentSpace 𝓘(ℝ, E) p` is `E` by definition.
      simp only [ρ.one_of_mem_closedBall (ball_subset_closedBall hp), one_smul]
      rfl) (hJ s hs)).hasMFDerivWithinAt

/-- Near the centre of `ρ`, the maximal integral curve of the cut-off field `bumpChartField x ρ v`
through `(extChartAt I x).symm c` is the straight line `t ↦ (extChartAt I x).symm (c + t • v)` in
the chart, for every time `t` with `‖c - extChartAt I x x‖ + |t| * ‖v‖ < ρ.rIn` (so the segment
from `c` to `c + t • v` stays in the inner ball of `ρ`). -/
theorem maximalIntegralCurve_bumpChartField_extChartAt_symm [T2Space M]
    [BoundarylessManifold I M] {n : ℕ∞ω} {m : ℕ∞} [IsManifold I n M] (hm : 1 ≤ m)
    (hmn : (m : ℕ∞ω) + 1 ≤ n)
    (hρ : closedBall (extChartAt I x x) ρ.rOut ⊆ (extChartAt I x).target) {c : E} {t : ℝ}
    (hct : ‖c - extChartAt I x x‖ + |t| * ‖v‖ < ρ.rIn) :
    maximalIntegralCurve (bumpChartField x ρ v) ((extChartAt I x).symm c) t =
      (extChartAt I x).symm (c + t • v) := by
  -- The segment `s ↦ c + s • v` stays in the inner ball of `ρ` for `|s| < |t| + δ`.
  set δ := (ρ.rIn - ‖c - extChartAt I x x‖ - |t| * ‖v‖) / (‖v‖ + 1) with hδ
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hδ0 : 0 < δ := div_pos (by linarith) hv1
  have hδv : δ * (‖v‖ + 1) = ρ.rIn - ‖c - extChartAt I x x‖ - |t| * ‖v‖ :=
    div_mul_cancel₀ _ hv1.ne'
  have hseg : ∀ s ∈ Ioo (-(|t| + δ)) (|t| + δ), c + s • v ∈ ball (extChartAt I x x) ρ.rIn :=
    fun s hs ↦ by
      have hs' : |s| * ‖v‖ ≤ (|t| + δ) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (abs_lt.2 hs).le (norm_nonneg v)
      rw [Metric.mem_ball, dist_eq_norm, add_sub_right_comm]
      calc ‖c - extChartAt I x x + s • v‖ ≤ ‖c - extChartAt I x x‖ + |s| * ‖v‖ := by
            rw [← Real.norm_eq_abs, ← norm_smul]; exact norm_add_le _ _
        _ < ρ.rIn := by nlinarith
  have h0 : (0 : ℝ) ∈ Ioo (-(|t| + δ)) (|t| + δ) :=
    ⟨by linarith [abs_nonneg t], by linarith [abs_nonneg t]⟩
  exact (isMIntegralCurveOn_bumpChartField v hρ hseg).eqOn_maximalIntegralCurve
    ((contMDiff_bumpChartField v hmn hρ).of_le (by exact_mod_cast hm)) h0 (by simp)
    (abs_lt.1 (lt_add_of_pos_right _ hδ0))

end BumpChartField

end TauCeti
