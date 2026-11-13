/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# Local gradient estimates at critical points

Near a critical point of a `C²` function, the Riemannian gradient is bounded above by a
constant times coordinate displacement. Nondegeneracy gives the reverse bound. For a metric
space whose distance is the Riemannian distance, these become two-sided gradient/distance
estimates. Only continuity of the Riemannian metric is required, not its differentiability,
completeness, or compatibility with Morse coordinates.

The upper estimates apply even to degenerate critical points. The lower estimates require an
invertible critical Hessian, but not definiteness: in particular they apply at saddles. These
bounds complement the energy/gradient inequality and permit conversion between small gradient
norm and proximity to an isolated nondegenerate critical point.

The proofs reuse the coordinate derivative estimates in
`TauCeti.Analysis.Calculus.Morse.Basic` and the local chart/length comparison in
`TauCeti.Geometry.Manifold.Riemannian.MetricBridge`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapters 1–2.
-/

public section

open Bundle Filter Set Topology
open scoped ContDiff Manifold ENNReal

namespace TauCeti

open TauCeti.Manifold

section Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {p : M}

/-- Near a critical point of a `C²` function, the gradient is bounded above by a multiple of
coordinate displacement, for any continuous Riemannian metric. Nondegeneracy is not needed. -/
theorem _root_.ContMDiffAt.exists_norm_mgradient_le_mul_norm_extChartAt_sub
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f p) (hp : mvfderiv I f p = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 p,
      ‖mgradient I f y‖ ≤ C * ‖extChartAt I p y - extChartAt I p p‖ := by
  have hg := hf.contDiffAt_comp_extChartAt_symm
  have hg0 : fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p p) = 0 := by
    rwa [← TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
  obtain ⟨A, hA, hupper⟩ := hg.exists_norm_fderiv_le_mul_norm_sub hg0
  let T := (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ p
  let B := 2 * (‖T‖ + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hmetric := eventually_norm_mgradient_le_mul_norm_fderiv_comp_extChartAt_symm
    (I := I) p (r := 2) (by norm_num)
  have hdiff : ∀ᶠ z in 𝓝 (extChartAt I p p),
      DifferentiableAt ℝ (f ∘ (extChartAt I p).symm) z := by
    filter_upwards [hg.eventually (by simp)] with z hz
    exact hz.differentiableAt two_ne_zero
  refine ⟨B * A, mul_pos hB hA, ?_⟩
  filter_upwards [hmetric, (continuousAt_extChartAt (I := I) p).eventually hupper,
    (continuousAt_extChartAt (I := I) p).eventually hdiff] with y hym hyu hyd
  calc
    _ ≤ 2 * ‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y) ∘L T‖ := hym f hyd
    _ ≤ 2 * (‖fderiv ℝ (f ∘ (extChartAt I p).symm) (extChartAt I p y)‖ * ‖T‖) := by
      gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * A * ‖extChartAt I p y - extChartAt I p p‖ := by
      calc
        _ ≤ 2 * ((A * ‖extChartAt I p y - extChartAt I p p‖) * (‖T‖ + 1)) := by
          gcongr; linarith
        _ = _ := by dsimp [B]; ring

omit [I.Boundaryless] in
/-- Near a nondegenerate critical point, coordinate displacement is bounded by the gradient
norm for any continuous Riemannian metric, including at a saddle. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_norm_extChartAt_sub_le_norm_mgradient
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ c > 0, ∀ᶠ y in 𝓝 p,
      c * ‖extChartAt I p y - extChartAt I p p‖ ≤ ‖mgradient I f y‖ := by
  obtain ⟨a, ha, hlower⟩ := ((isManifoldNondegenerateCriticalPoint_iff I).1
    hp).exists_mul_norm_sub_le_norm_fderiv
  obtain ⟨B, hB, hmetric⟩ :=
    eventually_norm_fderiv_comp_extChartAt_symm_le_mul_norm_mgradient (I := I) p
  refine ⟨a / B, div_pos ha hB, ?_⟩
  filter_upwards [hmetric, (continuousAt_extChartAt (I := I) p).eventually hlower]
    with y hym hyl
  have h := hyl.trans (hym f)
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hB).2 (by simpa only [mul_comm] using h)

end Coordinates

section Distance

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] {f : M → ℝ} {p : M}

/-- Near a critical point of a `C²` function on a Riemannian metric space, the gradient norm is
at most a constant times the distance to that point. The critical point may be degenerate. -/
theorem _root_.ContMDiffAt.exists_norm_mgradient_le_mul_dist
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f p) (hp : mvfderiv I f p = 0) :
    ∃ C > 0, ∀ᶠ y in 𝓝 p, ‖mgradient I f y‖ ≤ C * dist y p := by
  obtain ⟨A, hA, hupper⟩ := hf.exists_norm_mgradient_le_mul_norm_extChartAt_sub hp
  let T := trivializationAt E (fun x : M ↦ TangentSpace I x) p
  let ℓ : TangentSpace I p →L[ℝ] E := T.continuousLinearMapAt ℝ p
  -- The tangent chart at its own centre is the identity on coordinates, although its domain
  -- carries the Riemannian norm and its codomain carries the model-space norm.
  have hℓ (v : E) : ℓ v = v := by
    dsimp only [ℓ, T]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H p),
      mfderiv_extChartAt_self]
    rfl
  refine ⟨A * (2 * ‖ℓ‖ + 1), by positivity, ?_⟩
  filter_upwards [hupper, eventually_enorm_apply_extChartAt_sub_le
    (I := I) (F := E) p (by norm_num : (1 : ℝ) < 2)] with y hy hchart
  have hc := hchart ℓ
  rw [hℓ] at hc
  have hcoord : ‖extChartAt I p y - extChartAt I p p‖ ≤ 2 * ‖ℓ‖ * dist y p := by
    have hc' := ENNReal.toReal_mono (by finiteness) hc
    simpa [← ofReal_norm, ENNReal.toReal_mul, edist_dist, dist_comm] using hc'
  calc
    ‖mgradient I f y‖ ≤ A * ‖extChartAt I p y - extChartAt I p p‖ := hy
    _ ≤ A * (2 * ‖ℓ‖ * dist y p) := mul_le_mul_of_nonneg_left hcoord hA.le
    _ ≤ A * (2 * ‖ℓ‖ + 1) * dist y p := by nlinarith [dist_nonneg (x := y) (y := p)]

omit [I.Boundaryless] in
/-- Near a nondegenerate critical point on a Riemannian metric space, the gradient norm is
bounded below by a positive multiple of distance. No positivity of the Hessian is assumed. -/
theorem IsManifoldNondegenerateCriticalPoint.exists_mul_dist_le_norm_mgradient
    (hp : IsManifoldNondegenerateCriticalPoint I f p) :
    ∃ c > 0, ∀ᶠ y in 𝓝 p, c * dist y p ≤ ‖mgradient I f y‖ := by
  obtain ⟨a, ha, hlower⟩ := hp.exists_mul_norm_extChartAt_sub_le_norm_mgradient
  obtain ⟨B, hB, hdist⟩ :=
    eventually_riemannianEDist_le_edist_extChartAt I p
  refine ⟨a / B, div_pos ha (by exact_mod_cast hB), ?_⟩
  filter_upwards [hlower, hdist] with y hy hd
  rw [← IsRiemannianManifold.out (I := I)] at hd
  have hcoord : dist y p ≤ (B : ℝ) * ‖extChartAt I p y - extChartAt I p p‖ := by
    have hd' := ENNReal.toReal_mono (by finiteness) hd
    simpa [edist_dist, ENNReal.toReal_mul, dist_eq_norm, norm_sub_rev,
      dist_comm p y] using hd'
  calc
    a / B * dist y p ≤ a / B * ((B : ℝ) *
        ‖extChartAt I p y - extChartAt I p p‖) := by gcongr
    _ = a * ‖extChartAt I p y - extChartAt I p p‖ := by
      field_simp [ne_of_gt hB]
    _ ≤ ‖mgradient I f y‖ := hy

end Distance

end TauCeti
