/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DerivativeTest
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
public import TauCeti.Geometry.Manifold.Riemannian.CriticalHessian

/-!
# The second derivative test on a Riemannian manifold

Let `f` be a real function on a Riemannian manifold without boundary, `C²` at a critical point
`x`. If the Riemannian Hessian of `f` at `x` is positive definite, then `x` is a strict local
minimum of `f`.

At a critical point, the Riemannian Hessian is the second derivative of `f` read in the preferred
chart (`TauCeti.Manifold.hessian_eq_criticalHessian`), and the first derivative of the coordinate
expression vanishes, so the test reduces to the second derivative test on the model space
(`eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos`).

## Main results

* `TauCeti.Manifold.eventually_lt_of_hessian_pos`: the second derivative test.
-/

public section

open Bundle Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f : M → ℝ} {x : M}

/-- **The second derivative test.** If `x` is a critical point of a function `f` which is `C²`
at `x`, and the Riemannian Hessian of `f` at `x` is positive definite, then `f(x) < f(y)` for all
`y ≠ x` close to `x`. -/
theorem eventually_lt_of_hessian_pos (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hcrit : mvfderiv I f x = 0) (hpos : ∀ v : TangentSpace I x, v ≠ 0 → 0 < hessian I f x v v) :
    ∀ᶠ y in 𝓝[≠] x, f x < f y := by
  set φ := extChartAt I x
  set g := f ∘ φ.symm
  have hg : ContDiffAt ℝ 2 g (φ x) := hf.contDiffAt_comp_extChartAt_symm
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hd : fderiv ℝ g (φ x) = 0 :=
    (TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hx
      (hg.differentiableAt (by norm_num))).1 (mvfderiv_eq_zero_iff.1 hcrit)
  have hpos' (v : E) (hv : v ≠ 0) : 0 < fderiv ℝ (fderiv ℝ g) (φ x) v v := by
    have h := hpos v hv
    have h2 : hessian I f x v v = criticalHessian I f x v v :=
      TauCeti.Manifold.hessian_eq_criticalHessian hf hcrit v v
    rw [h2, criticalHessian_def] at h
    exact h
  have hmin := hg.eventually_lt_of_fderiv_eq_zero_of_fderiv_fderiv_pos hd hpos'
  have htend : Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuousAt_extChartAt (I := I) x).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy hys
    exact fun h ↦ hy (φ.injOn hys hx h)
  filter_upwards [htend.eventually hmin,
    nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy hys
  simpa [g, φ.left_inv hys, φ.left_inv hx] using hy

end TauCeti.Manifold
