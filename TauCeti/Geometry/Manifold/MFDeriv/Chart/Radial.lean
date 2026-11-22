/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Radial scalar functions in manifold charts

The squared distance from a chart center is smooth on the chart source. Its manifold derivative
vanishes only at that center, because the chart differential is invertible. These facts apply
to local defining functions for coordinate balls without any choice of Riemannian metric.

## Main results

* `TauCeti.Manifold.contMDiffOn_chart_radial`: smoothness of a radial chart function.
* `TauCeti.Manifold.mvfderiv_chart_radial_ne_zero`: its differential is nonzero off the center.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle Set Topology Filter Function Metric
open scoped ContDiff Manifold

namespace TauCeti.Manifold
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The radius-squared minus squared chart-distance function is smooth on the chart source. -/
theorem contMDiffOn_chart_radial {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n M] (p : M) (c : E) (r : ℝ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) n
      (fun x ↦ r ^ 2 - ‖extChartAt 𝓘(ℝ, E) p x - c‖ ^ 2)
      (extChartAt 𝓘(ℝ, E) p).source := by
  have he : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n
      (extChartAt 𝓘(ℝ, E) p) (extChartAt 𝓘(ℝ, E) p).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := p) (n := n))
  have hφ : ContDiff ℝ n (fun z : E ↦ r ^ 2 - ‖z - c‖ ^ 2) :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  exact hφ.contMDiff.comp_contMDiffOn he

/-- The radial chart function has nonzero manifold derivative away from its chart center, using
the actual invertible chart differential. -/
theorem mvfderiv_chart_radial_ne_zero [IsManifold 𝓘(ℝ, E) 1 M] (p : M) (c : E) (r : ℝ)
    {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) p).source)
    (hne : extChartAt 𝓘(ℝ, E) p x ≠ c) :
    mvfderiv 𝓘(ℝ, E)
      (fun y ↦ r ^ 2 - ‖extChartAt 𝓘(ℝ, E) p y - c‖ ^ 2) x ≠ 0 := by
  let e := extChartAt 𝓘(ℝ, E) p
  let φ : E → ℝ := fun z ↦ r ^ 2 - ‖z - c‖ ^ 2
  let L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x
  let z : E := e x - c
  let v := L.inverse z
  have hL : L.IsInvertible := isInvertible_mfderiv_extChartAt hx
  have hv : L v = z := hL.self_apply_inverse z
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have he : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e x :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hφ : ContDiff ℝ ∞ φ :=
    contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)
  have hc : mvfderiv 𝓘(ℝ, E) (fun y ↦ φ (e y)) x =
      (fderiv ℝ φ (e x)).comp L := by
    -- Name the scalar composition so the manifold chain rule applies directly.
    change mvfderiv 𝓘(ℝ, E) (φ ∘ e) x = _
    rw [mvfderiv_comp x ((hφ.differentiable (by simp)) (e x)).mdifferentiableAt he]
    congr 1
    ext v
    simp only [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply]
    rfl
  have hs := ((hasFDerivAt_id (e x)).sub_const c).norm_sq
  have hφd : HasFDerivAt φ (0 - 2 • (innerSL ℝ) z) (e x) := by
    simpa only [φ, z, Pi.sub_apply, id_eq, ContinuousLinearMap.comp_id] using!
      (hasFDerivAt_const (r ^ 2) (e x)).sub hs
  have hvalue : fderiv ℝ φ (e x) z = -2 * ‖z‖ ^ 2 := by
    rw [hφd.fderiv]
    simp only [sub_apply, zero_apply, two_smul, add_apply, innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq]
    ring
  intro hzero
  have h := congrArg (fun K : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ ↦ K v) hzero
  -- Evaluate the vanishing differential on the chosen tangent vector.
  change (mvfderiv 𝓘(ℝ, E) (fun y ↦ φ (e y)) x) v = 0 at h
  rw [hc] at h
  -- Continuous-linear-map composition evaluates by applying the chart differential first.
  change fderiv ℝ φ (e x) (L v) = 0 at h
  rw [hv, hvalue] at h
  have hpos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  linarith

end TauCeti.Manifold
