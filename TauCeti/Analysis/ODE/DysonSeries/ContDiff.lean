/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Geometry.Manifold.IntegralCurve.Flow
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth parameter dependence of the Dyson series

A jointly Cⁿ family of coefficient paths in a real Banach algebra has a left Dyson solution
which is jointly Cⁿ in its parameter and time, of the same order. The statement includes
continuity at order zero and smoothness at order infinity. No uniform coefficient bound is needed.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, Chapter 9.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Set Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  {p : X → ℝ → B}

/-- The left Dyson series of a smooth family is smooth jointly in the parameter and time.
No uniform bound on the coefficient paths is required. -/
theorem contDiff_parametric_dysonSeriesLeft {n : ℕ∞}
    (hp : ContDiff ℝ n (Function.uncurry p)) :
    ContDiff ℝ n (fun q : X × ℝ ↦ dysonSeriesLeft (p q.1) q.2) := by
  by_cases hn0 : n = 0
  · subst n
    exact contDiff_zero.mpr (continuous_parametric_dysonSeriesLeft hp.continuous)
  have hn : 1 ≤ n := Order.one_le_iff_ne_zero.mpr hn0
  let W := X × ℝ × B
  let v : (q : W) → TangentSpace 𝓘(ℝ, W) q := fun q ↦ (0, 1, p q.1 q.2.1 * q.2.2)
  let γ : X → ℝ → W := fun x t ↦ (x, t, dysonSeriesLeft (p x) t)
  have hv : ContDiff ℝ n v :=
    contDiff_const.prodMk (contDiff_const.prodMk
      ((hp.comp (contDiff_fst.prodMk contDiff_snd.fst)).mul contDiff_snd.snd))
  have hvM : ContMDiff 𝓘(ℝ, W) (𝓘(ℝ, W)).tangent n
      (fun q ↦ (⟨q, v q⟩ : TangentBundle 𝓘(ℝ, W) W)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hγ (x : X) : IsMIntegralCurve (I := 𝓘(ℝ, W)) (γ x) v := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_iff_isIntegralCurveOn]
    intro t _
    have hpx : Continuous (p x) := hp.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((hasDerivAt_const t x).prodMk
      ((hasDerivAt_id t).prodMk (hasDerivAt_dysonSeriesLeft hpx t))).hasDerivWithinAt
  have hinit (x : X) : γ x 0 = (x, 0, 1) := by simp [γ]
  have heq (x : X) (t : ℝ) :
      maximalIntegralCurve (I := 𝓘(ℝ, W)) v (x, 0, 1) t = γ x t := by
    simpa only [hinit] using (hγ x).maximalIntegralCurve_eq (hvM.of_le (by exact_mod_cast hn)) t
  have hflow := contMDiffOn_maximalIntegralCurve (I := 𝓘(ℝ, W)) hn hvM
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
    contMDiffOn_iff_contDiffOn] at hflow
  have hmap : ContDiff ℝ n
      (fun q : X × ℝ ↦ ((q.1, (0 : ℝ), (1 : B)), q.2)) :=
    (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_const)).prodMk contDiff_snd
  have hmem : MapsTo (fun q : X × ℝ ↦ ((q.1, (0 : ℝ), (1 : B)), q.2)) univ
      (maximalIntegralCurveFlowDomain (I := 𝓘(ℝ, W)) v) := by
    intro q _
    rw [mem_maximalIntegralCurveFlowDomain,
      (hγ q.1).maximalIntegralCurveInterval_eq_univ (hinit q.1)]
    exact mem_univ _
  have hs := hflow.comp hmap.contDiffOn hmem
  rw [contDiffOn_univ] at hs
  have hs' : ContDiff ℝ n (fun q : X × ℝ ↦ γ q.1 q.2) := by
    simpa only [Function.comp_def, heq] using hs
  exact hs'.snd.snd

end TauCeti
