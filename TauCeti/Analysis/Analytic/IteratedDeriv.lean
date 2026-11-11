/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Analyticity of iterated vertical slice derivatives

Mathlib proves that the `n`-fold iterate `deriv^[n] f` of an analytic function `f : 𝕜 → F` into a
complete normed space is analytic (`AnalyticAt.iterated_deriv`). This file proves the parametric
two-variable version for `iteratedDeriv`: if `f : E × 𝕜 → F` is jointly analytic at `p`, then
`(q : E × 𝕜) ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2` is jointly analytic at `p`
(`AnalyticAt.iteratedDeriv_snd`), and in particular the vertical Taylor coefficient
`x ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2` is analytic at `p.1`
(`AnalyticAt.curry_left_iteratedDeriv_snd`).
-/

public section

open Filter Metric Topology

namespace AnalyticAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If `f : E × 𝕜 → F` is jointly analytic at `p` and `F` is complete, then the `n`-th iterated
derivative in the second variable `(q : E × 𝕜) ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2` is
jointly analytic at `p`. -/
theorem iteratedDeriv_snd {f : E × 𝕜 → F} {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) :
    ∀ n : ℕ, AnalyticAt 𝕜 (fun q : E × 𝕜 ↦ iteratedDeriv n (fun y ↦ f (q.1, y)) q.2) p
  | 0 => by simpa only [iteratedDeriv_zero] using hf
  | n + 1 => by
    set f' : E × 𝕜 → F := fun q ↦ fderiv 𝕜 f q (0, 1)
    have hf' : AnalyticAt 𝕜 f' p :=
      ((ContinuousLinearMap.apply 𝕜 F ((0 : E), (1 : 𝕜))).analyticAt _).comp hf.fderiv
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt 𝕜 f) p hf
    refine (hf'.iteratedDeriv_snd n).congr ?_
    filter_upwards [ball_mem_nhds p (half_pos hr)] with q hq
    have hq_lt : dist q p < r := (mem_ball.1 hq).trans (half_lt_self hr)
    have hderiv_eq : (fun y ↦ f' (q.1, y)) =ᶠ[𝓝 q.2] deriv (fun y ↦ f (q.1, y)) := by
      have hy_open : {y : 𝕜 | (q.1, y) ∈ ball p r} ∈ 𝓝 q.2 :=
        ((continuous_const.prodMk continuous_id).tendsto q.2).eventually
          (isOpen_ball.mem_nhds (mem_ball.2 hq_lt))
      filter_upwards [hy_open] with y hy
      exact (((hball hy).differentiableAt.hasFDerivAt.comp_hasDerivAt y
        ((hasDerivAt_const y q.1).prodMk (hasDerivAt_id y))).deriv).symm
    rw [iteratedDeriv_succ']
    exact hderiv_eq.iteratedDeriv_eq n

/-- If `f : E × 𝕜 → F` is jointly analytic at `p` and `F` is complete, then
`x ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2` is analytic at `p.1`. -/
theorem curry_left_iteratedDeriv_snd {f : E × 𝕜 → F} {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) (n : ℕ) :
    AnalyticAt 𝕜 (fun x : E ↦ iteratedDeriv n (fun y ↦ f (x, y)) p.2) p.1 :=
  (hf.iteratedDeriv_snd n).curry_left

end AnalyticAt
