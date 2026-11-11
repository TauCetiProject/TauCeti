/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The punctured remainder form of the Fréchet derivative

A map `f` has Fréchet derivative `L` at `x` exactly when the relative remainder
`‖f (x + h) - f x - L h‖ / ‖h‖` tends to `0` as `h → 0` with `h ≠ 0`. This is
Mathlib's `hasFDerivAt_iff_isLittleO_nhds_zero` with the increment `0` removed from the filter,
which is the form in which difference quotients are usually compared.

For a jointly `C¹` family of maps `F p`, the remainder is moreover small uniformly over a compact
set of parameters `p`, at base points `x p` depending continuously on `p`:
`‖F p (x p + h) - F p (x p) - fderiv ℝ (F p) (x p) h‖ ≤ ε ‖h‖` for all `‖h‖ ≤ δ`
(`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le`). This follows from the mean value
inequality and the uniform continuity of the derivative at the compact graph of `x`. It is the
form in which a time-dependent vector field is linearized along a periodic orbit.
-/

public section

open Filter Topology Set Metric

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {L : E →L[𝕜] F} {x : E}

/-- The punctured remainder form of a Fréchet derivative: `f` has derivative `L` at `x` exactly
when `‖f (x + h) - f x - L h‖ / ‖h‖ → 0` as `h → 0`, `h ≠ 0`. -/
theorem hasFDerivAt_iff_tendsto_norm_div_nhdsNE :
    HasFDerivAt f L x ↔ Tendsto (fun h ↦ ‖f (x + h) - f x - L h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  -- The remainder vanishes at `h = 0`, so the point `0` can be removed from the filter.
  have hpunct : HasFDerivAt f L x ↔
      (fun h ↦ f (x + h) - f x - L h) =o[𝓝[≠] 0] fun h ↦ h := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, ← nhdsNE_sup_pure 0, Asymptotics.isLittleO_sup,
      Asymptotics.isLittleO_pure]
    simp
  rw [hpunct, ← Asymptotics.isLittleO_norm_norm,
    Asymptotics.isLittleO_iff_tendsto (by simp +contextual)]

end TauCeti

/-- **Uniform first-order approximation over a compact parameter set.** Let `F : P → E → G` be
jointly `C¹`, and let `x : P → E` be continuous on a compact set `K`. For every `ε > 0` there
is `δ > 0` such that `‖F p (x p + h) - F p (x p) - fderiv ℝ (F p) (x p) h‖ ≤ ε ‖h‖` for every
`p ∈ K` and every `h` with `‖h‖ ≤ δ`. -/
theorem IsCompact.exists_pos_forall_norm_sub_sub_fderiv_le {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} {K : Set P}
    {x : P → E}
    (hK : IsCompact K) (hF : ContDiff ℝ 1 (Function.uncurry F)) (hx : ContinuousOn x K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h : E, ‖h‖ ≤ δ →
      ‖F p (x p + h) - F p (x p) - fderiv ℝ (F p) (x p) h‖ ≤ ε * ‖h‖ := by
  -- The derivative is uniformly continuous at the compact graph `{(p, x p) | p ∈ K}`.
  set Q : Set (P × E) := (fun p => (p, x p)) '' K
  have hQ : IsCompact Q := hK.image_of_continuousOn (continuousOn_id.prodMk hx)
  have hFq : ContDiff ℝ 1 (Function.uncurry fun (q : P × E) (y : E) => F q.1 y) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : Continuous fun q : P × E => fderiv ℝ (F q.1) q.2 :=
    (hFq.fderiv (n := 0) contDiff_snd (by norm_num)).continuous
  obtain ⟨δ, hδ, hD'⟩ := Metric.mem_uniformity_dist.1
    (hQ.uniformContinuousAt_of_continuousAt _ (fun q _ => hD.continuousAt)
      (Metric.dist_mem_uniformity hε))
  refine ⟨δ / 2, by positivity, fun p hp h hh => ?_⟩
  have hdiff (y : E) : DifferentiableAt ℝ (F p) y :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero y
  have hx0 : x p ∈ closedBall (x p) ‖h‖ := mem_closedBall_self (norm_nonneg h)
  have hxh : x p + h ∈ closedBall (x p) ‖h‖ := by simp [mem_closedBall, dist_eq_norm]
  have hbound (y : E) (hy : y ∈ closedBall (x p) ‖h‖) :
      ‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ ε := by
    rw [← dist_eq_norm, dist_comm]
    refine (hD' (a := (p, x p)) (b := (p, y)) ?_ ⟨p, hp, rfl⟩).le
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm]
    exact (mem_closedBall.1 hy).trans_lt (hh.trans_lt (by linarith))
  simpa using (convex_closedBall (x p) ‖h‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hdiff y) hbound hx0 hxh
