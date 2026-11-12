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
inequality and the uniform continuity of the derivative at the compact graph of `x`
(`IsCompact.exists_pos_forall_norm_fderiv_sub_le`). It is the
form in which a time-dependent vector field is linearized along a periodic orbit.
In particular `F p` is Lipschitz with a constant independent of `p ∈ K` on balls of a radius
independent of `p` about `x p` (`IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sub`), and so
Lipschitz at `x p` (`IsCompact.exists_pos_forall_norm_sub_le_mul`).

For a jointly `C²` family the remainder is quadratic, uniformly over `K`, in the two-point form
`‖F p (x p + a) - F p (x p + b) - fderiv ℝ (F p) (x p) (a - b)‖ ≤ L max ‖a‖ ‖b‖ ‖a - b‖`
(`IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul`). This is the bound on the nonlinear
part of a map that a Newton iteration needs.
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

/-- **Uniform continuity of the derivative at a compact family of base points.** Let
`F : P → E → G` be jointly `C¹`, and let `x : P → E` be continuous on a compact set `K`. For every
`ε > 0` there is `δ > 0` such that `‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ ε` for every
`p ∈ K` and every `y` with `‖y - x p‖ ≤ δ`. -/
theorem IsCompact.exists_pos_forall_norm_fderiv_sub_le {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} {K : Set P}
    {x : P → E}
    (hK : IsCompact K) (hF : ContDiff ℝ 1 (Function.uncurry F)) (hx : ContinuousOn x K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ y : E, ‖y - x p‖ ≤ δ →
      ‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ ε := by
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
  refine ⟨δ / 2, by positivity, fun p hp y hy => ?_⟩
  rw [← dist_eq_norm, dist_comm]
  refine (hD' (a := (p, x p)) (b := (p, y)) ?_ ⟨p, hp, rfl⟩).le
  rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm, dist_eq_norm]
  linarith

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
  obtain ⟨δ, hδ, hclose⟩ := hK.exists_pos_forall_norm_fderiv_sub_le hF hx hε
  refine ⟨δ, hδ, fun p hp h hh => ?_⟩
  have hdiff (y : E) : DifferentiableAt ℝ (F p) y :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero y
  have hx0 : x p ∈ closedBall (x p) ‖h‖ := mem_closedBall_self (norm_nonneg h)
  have hxh : x p + h ∈ closedBall (x p) ‖h‖ := by simp [mem_closedBall, dist_eq_norm]
  have hbound (y : E) (hy : y ∈ closedBall (x p) ‖h‖) :
      ‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ ε :=
    hclose p hp y (by rw [← dist_eq_norm]; exact (mem_closedBall.1 hy).trans hh)
  simpa using (convex_closedBall (x p) ‖h‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hdiff y) hbound hx0 hxh

/-- **Uniform Lipschitz bound on balls about a compact family of base points.** Let `F : P → E → G`
be jointly `C¹`, and let `x : P → E` be continuous on a compact set `K`. Then there are `δ > 0` and
`L` such that `‖F p (x p + a) - F p (x p + b)‖ ≤ L ‖a - b‖` for every `p ∈ K` and all increments
`a`, `b` of norm at most `δ`. -/
theorem IsCompact.exists_pos_forall_norm_sub_le_mul_norm_sub {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} {K : Set P}
    {x : P → E}
    (hK : IsCompact K) (hF : ContDiff ℝ 1 (Function.uncurry F)) (hx : ContinuousOn x K) :
    ∃ δ > 0, ∃ L, ∀ p ∈ K, ∀ a b : E, ‖a‖ ≤ δ → ‖b‖ ≤ δ →
      ‖F p (x p + a) - F p (x p + b)‖ ≤ L * ‖a - b‖ := by
  -- The derivative is within `1` of its value at `x p` on balls of a fixed radius, and that
  -- value is bounded on `K`.
  obtain ⟨δ, hδ, hclose⟩ := hK.exists_pos_forall_norm_fderiv_sub_le hF hx one_pos
  have hD : Continuous fun q : P × E => fderiv ℝ (F q.1) q.2 :=
    ((hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv (n := 0) contDiff_snd
      (by norm_num)).continuous
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hD.comp_continuousOn (continuousOn_id.prodMk hx))
  refine ⟨δ, hδ, B + 1, fun p hp a b ha hb => ?_⟩
  have hdiff (y : E) : DifferentiableAt ℝ (F p) y :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero y
  have hxa : x p + a ∈ closedBall (x p) δ := by simpa [mem_closedBall, dist_eq_norm]
  have hxb : x p + b ∈ closedBall (x p) δ := by simpa [mem_closedBall, dist_eq_norm]
  have hbound (y : E) (hy : y ∈ closedBall (x p) δ) : ‖fderiv ℝ (F p) y‖ ≤ B + 1 := by
    rw [mem_closedBall, dist_eq_norm] at hy
    calc ‖fderiv ℝ (F p) y‖
        = ‖fderiv ℝ (F p) (x p) + (fderiv ℝ (F p) y - fderiv ℝ (F p) (x p))‖ := by
          rw [add_sub_cancel]
      _ ≤ B + 1 := norm_add_le_of_le (hB p hp) (hclose p hp y hy)
  simpa [add_sub_add_left_eq_sub] using
    (convex_closedBall (x p) δ).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hdiff y) hbound hxb hxa

/-- **Uniform Lipschitz bound at a compact family of base points.** Let `F : P → E → G` be jointly
`C¹`, and let `x : P → E` be continuous on a compact set `K`. Then there are `δ > 0` and `L` such
that `‖F p y - F p (x p)‖ ≤ L ‖y - x p‖` for every `p ∈ K` and every `y` with `‖y - x p‖ ≤ δ`. -/
theorem IsCompact.exists_pos_forall_norm_sub_le_mul {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} {K : Set P}
    {x : P → E}
    (hK : IsCompact K) (hF : ContDiff ℝ 1 (Function.uncurry F)) (hx : ContinuousOn x K) :
    ∃ δ > 0, ∃ L, ∀ p ∈ K, ∀ y : E, ‖y - x p‖ ≤ δ → ‖F p y - F p (x p)‖ ≤ L * ‖y - x p‖ := by
  obtain ⟨δ, hδ, L, hL⟩ := hK.exists_pos_forall_norm_sub_le_mul_norm_sub hF hx
  refine ⟨δ, hδ, L, fun p hp y hy => ?_⟩
  simpa using hL p hp (y - x p) 0 hy (by simpa using hδ.le)

/-- **Uniform quadratic remainder over a compact parameter set.** Let `F : P → E → G` be jointly
`C²`, and let `x : P → E` be continuous on a compact set `K`. Then there are `δ > 0` and `L` such
that for every `p ∈ K` and all increments `a`, `b` of norm at most `δ`,
`‖F p (x p + a) - F p (x p + b) - fderiv ℝ (F p) (x p) (a - b)‖ ≤ L max ‖a‖ ‖b‖ ‖a - b‖`.
For `b = 0` this is the second-order Taylor estimate at `x p`; in the two-point form it is the
Lipschitz bound on the nonlinear part of `F p` that drives a Newton iteration. -/
theorem IsCompact.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul {P E G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : P → E → G} {K : Set P}
    {x : P → E}
    (hK : IsCompact K) (hF : ContDiff ℝ 2 (Function.uncurry F)) (hx : ContinuousOn x K) :
    ∃ δ > 0, ∃ L, ∀ p ∈ K, ∀ a b : E, ‖a‖ ≤ δ → ‖b‖ ≤ δ →
      ‖F p (x p + a) - F p (x p + b) - fderiv ℝ (F p) (x p) (a - b)‖ ≤
        L * max ‖a‖ ‖b‖ * ‖a - b‖ := by
  -- The derivative `(p, y) ↦ fderiv ℝ (F p) y` is jointly `C¹`, hence Lipschitz at `x p`.
  have hFq : ContDiff ℝ 2 (Function.uncurry fun (q : P × E) (y : E) => F q.1 y) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hD : ContDiff ℝ 1 (Function.uncurry fun (p : P) (y : E) => fderiv ℝ (F p) y) :=
    hFq.fderiv (n := 1) contDiff_snd (by norm_num)
  obtain ⟨δ, hδ, L, hL⟩ := hK.exists_pos_forall_norm_sub_le_mul hD hx
  refine ⟨δ, hδ, max L 0, fun p hp a b ha hb => ?_⟩
  have hdiff (y : E) : DifferentiableAt ℝ (F p) y :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable two_ne_zero y
  set m := max ‖a‖ ‖b‖
  have hxa : x p + a ∈ closedBall (x p) m := by simp [mem_closedBall, dist_eq_norm, m]
  have hxb : x p + b ∈ closedBall (x p) m := by simp [mem_closedBall, dist_eq_norm, m]
  have hbound (y : E) (hy : y ∈ closedBall (x p) m) :
      ‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ max L 0 * m := by
    rw [mem_closedBall, dist_eq_norm] at hy
    calc ‖fderiv ℝ (F p) y - fderiv ℝ (F p) (x p)‖ ≤ L * ‖y - x p‖ :=
          hL p hp y (hy.trans (max_le ha hb))
      _ ≤ max L 0 * ‖y - x p‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * m := mul_le_mul_of_nonneg_left hy (le_max_right _ _)
  simpa [add_sub_add_left_eq_sub] using
    (convex_closedBall (x p) m).norm_image_sub_le_of_norm_fderiv_le'
      (fun y _ => hdiff y) hbound hxb hxa
