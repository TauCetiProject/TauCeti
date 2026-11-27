/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import TauCeti.Analysis.ODE.OneStep.Convergence
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Consistency implies convergence

A one-step method with increment function `Φ` is *consistent* with the differential equation
`y' = f (t, y)` if `Φ t u 0 = f t u`: for vanishing steps its increment is the vector field. This
file proves that a consistent method whose increment function is continuous, and Lipschitz in the
state for small steps, converges: along a solution `y` on `[a, b]`, the numerical solution started
at `y a` is uniformly close to `y` at the nodes of every mesh in `[a, b]` with small enough steps.
No differentiability of `f` or `Φ` and no order of the method is assumed.

The proof has two steps.

* The defect of a solution is `o(s)` uniformly in time. By the mean value inequality the defect
  `y (t + s) - y t - s • Φ t (y t) s` is at most `s` times the largest distance between
  `y' r = Φ r (y r) 0` and `Φ t (y t) s` for `r ∈ [t, t + s]`, and this distance is small by
  uniform continuity of `(r, s) ↦ Φ r (y r) s` on the compact rectangle `[a, b] × [0, h₀]`.
* A defect of at most `τ s` with Lipschitz constant `L` gives the global error bound
  `gronwallBound 0 L τ (b - a)`, by the convergence theorem `TauCeti.norm_sub_oneStepSeq_le`
  with `p = 0`; this bound tends to `0` with `τ`.

Neither step requires the meshes to be uniform.

## Main results

* `TauCeti.exists_forall_norm_oneStepDefect_le_of_consistent`: for a method consistent along a
  solution `y`, with `(r, s) ↦ Φ r (y r) s` continuous on `[a, b] × [0, h₀]`, the defect of `y` is
  at most `τ s` for all steps `s` below some `δ > 0`, for every `τ > 0`.
* `TauCeti.exists_forall_norm_sub_oneStepSeq_le_of_forall_norm_oneStepDefect_le`: a method whose
  defect along `y` is `o(s)` uniformly in time, and whose increment function is Lipschitz in the
  state, converges on every family of meshes whose largest step tends to `0`.
* `TauCeti.exists_forall_norm_sub_oneStepSeq_le_of_consistent`: **consistency implies
  convergence** for jointly continuous increment functions, Lipschitz in the state for steps in
  `[0, h₀]`.

## References

* E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of
  Oxford, 2022, Theorem 5 with Definition 2. There the space is `ℝ` and the mesh is uniform.
* D. Mirzaei, *Lecture notes: numerical solution of ODEs*, arXiv:2412.19959, 2024, Theorem 2.4.
-/

public section

open Filter Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The defect of a consistent method is `o(s)`.** Let `y` be a solution of `y' = f (t, y)` on
`[a, b]`, let the increment function satisfy `Φ r (y r) 0 = f r (y r)` on `[a, b]`, and let
`(r, s) ↦ Φ r (y r) s` be continuous on `[a, b] × [0, h₀]`. Then for every `τ > 0` there is
`δ > 0` such that the defect of `y` is at most `τ s` for every time `t ≥ a` and step
`s ∈ [0, δ]` with `t + s ≤ b`. -/
theorem exists_forall_norm_oneStepDefect_le_of_consistent {f : ℝ → E → E} {Φ : ℝ → E → ℝ → E}
    {y : ℝ → E} {a b h₀ : ℝ} (hh₀ : 0 < h₀) (hy : IsIntegralCurveOn y f (Icc a b))
    (hcont : ContinuousOn (fun q : ℝ × ℝ ↦ Φ q.1 (y q.1) q.2) (Icc a b ×ˢ Icc 0 h₀))
    (hcons : ∀ r ∈ Icc a b, Φ r (y r) 0 = f r (y r)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ δ > 0, ∀ t s, a ≤ t → 0 ≤ s → s ≤ δ → t + s ≤ b → ‖oneStepDefect Φ y t s‖ ≤ τ * s := by
  -- Uniform continuity on the compact rectangle `[a, b] × [0, h₀]`.
  obtain ⟨δ₀, hδ₀, hδ₀τ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont) τ hτ
  refine ⟨min (δ₀ / 2) h₀, by positivity, fun t s ht hs hsδ hts ↦ ?_⟩
  have hsδ₀ : s < δ₀ := by linarith [min_le_left (δ₀ / 2) h₀]
  have hsh₀ : s ≤ h₀ := hsδ.trans (min_le_right _ _)
  have hsub : Icc t (t + s) ⊆ Icc a b := Icc_subset_Icc ht hts
  -- Over the step, `y' r = Φ r (y r) 0` stays within `τ` of `Φ t (y t) s`.
  have hbound : ∀ r ∈ Icc t (t + s), ‖f r (y r) - Φ t (y t) s‖ ≤ τ := by
    intro r hr
    have hdist : dist (r, (0 : ℝ)) (t, s) < δ₀ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff, abs_lt, abs_lt]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hr.1, hr.2]
    have := hδ₀τ (r, 0) ⟨hsub hr, left_mem_Icc.2 hh₀.le⟩ (t, s)
      ⟨hsub (left_mem_Icc.2 (by linarith)), hs, hsh₀⟩ hdist
    rw [dist_eq_norm, hcons r (hsub hr)] at this
    exact this.le
  have hmvt := (convex_Icc t (t + s)).norm_image_sub_le_of_norm_hasDerivWithin_le'
    (fun r hr ↦ (hy r (hsub hr)).mono hsub) hbound (left_mem_Icc.2 (by linarith))
    (right_mem_Icc.2 (by linarith))
  rwa [add_sub_cancel_left, Real.norm_of_nonneg hs, ← oneStepDefect_def] at hmvt

/-- **Convergence of methods with defect `o(s)`.** Let the defect of a curve `y` be `o(s)`
uniformly in time: for every `τ > 0` there is `δ > 0` with `‖oneStepDefect Φ y t s‖ ≤ τ s` for
every time `t ≥ a` and step `s ∈ [0, δ]` with `t + s ≤ b`. Let `u ↦ Φ t u s` be `L`-Lipschitz for
`t ≥ a` and `s ∈ [0, h₀]` with `t + s ≤ b`, where `h₀ > 0`. Then for every `ε > 0` there is
`δ > 0` such that on every mesh with first node `a`, steps in `[0, δ]` and `t_N ≤ b`, the
numerical solution started at `y a` is within `ε` of `y` at the nodes `t_n` with `n ≤ N`. -/
theorem exists_forall_norm_sub_oneStepSeq_le_of_forall_norm_oneStepDefect_le
    {Φ : ℝ → E → ℝ → E} {y : ℝ → E} {a b h₀ : ℝ} {L : ℝ≥0} (hh₀ : 0 < h₀)
    (hΦ : ∀ t s, a ≤ t → 0 ≤ s → s ≤ h₀ → t + s ≤ b → LipschitzWith L fun u ↦ Φ t u s)
    (hdef : ∀ τ > 0, ∃ δ > 0, ∀ t s, a ≤ t → 0 ≤ s → s ≤ δ → t + s ≤ b →
      ‖oneStepDefect Φ y t s‖ ≤ τ * s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode a h N ≤ b →
      ∀ n ≤ N, ‖y (meshNode a h n) - oneStepSeq Φ a h (y a) n‖ ≤ ε := by
  -- Choose the rate `τ > 0` so small that `gronwallBound 0 L τ (b - a) ≤ ε`.
  have hbound := (gronwallBound_continuous_ε 0 L (b - a)).tendsto 0
  rw [gronwallBound_ε0_δ0] at hbound
  obtain ⟨τ, hτε, hτ⟩ := ((hbound.eventually (Iic_mem_nhds hε)).filter_mono
    nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  obtain ⟨δ, hδ, hdefτ⟩ := hdef τ hτ
  refine ⟨min δ h₀, by positivity, fun h N hh hb n hn ↦ ?_⟩
  have hh0 : ∀ n < N, 0 ≤ h n := fun n hn ↦ (hh n hn).1
  -- The step from the node `t_k` with `k < N` stays in `[a, b]`.
  have hend : ∀ k < N, meshNode a h k + h k ≤ b := fun k hk ↦ by
    rw [← meshNode_succ]
    exact (monotoneOn_meshNode hh0 (Set.mem_Iic.2 hk) (Set.mem_Iic.2 le_rfl) hk).trans hb
  have herr := norm_sub_oneStepSeq_le (p := 0) (C := τ) (y a) hh hb
    (fun k hk ↦ hΦ _ _ (self_le_meshNode hh0 hk.le) (hh0 k hk)
      ((hh k hk).2.trans (min_le_right _ _)) (hend k hk))
    (fun t s ht hs hsδ hts ↦ by
      simpa using hdefτ t s ht hs (hsδ.trans (min_le_left _ _)) hts) hn
  simp only [sub_self, norm_zero, pow_zero, mul_one] at herr
  refine herr.trans (le_trans ?_ hτε)
  exact gronwallBound_mono le_rfl hτ.le L.coe_nonneg (sub_le_sub_right
    ((monotoneOn_meshNode hh0 (Set.mem_Iic.2 hn) (Set.mem_Iic.2 le_rfl) hn).trans hb) a)

/-- **Consistency implies convergence.** Let `y` be a solution of `y' = f (t, y)` on `[a, b]`,
and let the increment function `Φ` be jointly continuous, consistent with `f`
(`Φ t u 0 = f t u`) and `L`-Lipschitz in the state for every time and every step in `[0, h₀]`,
where `h₀ > 0`. Then for every `ε > 0` there is `δ > 0` such that on every mesh with first node
`a`, steps in `[0, δ]` and `t_N ≤ b`, the numerical solution started at `y a` is within `ε` of
`y` at the nodes `t_n` with `n ≤ N`.

Continuity and consistency are only used along `y`; for that weaker form combine
`TauCeti.exists_forall_norm_oneStepDefect_le_of_consistent` with
`TauCeti.exists_forall_norm_sub_oneStepSeq_le_of_forall_norm_oneStepDefect_le`. -/
theorem exists_forall_norm_sub_oneStepSeq_le_of_consistent {f : ℝ → E → E} {Φ : ℝ → E → ℝ → E}
    {y : ℝ → E} {a b h₀ : ℝ} {L : ℝ≥0} (hh₀ : 0 < h₀) (hy : IsIntegralCurveOn y f (Icc a b))
    (hcont : Continuous fun q : ℝ × E × ℝ ↦ Φ q.1 q.2.1 q.2.2)
    (hcons : ∀ t u, Φ t u 0 = f t u)
    (hΦ : ∀ t s, 0 ≤ s → s ≤ h₀ → LipschitzWith L fun u ↦ Φ t u s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (h : ℕ → ℝ) (N : ℕ), (∀ n < N, 0 ≤ h n ∧ h n ≤ δ) → meshNode a h N ≤ b →
      ∀ n ≤ N, ‖y (meshNode a h n) - oneStepSeq Φ a h (y a) n‖ ≤ ε := by
  have hcurve : ContinuousOn (fun q : ℝ × ℝ ↦ Φ q.1 (y q.1) q.2) (Icc a b ×ˢ Icc 0 h₀) :=
    hcont.comp_continuousOn (continuousOn_fst.prodMk
      ((hy.continuousOn.comp continuousOn_fst mapsTo_fst_prod).prodMk continuousOn_snd))
  exact exists_forall_norm_sub_oneStepSeq_le_of_forall_norm_oneStepDefect_le hh₀
    (fun t s _ hs hsh₀ _ ↦ hΦ t s hs hsh₀)
    (fun _ hτ ↦ exists_forall_norm_oneStepDefect_le_of_consistent hh₀ hy hcurve
      (fun r _ ↦ hcons r (y r)) hτ) hε

end TauCeti
