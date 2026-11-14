/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Convex.Conjugate
public import TauCeti.MeasureTheory.OptimalTransport.Cost.CyclicalMonotonicity
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Monge
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Convex.Superlinear
import TauCeti.MeasureTheory.Covering.Besicovitch
import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
import TauCeti.MeasureTheory.OptimalTransport.CTransform.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Existence.CyclicalMonotonicity
import TauCeti.MeasureTheory.OptimalTransport.Existence.Finite
import TauCeti.MeasureTheory.OptimalTransport.Twist.StrictConvex

/-!
# Gangbo–McCann's theorem for strictly convex displacement costs

For a strictly convex displacement cost `c (x, y) = h (x - y)` on a finite-dimensional real inner
product space `E`, `TauCeti.gradient_fenchelConjugate_eq_sub_of_mem_contactSet` shows that at any
point `x` where a `c`-concave potential `φ` is finite nearby and differentiable, its unique contact
partner is `T x = x - ∇h⋆(∇φ x)`, where `h⋆` is the Legendre–Fenchel conjugate of `h`. Turning this
pointwise formula into an optimal transport theorem requires two regularity ingredients that are
automatic in the quadratic case `h z = ‖z‖ ^ 2 / 2` (where `x ↦ ‖x‖ ^ 2 / 2 - φ x` is convex)
but require geometric control of `h` in general:

1. **Full-measure interior of the finiteness domain** (Gangbo–McCann, Proposition 3.3). Even for
   smooth strictly convex superlinear `h` on `ℝ²`, a `c`-concave potential `φ` can take `-∞` on a
   dense set while remaining finite on a set of positive Lebesgue measure unless the level sets of
   `h` satisfy the cone condition (H2) at infinity: for every height `r` and aperture `θ ∈ (0, π)`,
   every sufficiently distant vertex `p` admits `z ≠ 0` such that `h ≤ h p` on the truncated cone
   `{x | ‖x - p‖ ‖z‖ cos (θ / 2) ≤ ⟪z, x - p⟫ ≤ r ‖z‖}`. Under continuity of `h` and (H2), a
   finite net on the unit sphere forces any point where `φ = ⊥` to propagate `φ = ⊥` to a ball of
   comparable radius nearby, so `{x | φ x ≠ ⊥} \ interior {x | φ x ≠ ⊥}` has zero Haar measure by
   Lebesgue's density theorem (`TauCeti.addHaar_diff_interior_setOf_cTransformSymm_ne_bot_eq_zero`),
   and `φ` is locally bounded below on `interior {x | φ x ≠ ⊥}`
   (`TauCeti.exists_eventually_le_cTransformSymm_of_mem_interior`).
2. **Local Lipschitzness and Rademacher differentiability** (Gangbo–McCann, Proposition C.2). Under
   convexity of `h` and superlinear growth `h z / ‖z‖ → ∞`, local lower bounds and upper
   semicontinuity of `φ` confine nearly optimal target points `y` for `x₁` near `x₀` to a bounded
   ball, where `h` is Lipschitz; hence `x ↦ (φ x).toReal` is locally Lipschitz wherever `φ` is
   locally bounded below (`TauCeti.locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le`), and
   therefore differentiable Haar-almost everywhere on `{x | φ x ≠ ⊥}` by Rademacher's theorem
   (`TauCeti.ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm`).

Combining these regularity results with
`TauCeti.exists_isOptimalCoupling_isCyclicallyMonotone_support` and Rockafellar–Rüschendorf
(`TauCeti.IsCyclicallyMonotone.exists_isCConcave_subset_cSuperdifferential`) yields Gangbo and
McCann's Theorem 1.2: for probability measures `μ` and `ν` with `μ` absolutely continuous with
respect to Haar measure, there is a `c`-concave potential `φ` such that `T x = x - ∇h⋆(∇φ x)` is a
Kantorovich-optimal transport map whose graph plan has `c`-cyclically monotone support
(`TauCeti.exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn`), even when the
optimal transport cost is `∞`. When the optimal cost is finite, both the optimal coupling and the
optimal transport map are unique
(`TauCeti.IsOptimalCoupling.unique_of_strictConvexOn`,
`TauCeti.exists_isKantorovichOptimalTransportMap_of_strictConvexOn`). When `h` is also
differentiable, `∇h⋆` is the two-sided inverse of `∇h` by
`TauCeti.leftInverse_gradient_fenchelConjugate_of_superlinear` and
`TauCeti.rightInverse_gradient_fenchelConjugate_of_superlinear`.

## Main statements

* `TauCeti.exists_eventually_le_cTransformSymm_of_mem_interior` — under continuity of `h` and the
  cone condition, `cTransformSymm` is locally bounded below on `interior {x | φ x ≠ ⊥}`;
* `TauCeti.addHaar_diff_interior_setOf_cTransformSymm_ne_bot_eq_zero` — under continuity of `h` and
  the cone condition, `{x | φ x ≠ ⊥} \ interior {x | φ x ≠ ⊥}` is Haar-null;
* `TauCeti.locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le` and
  `TauCeti.locallyLipschitzOn_interior_toReal_cTransformSymm` — local Lipschitzness of the real
  representative of `cTransformSymm` for convex superlinear `h`;
* `TauCeti.ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm` — Haar-almost everywhere
  local finiteness and differentiability on `{x | φ x ≠ ⊥}`;
* `TauCeti.eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn` — any plan with Haar-regular
  first marginal concentrated on `cSuperdifferential c φ` is the graph plan of
  `x ↦ x - ∇h⋆(∇φ x)`;
* `TauCeti.IsOptimalCoupling.exists_eq_graphPlan_of_strictConvexOn` and
  `TauCeti.IsOptimalCoupling.unique_of_strictConvexOn` — map representation and uniqueness of
  finite-cost optimal plans;
* `TauCeti.exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn` — unconditional
  existence of a `c`-concave potential and cyclically/Kantorovich-optimal map `x ↦ x - ∇h⋆(∇φ x)`;
* `TauCeti.exists_isKantorovichOptimalTransportMap_of_strictConvexOn` — finite-cost existence and
  uniqueness of the Kantorovich-optimal transport map and optimal plan.

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Theorem 1.2, Proposition 3.3, and Proposition C.2.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 10.28.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal Gradient NNReal RealInnerProductSpace Topology

namespace TauCeti

/-! ### Cone condition and regularity of the finiteness domain -/

section ConeRegularity

private theorem cos_pi_div_four_bounds :
    0 ≤ Real.cos ((Real.pi / 2) / 2) ∧ Real.cos ((Real.pi / 2) / 2) ≤ 3 / 4 := by
  have hdiv : (Real.pi / 2) / 2 = Real.pi / 4 := by ring
  rw [hdiv, Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by positivity, by norm_num⟩
  exact ⟨by positivity, by linarith⟩

/-- On a nontrivial finite-dimensional normed space, `sphere (0 : E) 1` admits a nonempty finite
`1 / 20`-net. -/
private theorem exists_finset_sphere_net {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    ∃ F : Finset E, F.Nonempty ∧ (↑F : Set E) ⊆ sphere (0 : E) 1 ∧
      ∀ w ∈ sphere (0 : E) 1, ∃ u ∈ F, ‖w - u‖ < 1 / 20 := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  have hne : (sphere (0 : E) 1).Nonempty :=
    ⟨(‖v₀‖⁻¹ : ℝ) • v₀, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hv₀)⟩
  obtain ⟨F, hFsub, hFcov⟩ :=
    (isCompact_sphere (0 : E) 1).elim_nhds_subcover (fun u ↦ ball u (1 / 20))
      fun u _ ↦ ball_mem_nhds u (by positivity)
  have hFne : F.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨u, hu, -⟩ := mem_iUnion₂.1 (hFcov hw)
    exact ⟨u, hu⟩
  refine ⟨F, hFne, hFsub, fun w hw ↦ ?_⟩
  obtain ⟨u, huF, hwu⟩ := mem_iUnion₂.1 (hFcov hw)
  exact ⟨u, huF, mem_ball_iff_norm.1 hwu⟩

/-- Any point of `closedBall (x₀ + (δ / 2) • u) (δ / 80)` with `u` on the unit sphere within
`1 / 20` of `‖z‖⁻¹ • z` and `0 < δ ≤ 1` lies in the truncated cone of height `1` and aperture
`π / 2` in direction `z`. -/
private theorem mem_truncatedCone_of_mem_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {z u x₀ x p : E} {δ : ℝ} (hz : z ≠ 0)
    (hu : u ∈ sphere (0 : E) 1) (hzu : ‖(‖z‖⁻¹ : ℝ) • z - u‖ < 1 / 20)
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) (hx : x ∈ closedBall (x₀ + (δ / 2) • u) (δ / 80)) :
    ‖(x - x₀ + p) - p‖ * ‖z‖ * Real.cos ((Real.pi / 2) / 2) ≤ ⟪z, (x - x₀ + p) - p⟫ ∧
      ⟪z, (x - x₀ + p) - p⟫ ≤ 1 * ‖z‖ := by
  have hnorm_u : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set e := x - (x₀ + (δ / 2) • u)
  have he : ‖e‖ ≤ δ / 80 := mem_closedBall_iff_norm.1 hx
  have hdiff : (x - x₀ + p) - p = (δ / 2) • u + e := by simp only [e]; abel
  have hnorm_diff : ‖(x - x₀ + p) - p‖ ≤ 41 / 80 * δ := by
    rw [hdiff]
    calc ‖(δ / 2) • u + e‖ ≤ ‖(δ / 2) • u‖ + ‖e‖ := norm_add_le _ _
      _ = δ / 2 + ‖e‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hnorm_u, mul_one]
      _ ≤ 41 / 80 * δ := by linarith
  refine ⟨?_, ?_⟩
  · set w := (‖z‖⁻¹ : ℝ) • z
    have h1 : ⟪u, e⟫ ≥ -(δ / 80) := by
      have := abs_real_inner_le_norm u e
      rw [hnorm_u, one_mul] at this
      linarith [(abs_le.1 this).1]
    have h2 : ⟪w - u, (x - x₀ + p) - p⟫ ≥ -(41 / 1600 * δ) := by
      have := abs_real_inner_le_norm (w - u) ((x - x₀ + p) - p)
      have hprod : ‖w - u‖ * ‖(x - x₀ + p) - p‖ ≤ 1 / 20 * (41 / 80 * δ) :=
        mul_le_mul hzu.le hnorm_diff (norm_nonneg _) (by positivity)
      linarith [(abs_le.1 this).1, hprod]
    have h3 : ⟪w, (x - x₀ + p) - p⟫ ≥ 739 / 1600 * δ := by
      have hwu : w = u + (w - u) := by abel
      rw [hwu, inner_add_left]
      have hu_diff : ⟪u, (x - x₀ + p) - p⟫ = δ / 2 + ⟪u, e⟫ := by
        rw [hdiff, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hnorm_u]
        ring
      linarith
    have hz_eq : ⟪z, (x - x₀ + p) - p⟫ = ‖z‖ * ⟪w, (x - x₀ + p) - p⟫ := by
      have : z = ‖z‖ • w := by simp [w, smul_smul, hz_pos.ne']
      conv_lhs => rw [this]
      rw [inner_smul_left, RCLike.conj_to_real]
    calc ‖(x - x₀ + p) - p‖ * ‖z‖ * Real.cos ((Real.pi / 2) / 2)
        ≤ (41 / 80 * δ) * ‖z‖ * (3 / 4) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hnorm_diff hz_pos.le)
            cos_pi_div_four_bounds.2 cos_pi_div_four_bounds.1 (by positivity)
      _ ≤ ‖z‖ * (739 / 1600 * δ) := by nlinarith
      _ ≤ ‖z‖ * ⟪w, (x - x₀ + p) - p⟫ := mul_le_mul_of_nonneg_left h3 hz_pos.le
      _ = ⟪z, (x - x₀ + p) - p⟫ := hz_eq.symm
  · calc ⟪z, (x - x₀ + p) - p⟫ ≤ ‖z‖ * ‖(x - x₀ + p) - p‖ := real_inner_le_norm _ _
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left (by linarith) hz_pos.le
      _ = 1 * ‖z‖ := by ring

/-- On compact balls around `x₀`, continuity of `h` bounds `(h (x - y) : EReal) - ψ y` from below
whenever `cTransformSymm` avoids `⊥` at a reference point `x_ref` within distance `1` of `x₀`. -/
private theorem le_sub_of_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {h : E → ℝ} (hc : Continuous h) {ψ : E → EReal} {x₀ x_ref : E}
    {R : ℝ} (hR : 0 ≤ R) (href_dist : ‖x_ref - x₀‖ ≤ 1)
    (href_bot : cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x_ref ≠ ⊥)
    (hψ_top : ∀ y, ψ y ≠ ⊤) :
    ∃ m₀ : ℝ, ∀ x y : E, ‖x - x₀‖ ≤ 1 → ‖x₀ - y‖ ≤ R →
      (m₀ : EReal) ≤ (h (x - y) : EReal) - ψ y := by
  obtain ⟨m_h, -, hm_h⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_isMinOn
    (nonempty_closedBall.2 (by positivity)) hc.continuousOn
  obtain ⟨M_h, -, hM_h⟩ := (isCompact_closedBall (0 : E) (R + 1)).exists_isMaxOn
    (nonempty_closedBall.2 (by positivity)) hc.continuousOn
  by_cases hall : ∀ y, ψ y = ⊥
  · exact ⟨0, fun _ y _ _ ↦ by simp [hall y]⟩
  push Not at hall
  obtain ⟨y₁, hy₁⟩ := hall
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  have href_top : φ x_ref ≠ ⊤ := (cTransformSymm_lt_top_of_ne_bot _ hy₁ x_ref).ne
  refine ⟨h m_h - h M_h + (φ x_ref).toReal, fun x y hx hy ↦ ?_⟩
  rcases eq_or_ne (ψ y) ⊥ with hybot | hybot
  · simp [hybot]
  have hψy : ψ y = ((ψ y).toReal : EReal) := (EReal.coe_toReal (hψ_top y) hybot).symm
  have hφ_le : ((φ x_ref).toReal : EReal) ≤ (h (x_ref - y) : EReal) - ((ψ y).toReal : EReal) := by
    rw [EReal.coe_toReal href_top href_bot, ← hψy]
    exact cTransformSymm_le _ ψ x_ref y
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hφ_le
  have hx_mem : x - y ∈ closedBall (0 : E) (R + 1) := mem_closedBall_zero_iff.2 <| by
    calc ‖x - y‖ = ‖(x - x₀) + (x₀ - y)‖ := by congr 1; abel
      _ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have href_mem : x_ref - y ∈ closedBall (0 : E) (R + 1) := mem_closedBall_zero_iff.2 <| by
    calc ‖x_ref - y‖ = ‖(x_ref - x₀) + (x₀ - y)‖ := by congr 1; abel
      _ ≤ ‖x_ref - x₀‖ + ‖x₀ - y‖ := norm_add_le _ _
      _ ≤ R + 1 := by linarith
  have hlo : h m_h ≤ h (x - y) := isMinOn_iff.1 hm_h _ hx_mem
  have hhi : h (x_ref - y) ≤ h M_h := isMaxOn_iff.1 hM_h _ href_mem
  rw [hψy, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  linarith

private theorem closedBall_shift_subset_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x₀ x₁ u : E} {δ : ℝ} (hδ₀ : 0 < δ)
    (hx₁ : x₁ ∈ ball x₀ (δ / 4)) (hu : u ∈ sphere (0 : E) 1) :
    closedBall (x₁ + (δ / 2) • u) (δ / 80) ⊆ closedBall x₀ δ := fun x hx ↦ by
  rw [mem_closedBall_iff_norm] at hx ⊢
  have hx₁' := mem_ball_iff_norm.1 hx₁
  have hu' : ‖(δ / 2) • u‖ = δ / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      mem_sphere_zero_iff_norm.1 hu, mul_one]
  calc ‖x - x₀‖ = ‖(x - (x₁ + (δ / 2) • u)) + (δ / 2) • u + (x₁ - x₀)‖ := by congr 1; abel
    _ ≤ ‖x - (x₁ + (δ / 2) • u)‖ + ‖(δ / 2) • u‖ + ‖x₁ - x₀‖ := norm_add₃_le
    _ ≤ δ := by linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ}

/-- Cone-net propagation lemma: under the cone condition (H2), there exist `R ≥ 0` and a finite
subset `F` of the unit sphere such that for every distant `p` (`R < ‖p‖`), every center `x₀`, and
every `δ ∈ (0, 1]`, some `u ∈ F` satisfies `h (x - x₀ + p) ≤ h p` throughout
`closedBall (x₀ + (δ / 2) • u) (δ / 80)`. -/
private theorem exists_net_forall_closedBall_le [Nontrivial E]
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p) :
    ∃ (R : ℝ) (F : Finset E), 0 ≤ R ∧ F.Nonempty ∧ (↑F : Set E) ⊆ sphere (0 : E) 1 ∧
      ∀ p, R < ‖p‖ → ∀ x₀ : E, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ u ∈ F, ∀ x ∈ closedBall (x₀ + (δ / 2) • u) (δ / 80), h (x - x₀ + p) ≤ h p := by
  obtain ⟨R₀, hR₀⟩ := h_cone 1 (Real.pi / 2) (by positivity) (by linarith [Real.pi_pos])
  obtain ⟨F, hFne, hFsub, hFnet⟩ := exists_finset_sphere_net (E := E)
  refine ⟨max R₀ 0, F, le_max_right _ _, hFne, hFsub, fun p hp x₀ δ hδ₀ hδ₁ ↦ ?_⟩
  obtain ⟨z, hz, hcone_z⟩ := hR₀ p ((le_max_left R₀ 0).trans_lt hp)
  have hz_mem : (‖z‖⁻¹ : ℝ) • z ∈ sphere (0 : E) 1 :=
    mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hz)
  obtain ⟨u, huF, hzu⟩ := hFnet _ hz_mem
  refine ⟨u, huF, fun x hx ↦ ?_⟩
  obtain ⟨hc₁, hc₂⟩ := mem_truncatedCone_of_mem_closedBall hz (hFsub huF) hzu hδ₀ hδ₁ hx
  exact hcone_z (x - x₀ + p) hc₁ hc₂

/-- **Local lower bound on the interior of the finiteness domain** (Gangbo–McCann, Proposition 3.3).
If `h` is continuous and satisfies the cone condition (H2), then `cTransformSymm` for the cost
`h (x - y)` is locally bounded below by a real constant around every point of
`interior {x | cTransformSymm c ψ x ≠ ⊥}`. -/
theorem exists_eventually_le_cTransformSymm_of_mem_interior (hc : Continuous h)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {ψ : E → EReal} {x₀ : E}
    (hx₀ : x₀ ∈ interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}) :
    ∃ m : ℝ, ∀ᶠ x in 𝓝 x₀, (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  by_cases hall : ∀ y, ψ y = ⊥
  · exact ⟨0, Eventually.of_forall fun x ↦ le_cTransformSymm fun y ↦ by simp [hall y]⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y, ψ y ≠ ⊥ := by simpa using hall
  have hx₀_bot : φ x₀ ≠ ⊥ := interior_subset hx₀
  have hψ_top : ∀ y, ψ y ≠ ⊤ := fun y hy ↦ hx₀_bot <| eq_bot_iff.2 <| by
    simpa [hy] using cTransformSymm_le (fun z : E × E ↦ h (z.1 - z.2)) ψ x₀ y
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · refine ⟨(φ x₀).toReal, Eventually.of_forall fun x ↦ ?_⟩
    rw [Subsingleton.elim x x₀,
      EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ x₀).ne hx₀_bot]
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx₀)
  set δ := min (δ₀ / 2) 1
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 := min_le_right _ _
  have hcb_sub : closedBall x₀ δ ⊆ {x | φ x ≠ ⊥} :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hδ₀_sub
  obtain ⟨R, F, hR₀, hFne, hFsub, hnet⟩ := exists_net_forall_closedBall_le h_cone
  obtain ⟨m₀, hm₀⟩ := le_sub_of_norm_sub_le hc (by positivity : 0 ≤ R + 1)
    (by simp : ‖x₀ - x₀‖ ≤ 1) hx₀_bot hψ_top
  set m₁ := F.inf' hFne fun u ↦ (φ (x₀ + (δ / 2) • u)).toReal
  refine ⟨min m₀ m₁, eventually_of_mem (closedBall_mem_nhds x₀ (by positivity : 0 < δ / 80))
    fun x hx ↦ le_cTransformSymm fun y ↦ ?_⟩
  have hx_dist : ‖x - x₀‖ ≤ δ / 80 := mem_closedBall_iff_norm.1 hx
  by_cases hyR : ‖x₀ - y‖ ≤ R + 1
  · exact (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans
      (hm₀ x y (hx_dist.trans (by linarith)) hyR)
  push Not at hyR
  have hp : R < ‖x - y‖ := by
    have htri : ‖x₀ - y‖ - ‖x₀ - x‖ ≤ ‖x - y‖ := by
      simpa only [sub_sub_sub_cancel_left] using norm_sub_norm_le (x₀ - y) (x₀ - x)
    rw [norm_sub_rev x₀ x] at htri
    linarith
  obtain ⟨u, huF, hu_le⟩ := hnet (x - y) hp x δ hδ_pos hδ_le
  set z := x₀ + (δ / 2) • u
  have hz_mem : z ∈ closedBall (x + (δ / 2) • u) (δ / 80) := mem_closedBall_iff_norm.2 <| by
    simpa only [z, add_sub_add_right_eq_sub, norm_sub_rev] using hx_dist
  have hzy : h (z - y) ≤ h (x - y) := by simpa only [sub_add_sub_cancel] using hu_le z hz_mem
  have hz_bot : φ z ≠ ⊥ := hcb_sub <| mem_closedBall_iff_norm.2 <| by
    rw [show z - x₀ = (δ / 2) • u by simp [z], norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < δ / 2), mem_sphere_zero_iff_norm.1 (hFsub huF), mul_one]
    linarith
  calc ((min m₀ m₁ : ℝ) : EReal) ≤ (m₁ : EReal) := EReal.coe_le_coe_iff.2 (min_le_right _ _)
    _ ≤ ((φ z).toReal : EReal) := EReal.coe_le_coe_iff.2 (Finset.inf'_le _ huF)
    _ = φ z := EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ z).ne hz_bot
    _ ≤ (h (z - y) : EReal) - ψ y := cTransformSymm_le _ ψ z y
    _ ≤ (h (x - y) : EReal) - ψ y := EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hzy) le_rfl

/-- If `cTransformSymm` takes `⊥` at `x₁`, then under continuity of `h` and the cone condition (H2),
it takes `⊥` on an entire ball `closedBall (x₁ + (δ / 2) • u) (δ / 80)` for some unit vector `u`. -/
private theorem exists_closedBall_subset_setOf_cTransformSymm_eq_bot [Nontrivial E]
    (hc : Continuous h)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {ψ : E → EReal} {x₁ : E}
    (hx₁ : cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x₁ = ⊥) {δ : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ u ∈ sphere (0 : E) 1,
      closedBall (x₁ + (δ / 2) • u) (δ / 80) ⊆
        {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x = ⊥} := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  obtain ⟨R, F, hR₀, hFne, hFsub, hnet⟩ := exists_net_forall_closedBall_le h_cone
  by_contra! hcon
  have hcon' : ∀ u, ∃ x, u ∈ F → x ∈ closedBall (x₁ + (δ / 2) • u) (δ / 80) ∧ φ x ≠ ⊥ := fun u ↦ by
    by_cases hu : u ∈ F
    · obtain ⟨x, hx_cb, hx_bot⟩ := not_subset.1 (hcon u (hFsub hu))
      exact ⟨x, fun _ ↦ ⟨hx_cb, hx_bot⟩⟩
    · exact ⟨x₁, fun h ↦ (hu h).elim⟩
  choose g hg using hcon'
  obtain ⟨u₀, hu₀⟩ := hFne
  have hy_ne_bot : ∃ y, ψ y ≠ ⊥ := by
    by_contra! hall
    have htop : φ x₁ = ⊤ := eq_top_iff.2 (le_cTransformSymm fun y ↦ by simp [hall y])
    exact bot_ne_top (hx₁.symm.trans htop)
  obtain ⟨y₁, hy₁⟩ := hy_ne_bot
  have hψ_top : ∀ y, ψ y ≠ ⊤ := fun y hy ↦ (hg u₀ hu₀).2 <| eq_bot_iff.2 <| by
    simpa [hy] using cTransformSymm_le (fun z : E × E ↦ h (z.1 - z.2)) ψ (g u₀) y
  have hgu₀_dist : ‖g u₀ - x₁‖ ≤ 1 := by
    have hmem := mem_closedBall_iff_norm.1 (hg u₀ hu₀).1
    have hu₀_norm : ‖(δ / 2) • u₀‖ = δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        mem_sphere_zero_iff_norm.1 (hFsub hu₀), mul_one]
    calc ‖g u₀ - x₁‖ = ‖(g u₀ - (x₁ + (δ / 2) • u₀)) + (δ / 2) • u₀‖ := by congr 1; abel
      _ ≤ ‖g u₀ - (x₁ + (δ / 2) • u₀)‖ + ‖(δ / 2) • u₀‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  obtain ⟨m₀, hm₀⟩ := le_sub_of_norm_sub_le hc hR₀ hgu₀_dist (hg u₀ hu₀).2 hψ_top
  set m₁ := F.inf' ⟨u₀, hu₀⟩ fun u ↦ (φ (g u)).toReal
  set m := min m₀ m₁ - 1
  have hlt : φ x₁ < (m : EReal) := hx₁ ▸ EReal.bot_lt_coe m
  rw [show φ x₁ = _ from cTransformSymm_apply _ ψ x₁] at hlt
  obtain ⟨y, hy⟩ := iInf_lt_iff.1 hlt
  have hyR : R < ‖x₁ - y‖ := by
    by_contra! hle
    have hge := hm₀ x₁ y (by simp) hle
    exact (hy.trans_le (EReal.coe_le_coe_iff.2 (by linarith [min_le_left m₀ m₁]))).not_ge hge
  obtain ⟨u, huF, hu_le⟩ := hnet (x₁ - y) hyR x₁ δ hδ₀ hδ₁
  have hguy : h (g u - y) ≤ h (x₁ - y) := by
    simpa only [sub_add_sub_cancel] using hu_le (g u) (hg u huF).1
  have hgu_le : ((φ (g u)).toReal : EReal) ≤ (h (x₁ - y) : EReal) - ψ y := by
    calc ((φ (g u)).toReal : EReal) = φ (g u) :=
          EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ (g u)).ne (hg u huF).2
      _ ≤ (h (g u - y) : EReal) - ψ y := cTransformSymm_le _ ψ (g u) y
      _ ≤ (h (x₁ - y) : EReal) - ψ y := EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hguy) le_rfl
  have hm_lt : (m : EReal) < ((φ (g u)).toReal : EReal) := EReal.coe_lt_coe_iff.2 <| by
    linarith [min_le_right m₀ m₁, Finset.inf'_le (f := fun u ↦ (φ (g u)).toReal) huF]
  exact (hy.trans hm_lt).not_ge hgu_le

/-- **The finiteness domain of `cTransformSymm` equals its interior up to Haar measure zero**
(Gangbo–McCann, Proposition 3.3). Under continuity of `h` and the cone condition (H2), the
boundary points `{x | cTransformSymm c ψ x ≠ ⊥} \ interior {x | cTransformSymm c ψ x ≠ ⊥}` have
zero additive Haar measure. -/
theorem addHaar_diff_interior_setOf_cTransformSymm_ne_bot_eq_zero
    [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure] (hc : Continuous h)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    ρ ({x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥} \
      interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}) = 0 := by
  set S := {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · have : DiscreteTopology E := Finite.instDiscreteTopology
    rw [(isOpen_discrete S).interior_eq, sdiff_self, measure_empty]
  have hS_meas : NullMeasurableSet S ρ :=
    (measurable_cTransformSymm_of_upperSemicontinuous
      (fun y ↦ (hc.comp (continuous_id.sub continuous_const)).upperSemicontinuous) ψ
      (measurableSet_singleton ⊥).compl).nullMeasurableSet
  set D := {x | Tendsto (fun r ↦ ρ (S ∩ closedBall x r) / ρ (closedBall x r)) (𝓝[>] 0) (𝓝 1)}
  suffices hsub_int : D ⊆ interior S from
    measure_mono_null (sdiff_subset_sdiff_right hsub_int)
      (ae_eq_set.1 hS_meas.ae_eq_setOf_tendsto_measure_inter_div).1
  intro x₀ hx₀
  by_contra hx₀_int
  have hball_pos : ∀ᶠ r in 𝓝[>] (0 : ℝ), ρ (closedBall x₀ r) ≠ 0 ∧ ρ (closedBall x₀ r) ≠ ∞ :=
    eventually_nhdsWithin_of_forall fun r (hr : 0 < r) ↦
      ⟨((isOpen_ball.measure_pos ρ (nonempty_ball.2 hr)).trans_le
        (measure_mono ball_subset_closedBall)).ne', measure_closedBall_lt_top.ne⟩
  have hcompl := (hS_meas.tendsto_measure_compl_inter_div_iff hball_pos).2 hx₀
  set α : ℝ≥0∞ := ENNReal.ofReal ((1 / 80 : ℝ) ^ Module.finrank ℝ E)
  have hα : 0 < α := ENNReal.ofReal_pos.2 (by positivity)
  have hev := (hcompl.eventually (gt_mem_nhds hα)).and
    (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))
  obtain ⟨δ, ⟨hδ_lt, hδ₀, hδ₁⟩, hρ0, hρtop⟩ := (hev.and hball_pos).exists
  have hnot_sub : ¬ ball x₀ (δ / 4) ⊆ S := fun hsub ↦
    hx₀_int (mem_interior.2 ⟨ball x₀ (δ / 4), hsub, isOpen_ball, mem_ball_self (by positivity)⟩)
  obtain ⟨x₁, hx₁_ball, hx₁_notS⟩ := not_subset.1 hnot_sub
  obtain ⟨u, hu_sph, hu_sub⟩ := exists_closedBall_subset_setOf_cTransformSymm_eq_bot hc h_cone
    (not_not.1 hx₁_notS) hδ₀ hδ₁.le
  have hcb_sub : closedBall (x₁ + (δ / 2) • u) (1 / 80 * δ) ⊆ Sᶜ ∩ closedBall x₀ δ := fun x hx ↦ by
    have hx_cb : x ∈ closedBall (x₁ + (δ / 2) • u) (δ / 80) := by convert hx using 2; ring
    exact ⟨fun hxS ↦ hxS (hu_sub hx_cb),
      closedBall_shift_subset_closedBall hδ₀ hx₁_ball hu_sph hx_cb⟩
  have hmeas_eq : ρ (closedBall (x₁ + (δ / 2) • u) (1 / 80 * δ)) = α * ρ (closedBall x₀ δ) := by
    rw [Measure.addHaar_closedBall_mul_of_pos ρ _ (by norm_num : (0 : ℝ) < 1 / 80) δ,
      Measure.addHaar_closedBall_center ρ x₀ δ]
  have hle : α ≤ ρ (Sᶜ ∩ closedBall x₀ δ) / ρ (closedBall x₀ δ) := by
    calc α = (α * ρ (closedBall x₀ δ)) / ρ (closedBall x₀ δ) :=
          (ENNReal.mul_div_cancel_right hρ0 hρtop).symm
      _ ≤ ρ (Sᶜ ∩ closedBall x₀ δ) / ρ (closedBall x₀ δ) :=
          ENNReal.div_le_div_right (hmeas_eq ▸ measure_mono hcb_sub) _
  exact hδ_lt.not_ge hle

end ConeRegularity

/-! ### Local Lipschitzness and Rademacher differentiability -/

section LocallyLipschitz

/-- Convexity and superlinearity of `h` confine nearly optimal target points `y` for `x₁` near
`x₀` to a bounded ball around `x₁`, provided `cTransformSymm` is bounded below on `ball x₀ η`. -/
private theorem exists_norm_sub_le_of_sub_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    {ψ : E → EReal} {x₀ : E} {η m M : ℝ} (hη : 0 < η)
    (hm : ∀ x' ∈ ball x₀ η, (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x') :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x₁ ∈ ball x₀ (η / 2), ∀ y : E,
      ψ y ≠ ⊥ → ψ y ≠ ⊤ → h (x₁ - y) - (ψ y).toReal < M + 1 → ‖x₁ - y‖ ≤ R := by
  set C := max 0 (2 * (M + 1 - m) / η) + |h 0| / η + 1
  obtain ⟨R₀, -, hR₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1
    (h_superlinear.eventually_ge_atTop C)
  refine ⟨max R₀ η + 1, by positivity, fun x₁ hx₁ y hy_bot hy_top hlt ↦ ?_⟩
  by_contra! hgt
  set v := x₁ - y
  have hv_η : η < ‖v‖ := lt_of_le_of_lt (by linarith [le_max_right R₀ η]) hgt
  have hv_pos : 0 < ‖v‖ := hη.trans hv_η
  have hv_C : C ≤ h v / ‖v‖ := hR₀ ((le_max_left R₀ η).trans (by linarith) : R₀ ≤ ‖v‖)
  set t := η / (2 * ‖v‖)
  have ht_pos : 0 < t := by positivity
  have ht_lt : t < 1 := by rw [div_lt_one (by positivity)]; linarith
  set x' := x₁ - t • v
  have hx'_mem : x' ∈ ball x₀ η := by
    rw [mem_ball_iff_norm]
    have hx₁_norm : ‖x₁ - x₀‖ < η / 2 := mem_ball_iff_norm.1 hx₁
    have htv_norm : ‖t • v‖ = η / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
      simp only [t]
      field_simp
    calc ‖x' - x₀‖ = ‖(x₁ - x₀) - t • v‖ := by simp only [x', sub_right_comm]
      _ ≤ ‖x₁ - x₀‖ + ‖t • v‖ := norm_sub_le _ _
      _ < η := by linarith
  have hm_x' : (m : EReal) ≤ (h (x' - y) : EReal) - ((ψ y).toReal : EReal) := by
    rw [EReal.coe_toReal hy_top hy_bot]
    exact (hm x' hx'_mem).trans (cTransformSymm_le _ ψ x' y)
  rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at hm_x'
  have hconv_step : h (x' - y) ≤ (1 - t) * h v + t * h 0 := by
    have heq : x' - y = (1 - t) • v + t • (0 : E) := by
      simp only [x', v, sub_smul, one_smul, smul_zero, add_zero]
      abel
    rw [heq]
    exact hh.2 (mem_univ v) (mem_univ 0) (by linarith) ht_pos.le (by ring)
  have hslope : t * (h v - h 0) < M + 1 - m := by linarith
  have hdiv₁ : (h v - h 0) / ‖v‖ < 2 * (M + 1 - m) / η := by
    have hmul : (2 / η) * (t * (h v - h 0)) < (2 / η) * (M + 1 - m) :=
      mul_lt_mul_of_pos_left hslope (by positivity)
    have hident : (2 / η) * (t * (h v - h 0)) = (h v - h 0) / ‖v‖ := by
      simp only [t]
      field_simp
    rwa [hident, show (2 / η) * (M + 1 - m) = 2 * (M + 1 - m) / η by ring] at hmul
  have hdiv₂ : h 0 / ‖v‖ ≤ |h 0| / η :=
    (div_le_div_of_nonneg_right (le_abs_self _) hv_pos.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hη hv_η.le)
  have hsum : h v / ‖v‖ = (h v - h 0) / ‖v‖ + h 0 / ‖v‖ := by ring
  linarith [le_max_right 0 (2 * (M + 1 - m) / η)]

/-- On `ball x₀ (η / 2)`, uniform bounds `m ≤ φ < M` on `ball x₀ η` and a radius bound `R` on
nearly optimal shifts transfer Lipschitzness of `h` on `ball 0 (R + η + 1)` to `(φ ·).toReal`. -/
private theorem lipschitzOnWith_toReal_cTransformSymm {E : Type*} [NormedAddCommGroup E]
    {h : E → ℝ} {ψ : E → EReal} {y₁ x₀ : E}
    (hy₁ : ψ y₁ ≠ ⊥) (hψ_top : ∀ y, ψ y ≠ ⊤) {η m M R : ℝ} {K : ℝ≥0}
    (hball : ∀ x', dist x' x₀ < η →
      (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ∧
        cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' < (M : EReal))
    (hR : ∀ x₁ ∈ ball x₀ (η / 2), ∀ y : E,
      ψ y ≠ ⊥ → ψ y ≠ ⊤ → h (x₁ - y) - (ψ y).toReal < M + 1 → ‖x₁ - y‖ ≤ R)
    (hK : LipschitzOnWith K h (ball (0 : E) (R + η + 1))) :
    LipschitzOnWith K (fun x ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x).toReal)
      (ball x₀ (η / 2)) := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  have oneside : ∀ x₁ ∈ ball x₀ (η / 2), ∀ x₂ ∈ ball x₀ (η / 2),
      (φ x₂).toReal - (φ x₁).toReal ≤ K * dist x₁ x₂ := by
    intro x₁ hx₁ x₂ hx₂
    have hη : 0 < η := by linarith [mem_ball.1 hx₁, dist_nonneg (x := x₁) (y := x₀)]
    have hx₁_η : dist x₁ x₀ < η := by linarith [mem_ball.1 hx₁]
    have hφx₁_real : φ x₁ = ((φ x₁).toReal : EReal) :=
      (EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ x₁).ne
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hball x₁ hx₁_η).1)).symm
    have hφx₁_le : (φ x₁).toReal ≤ M := EReal.coe_le_coe_iff.1 (hφx₁_real ▸ (hball x₁ hx₁_η).2.le)
    have hx₂_η : dist x₂ x₀ < η := by linarith [mem_ball.1 hx₂]
    have hφx₂_real : φ x₂ = ((φ x₂).toReal : EReal) :=
      (EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ x₂).ne
        (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hball x₂ hx₂_η).1)).symm
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    set ε' := min ε 1
    have hε'_pos : 0 < ε' := by positivity
    have hlt_x₁ : φ x₁ < (((φ x₁).toReal + ε' : ℝ) : EReal) := by
      conv_lhs => rw [hφx₁_real]
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    conv at hlt_x₁ => lhs; rw [show φ x₁ = _ from cTransformSymm_apply _ ψ x₁]
    obtain ⟨y, hy⟩ := iInf_lt_iff.1 hlt_x₁
    dsimp only at hy
    have hy_bot : ψ y ≠ ⊥ := fun hb ↦ by simp [hb] at hy
    rw [← EReal.coe_toReal (hψ_top y) hy_bot, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hy
    have hxy₁ : ‖x₁ - y‖ ≤ R :=
      hR x₁ hx₁ y hy_bot (hψ_top y) (by linarith [min_le_right ε 1])
    have hmem₁ : x₁ - y ∈ ball (0 : E) (R + η + 1) := mem_ball_zero_iff.2 (by linarith)
    have hmem₂ : x₂ - y ∈ ball (0 : E) (R + η + 1) := mem_ball_zero_iff.2 <| by
      have hd₁₂ : ‖x₂ - x₁‖ < η := by
        rw [← dist_eq_norm]
        exact (dist_triangle x₂ x₀ x₁).trans_lt
          (by linarith [dist_comm x₀ x₁ ▸ mem_ball.1 hx₁, mem_ball.1 hx₂])
      calc ‖x₂ - y‖ = ‖(x₂ - x₁) + (x₁ - y)‖ := by congr 1; abel
        _ ≤ ‖x₂ - x₁‖ + ‖x₁ - y‖ := norm_add_le _ _
        _ < R + η + 1 := by linarith
    have hlip := hK.dist_le_mul (x₂ - y) hmem₂ (x₁ - y) hmem₁
    rw [Real.dist_eq, dist_sub_right, dist_comm x₂ x₁] at hlip
    have hφx₂_le : (φ x₂).toReal ≤ h (x₂ - y) - (ψ y).toReal := by
      rw [← EReal.coe_le_coe_iff, EReal.coe_sub, EReal.coe_toReal (hψ_top y) hy_bot, ← hφx₂_real]
      exact cTransformSymm_le _ ψ x₂ y
    linarith [(abs_le.1 hlip).2, min_le_left ε 1]
  refine LipschitzOnWith.of_dist_le_mul fun x₁ hx₁ x₂ hx₂ ↦ ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  exact ⟨dist_comm x₁ x₂ ▸ oneside x₂ hx₂ x₁ hx₁, oneside x₁ hx₁ x₂ hx₂⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ}

/-- **Local Lipschitzness of `cTransformSymm` where locally bounded below**
(Gangbo–McCann, Proposition C.2). On a finite-dimensional real normed space, if `h` is convex and
superlinear, then the real representative of `cTransformSymm` for `h (x - y)` is locally Lipschitz
on every set `s` around whose points `cTransformSymm` has a local real lower bound. -/
theorem locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    {ψ : E → EReal} {s : Set E}
    (hs : ∀ x ∈ s, ∃ m : ℝ, ∀ᶠ x' in 𝓝 x,
      (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x') :
    LocallyLipschitzOn s fun x ↦
      (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x).toReal := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  by_cases hall : ∀ y, ψ y = ⊥
  · intro x₀ _
    have htop : ∀ x, φ x = ⊤ := fun x ↦ eq_top_iff.2 (le_cTransformSymm fun y ↦ by simp [hall y])
    have hzero : (fun x ↦ (φ x).toReal) = fun _ ↦ 0 := funext fun x ↦ by
      rw [htop x, EReal.toReal_top]
    exact ⟨0, univ, univ_mem, hzero ▸ (LipschitzWith.const (0 : ℝ)).lipschitzOnWith⟩
  push Not at hall
  obtain ⟨y₁, hy₁⟩ := hall
  have hc : Continuous h := continuousOn_univ.1 (hh.continuousOn isOpen_univ)
  have husc : UpperSemicontinuous φ :=
    upperSemicontinuous_cTransformSymm_of_continuous
      (fun y ↦ hc.comp (continuous_id.sub continuous_const)) ψ
  intro x₀ hx₀
  obtain ⟨m, hm_ev⟩ := hs x₀ hx₀
  have hψ_top : ∀ y, ψ y ≠ ⊤ := fun y hy ↦ by
    have hbot : φ x₀ = ⊥ := eq_bot_iff.2 (by simpa [hy] using cTransformSymm_le _ ψ x₀ y)
    exact EReal.coe_ne_bot m (eq_bot_iff.2 (hm_ev.self_of_nhds.trans_eq hbot))
  have hx₀_top : φ x₀ < ⊤ := cTransformSymm_lt_top_of_ne_bot _ hy₁ x₀
  set M := (φ x₀).toReal + 1
  have hx₀_lt : φ x₀ < (M : EReal) := by
    rw [← EReal.coe_toReal hx₀_top.ne
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) hm_ev.self_of_nhds)]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hM_ev : ∀ᶠ x' in 𝓝 x₀, φ x' < (M : EReal) := husc x₀ (M : EReal) hx₀_lt
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 (hm_ev.and hM_ev)
  obtain ⟨R, -, hR⟩ := exists_norm_sub_le_of_sub_lt hh h_superlinear hη
    fun x' hx' ↦ (hball (mem_ball.1 hx')).1
  have hbnd : Bornology.IsBounded (h '' ball (0 : E) (R + η + 2)) :=
    ((isCompact_closedBall (0 : E) (R + η + 2)).image hc).isBounded.subset
      (image_mono ball_subset_closedBall)
  obtain ⟨K, hK⟩ :=
    (hh.subset (subset_univ _) (convex_ball _ _)).exists_lipschitzOnWith_of_isBounded
      (r' := R + η + 1) (by linarith) hbnd
  exact ⟨K, ball x₀ (η / 2), nhdsWithin_le_nhds (ball_mem_nhds x₀ (by positivity)),
    lipschitzOnWith_toReal_cTransformSymm hy₁ hψ_top (fun _ hx' ↦ hball hx') hR hK⟩

end LocallyLipschitz

/-! ### Differentiability on the finiteness domain and Gangbo–McCann transport maps -/

section InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ}

/-- **Local Lipschitzness on the interior of the finiteness domain**
(Gangbo–McCann, Proposition C.2). Under convexity, superlinear growth, and the cone condition (H2),
the real representative of `cTransformSymm` for `h (x - y)` is locally Lipschitz on
`interior {x | cTransformSymm c ψ x ≠ ⊥}`. -/
theorem locallyLipschitzOn_interior_toReal_cTransformSymm (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    LocallyLipschitzOn (interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥})
      fun x ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x).toReal :=
  locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le hh h_superlinear fun _ hx ↦
    exists_eventually_le_cTransformSymm_of_mem_interior
      (continuousOn_univ.1 (hh.continuousOn isOpen_univ)) h_cone hx

/-- **Haar-almost everywhere differentiability of `cTransformSymm`** (Gangbo–McCann, Theorem 3.7).
Under convexity, superlinear growth, and the cone condition (H2), at Haar-almost every point where
`cTransformSymm` avoids `⊥`, it avoids `⊥` on a neighbourhood and its real representative is
differentiable. -/
theorem ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm
    [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure]
    (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    ∀ᵐ x ∂ρ, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥ →
      (∀ᶠ x' in 𝓝 x, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ≠ ⊥) ∧
        DifferentiableAt ℝ
          (fun x' ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x').toReal) x := by
  have hc : Continuous h := continuousOn_univ.1 (hh.continuousOn isOpen_univ)
  have hint : ∀ᵐ x ∂ρ, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥ →
      x ∈ interior {x' | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ≠ ⊥} := by
    rw [ae_iff]
    convert addHaar_diff_interior_setOf_cTransformSymm_ne_bot_eq_zero ρ hc h_cone ψ using 2
    ext x
    simp
  have hdiff := (locallyLipschitzOn_interior_toReal_cTransformSymm hh h_superlinear h_cone
    ψ).ae_differentiableAt_of_mem (μ := ρ) isOpen_interior
  filter_upwards [hint, hdiff] with x hx₁ hx₂ hxbot
  exact ⟨mem_interior_iff_mem_nhds.1 (hx₁ hxbot), hx₂ (hx₁ hxbot)⟩

end InteriorRegularity

section TransportMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ρ : Measure E} [ρ.IsAddHaarMeasure]
  {h : E → ℝ} {μ ν : Measure E} {π : Measure (E × E)}

/-- **A plan on the `c`-superdifferential is induced by the Gangbo–McCann map.** Let `π` be a
measure on `E × E` with first marginal `μ ≪ ρ`, where `ρ` is an additive Haar measure, and let `h`
be strictly convex, superlinear, and satisfy the cone condition (H2). If `φ` is `c`-concave for
`c (x, y) = h (x - y)` and `π`-almost every point lies in `cSuperdifferential c φ`, then `φ` avoids
`⊥` near `μ`-almost every point and has differentiable real representative there, and `π` is the
graph plan over `μ` of `x ↦ x - ∇h⋆(∇φ x)`. -/
theorem eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn (hπ : π.fst = μ) (hμ : μ ≪ ρ)
    (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {φ : E → EReal} (hφ : IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ)
    (hcon : ∀ᵐ z ∂π, z ∈ cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ) :
    (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      π = graphPlan (fun x ↦ x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) μ := by
  set c : E × E → ℝ := fun z ↦ h (z.1 - z.2)
  have hc : Continuous h := continuousOn_univ.1 (h_strict.convexOn.continuousOn isOpen_univ)
  have hsuper_cc : Tendsto (fun x ↦ h x / ‖x‖) (cocompact E) atTop :=
    Metric.cobounded_eq_cocompact (α := E) ▸ h_superlinear
  rw [cSuperdifferential_def] at hcon
  have hφ_eq : φ = cTransformSymm c (cTransform c φ) := hφ.cTransformSymm_cTransform.symm
  have hφ_meas : Measurable φ :=
    hφ_eq ▸ measurable_cTransformSymm_of_upperSemicontinuous
      (fun y ↦ (hc.comp (continuous_id.sub continuous_const)).upperSemicontinuous) (cTransform c φ)
  have hdom : ∀ᵐ x ∂μ, φ x ≠ ⊥ := by
    rw [← hπ]
    refine (ae_map_iff measurable_fst.aemeasurable
      (hφ_meas (measurableSet_singleton ⊥).compl)).2 ?_
    filter_upwards [hcon] with z hz using ne_bot_left_of_mem_contactSet (x := z.1) (y := z.2) hz
  have hdiff : ∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧
      DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x := by
    rw [hφ_eq]
    filter_upwards [hμ.ae_le (ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm ρ
      h_strict.convexOn h_superlinear h_cone (cTransform c φ)), hφ_eq ▸ hdom] with x hx hx'
      using hx hx'
  have hconj_top : ∀ q, fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q ≠ ⊤ := fun q ↦ by
    obtain ⟨w, hw⟩ := exists_fenchelConjugate_eq_of_superlinear hc hsuper_cc q
    exact hw ▸ EReal.coe_ne_top _
  have hconj_diff : Differentiable ℝ
      (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal) :=
    (contDiff_fenchelConjugate_toReal_of_superlinear h_strict hsuper_cc).differentiable one_ne_zero
  set T : E → E := fun x ↦ x -
    ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x)
  have hT_meas : Measurable T :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  have hgraph : ∀ᵐ z ∂π, z.2 = T z.1 := by
    rw [← hπ] at hdiff
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hdiff, hcon] with z ⟨hfin, hd⟩ hz
    have heq := gradient_fenchelConjugate_eq_sub_of_mem_contactSet (x := z.1) (y := z.2)
      h_strict.convexOn (Eventually.of_forall fun x' ↦ add_cTransform_le c φ x' z.2) hfin hz hd
      (Eventually.of_forall hconj_top) (hconj_diff _)
    simp only [T, heq, sub_sub_cancel]
  refine ⟨hdiff, ?_⟩
  rw [eq_graphPlan_of_ae_snd_eq hT_meas.aemeasurable hgraph, hπ]

/-- **An optimal finite-cost plan is the graph plan of a Gangbo–McCann map.** Between finite
measures on a finite-dimensional real inner product space with `μ ≪ ρ`, any optimal coupling of
finite cost for a nonnegative strictly convex superlinear displacement cost `h (x - y)` satisfying
the cone condition (H2) is the graph plan of `x ↦ x - ∇h⋆(∇φ x)` for a `c`-concave potential
`φ`. -/
theorem IsOptimalCoupling.exists_eq_graphPlan_of_strictConvexOn [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π μ ν)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    ∃ φ : E → EReal, IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      π = graphPlan (fun x ↦ x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) μ := by
  have hc : Continuous h := continuousOn_univ.1 (h_strict.convexOn.continuousOn isOpen_univ)
  have hc_prod : Continuous fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)) :=
    ENNReal.continuous_ofReal.comp (hc.comp (continuous_fst.sub continuous_snd))
  have hcm : IsCyclicallyMonotone (fun z : E × E ↦ h (z.1 - z.2)) π.support :=
    (isCyclicallyMonotone_ofReal_iff fun z ↦ h_nonneg _).1
      (hopt.isCyclicallyMonotone_support hc_prod hfin)
  obtain ⟨φ, hφ, hsub⟩ := hcm.exists_isCConcave_subset_cSuperdifferential
  have hcon : ∀ᵐ z ∂π, z ∈ cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ := eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn
    hopt.fst_eq hμ h_strict h_superlinear h_cone hφ hcon
  exact ⟨φ, hφ, hdiff, hgraph⟩

/-- **Uniqueness of the optimal plan for a strictly convex displacement cost**
(Gangbo–McCann, Theorem 1.2). Between finite measures on a finite-dimensional real inner product
space with `μ ≪ ρ`, if the optimal cost for `h (x - y)` is finite, any two optimal couplings are
equal. -/
theorem IsOptimalCoupling.unique_of_strictConvexOn [IsFiniteMeasure μ] (hμ : μ ≪ ρ)
    {π' : Measure (E × E)} (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hopt : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π μ ν)
    (hopt' : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) π' μ ν)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    π = π' := by
  have hsum := hopt.add hopt'
  have hfin' : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)))
      (μ + μ) (ν + ν) ≠ ∞ := by
    rw [← hsum.lintegral_eq, lintegral_add_measure, hopt.lintegral_eq, hopt'.lintegral_eq]
    exact ENNReal.add_ne_top.2 ⟨hfin, hfin⟩
  obtain ⟨φ, -, -, hgraph⟩ :=
    hsum.exists_eq_graphPlan_of_strictConvexOn (hμ.add_left hμ) h_nonneg h_strict h_superlinear
      h_cone hfin'
  have hT : Measurable fun x ↦ x -
      ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
        (∇ (fun x' ↦ (φ x').toReal) x) :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  have hae := hgraph ▸ ae_snd_eq_graphPlan (μ := μ + μ) hT.aemeasurable
  rw [eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_right le_rfl) hae),
    eq_graphPlan_of_ae_snd_eq hT.aemeasurable (ae_mono (Measure.le_add_left le_rfl) hae),
    hopt.fst_eq, hopt'.fst_eq]

/-- **Gangbo–McCann's theorem, unconditional potential and map form**
(Gangbo–McCann, Theorem 1.2). For probability measures `μ` and `ν` on a finite-dimensional real
inner product space with `μ ≪ ρ`, and a nonnegative strictly convex superlinear function `h`
satisfying the cone condition (H2), there exists a `c`-concave potential `φ` for
`c (x, y) = h (x - y)` that never takes `⊤`, avoids `⊥` near `μ`-almost every point and has
differentiable real representative there, such that `T x = x - ∇h⋆(∇φ x)` satisfies
`(x, T x) ∈ cSuperdifferential c φ` `μ`-almost everywhere, `(graphPlan T μ).support` is
`c`-cyclically monotone, and `T` is a Kantorovich-optimal transport map from `μ` to `ν`. No
finiteness assumption on `transportCost` is required, and no uniqueness claim is made when the
optimal cost is `∞`. -/
theorem exists_isCConcave_and_isKantorovichOptimalTransportMap_of_strictConvexOn
    [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν] (hμ : μ ≪ ρ)
    (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p) :
    ∃ φ : E → EReal, IsCConcave (fun z : E × E ↦ h (z.1 - z.2)) φ ∧
      (∀ x, φ x ≠ ⊤) ∧
      (∀ᵐ x ∂μ, (∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) ∧ DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x) ∧
      (∀ᵐ x ∂μ, (x, x -
        ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
          (∇ (fun x' ↦ (φ x').toReal) x)) ∈
        cSuperdifferential (fun z : E × E ↦ h (z.1 - z.2)) φ) ∧
      IsCyclicallyMonotone (fun z : E × E ↦ h (z.1 - z.2))
        (graphPlan (fun x ↦ x -
          ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
            (∇ (fun x' ↦ (φ x').toReal) x)) μ).support ∧
      IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν
        (fun x ↦ x -
          ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
            (∇ (fun x' ↦ (φ x').toReal) x)) := by
  set c : E × E → ℝ := fun z ↦ h (z.1 - z.2)
  have hc : Continuous c :=
    (continuousOn_univ.1 (h_strict.convexOn.continuousOn isOpen_univ)).comp
      (continuous_fst.sub continuous_snd)
  obtain ⟨π, hopt, hcm⟩ := exists_isOptimalCoupling_isCyclicallyMonotone_support μ ν hc
    fun z ↦ h_nonneg _
  have : IsProbabilityMeasure π := hopt.toIsCoupling.isProbabilityMeasure
  obtain ⟨φ, hφ, hsub⟩ := hcm.exists_isCConcave_subset_cSuperdifferential
  obtain ⟨z₀, hz₀⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero π)
  have hhz₀ : (z₀.1, z₀.2) ∈ contactSet c φ (cTransform c φ) := by
    simpa only [cSuperdifferential_def] using hsub hz₀
  have hφ_top : ∀ x, φ x ≠ ⊤ := fun x ↦ by
    rw [← hφ.cTransformSymm_cTransform]
    exact (cTransformSymm_lt_top_of_ne_bot c (ne_bot_right_of_mem_contactSet hhz₀) x).ne
  have hcon : ∀ᵐ z ∂π, z ∈ cSuperdifferential c φ := by
    filter_upwards [π.support_mem_ae] with z hz using hsub hz
  obtain ⟨hdiff, hgraph⟩ := eq_graphPlan_of_ae_mem_cSuperdifferential_of_strictConvexOn
    hopt.fst_eq hμ h_strict h_superlinear h_cone hφ hcon
  set T : E → E := fun x ↦ x -
    ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x)
  have hT_meas : Measurable T :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  have hlaw : HasLaw T ν μ :=
    (isCoupling_graphPlan_iff hT_meas.aemeasurable).1 (hgraph ▸ hopt.toIsCoupling)
  have hcon_T : ∀ᵐ x ∂μ, (x, T x) ∈ cSuperdifferential c φ :=
    ae_of_ae_graphPlan hT_meas.aemeasurable (hgraph ▸ hcon)
  refine ⟨φ, hφ, hφ_top, hdiff, hcon_T, hgraph ▸ hcm, ?_⟩
  exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hlaw
    (ENNReal.continuous_ofReal.comp hc).measurable.aemeasurable).2 (hgraph ▸ hopt)

/-- **Gangbo–McCann's theorem for strictly convex costs** (Gangbo–McCann, Theorem 1.2). Let `μ` be
a finite measure and `ν` a measure on a finite-dimensional real inner product space `E`, with `μ`
absolutely continuous with respect to an additive Haar measure `ρ`, and let `h : E → [0, ∞)` be
strictly convex, superlinear, and satisfy the cone condition (H2). If the optimal transport cost of
`c (x, y) = h (x - y)` from `μ` to `ν` is finite (so `μ` and `ν` have the same finite mass), then
there exists a transport map `T : E → E` that:

* is a Kantorovich-optimal transport map from `μ` to `ν`;
* induces the unique optimal coupling: `γ` is optimal if and only if `γ = graphPlan T μ`;
* is the unique Kantorovich-optimal transport map up to `μ`-almost everywhere equality. -/
theorem exists_isKantorovichOptimalTransportMap_of_strictConvexOn [IsFiniteMeasure μ]
    (hμ : μ ≪ ρ) (h_nonneg : ∀ x, 0 ≤ h x) (h_strict : StrictConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∀ r θ : ℝ, 0 < θ → θ < Real.pi → ∃ R : ℝ, ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (hfin : transportCost (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν ≠ ∞) :
    ∃ T : E → E,
      IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν T ∧
      (∀ γ, IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) γ μ ν ↔
        γ = graphPlan T μ) ∧
      ∀ S : E → E,
        IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν S →
          S =ᵐ[μ] T := by
  have hc : Continuous fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)) :=
    ENNReal.continuous_ofReal.comp
      ((continuousOn_univ.1 (h_strict.convexOn.continuousOn isOpen_univ)).comp
        (continuous_fst.sub continuous_snd))
  obtain ⟨π, hπ⟩ := (exists_isOptimalCoupling_iff hc.lowerSemicontinuous).2
    (exists_isCoupling_of_transportCost_ne_top hfin).choose_spec.measure_univ_eq
  obtain ⟨φ, -, -, hgraph⟩ :=
    hπ.exists_eq_graphPlan_of_strictConvexOn hμ h_nonneg h_strict h_superlinear h_cone hfin
  set T : E → E := fun x ↦ x -
    ∇ (fun q ↦ (fenchelConjugate (innerₗ E) (fun z ↦ (h z : EReal)) q).toReal)
      (∇ (fun x' ↦ (φ x').toReal) x)
  have hT_meas : Measurable T :=
    measurable_id.sub ((measurable_gradient _).comp (measurable_gradient _))
  have hlaw : HasLaw T ν μ :=
    (isCoupling_graphPlan_iff hT_meas.aemeasurable).1 (hgraph ▸ hπ.toIsCoupling)
  have hiff : ∀ S : E → E, HasLaw S ν μ →
      (IsKantorovichOptimalTransportMap (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2))) μ ν S ↔
        IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)))
          (graphPlan S μ) μ ν) := fun S hS ↦
    isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hS hc.measurable.aemeasurable
  have hopt_T : IsOptimalCoupling (fun z : E × E ↦ ENNReal.ofReal (h (z.1 - z.2)))
      (graphPlan T μ) μ ν := hgraph ▸ hπ
  refine ⟨T, (hiff T hlaw).2 hopt_T, fun γ ↦ ⟨fun hγ ↦ hγ.unique_of_strictConvexOn hμ h_nonneg
    h_strict h_superlinear h_cone hopt_T hfin, fun hγ ↦ hγ ▸ hopt_T⟩, fun S hS ↦ ?_⟩
  exact (graphPlan_eq_graphPlan_iff hS.toHasLaw.aemeasurable hT_meas.aemeasurable).1
    (((hiff S hS.toHasLaw).1 hS).unique_of_strictConvexOn hμ h_nonneg h_strict h_superlinear
      h_cone hopt_T hfin)

end TransportMap

end TauCeti
