/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.OptimalTransport.CTransform.Basic
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import TauCeti.Analysis.Calculus.Rademacher
import TauCeti.MeasureTheory.Covering.Besicovitch
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Regularity of the infimal `c`-transform for displacement costs

For a displacement cost `c (x, y) = h (x - y)` on a finite-dimensional real inner product space `E`,
extracting transport maps from `c`-concave potentials requires avoiding `⊥` locally and
almost-everywhere differentiability of `φ = cTransformSymm c ψ`. Unlike the quadratic cost
`h z = ‖z‖ ^ 2 / 2` (where `x ↦ ‖x‖ ^ 2 / 2 - φ x` is convex), general displacement costs need two
geometric regularity steps:

1. **Full-measure interior of `{x | φ x ≠ ⊥}`** (Gangbo–McCann, Proposition 3.3). Even for
   smooth strictly convex superlinear `h` on `ℝ²`, a `c`-concave potential `φ` can take `-∞` on a
   dense set while remaining finite on a set of positive Lebesgue measure unless the level sets of
   `h` satisfy the cone condition (H2) at infinity: for some height `r > 0`, aperture `θ ∈ (0, π)`,
   and radius `R`, every distant vertex `p` (`R < ‖p‖`) admits `z ≠ 0` such that `h ≤ h p` on the
   truncated cone `{x | ‖x - p‖ ‖z‖ cos (θ / 2) ≤ ⟪z, x - p⟫ ≤ r ‖z‖}`. Under continuity of `h` and
   (H2), a finite ball cover of the unit sphere (`IsCompact.finite_cover_balls`) forces any point
   where `φ = ⊥` to propagate `φ = ⊥` to a ball of comparable radius nearby, so
   `{x | φ x ≠ ⊥} \ interior {x | φ x ≠ ⊥}` (where `{x | φ x ≠ ⊥}` is the finiteness domain whenever
   `ψ ≢ ⊥`) has zero Haar measure by Besicovitch/Lebesgue density
   (`NullMeasurableSet.ae_eq_setOf_tendsto_measure_inter_div`,
   `TauCeti.addHaar_sdiff_interior_setOf_cTransformSymm_ne_bot_eq_zero`), and `φ` is locally bounded
   below on `interior {x | φ x ≠ ⊥}`
   (`TauCeti.exists_eventually_le_cTransformSymm_of_mem_interior`).
2. **Local Lipschitzness and Rademacher differentiability** (Gangbo–McCann, Proposition C.2 and
   Theorem 3.7). Under convexity of `h` and superlinear growth `h z / ‖z‖ → ∞`, local lower bounds
   and upper semicontinuity of `φ` confine nearly optimal target points `y` for `x₁` near `x₀` to a
   bounded ball, where `h` is Lipschitz (`ConvexOn.locallyLipschitz`,
   `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`); hence
   `x ↦ (φ x).toReal` is locally Lipschitz wherever `φ` is locally bounded below
   (`TauCeti.locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le`). Combined with step 1 under
   the cone condition (H2), `φ` avoids `⊥` locally and `x ↦ (φ x).toReal` is differentiable
   Haar-almost everywhere on `{x | φ x ≠ ⊥}` by Rademacher's theorem
   (`LocallyLipschitzOn.ae_differentiableAt_of_mem`,
   `TauCeti.ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm`).

## Main statements

* `TauCeti.exists_eventually_le_cTransformSymm_of_mem_interior` — under continuity of `h` and the
  cone condition, `cTransformSymm` is locally bounded below on `interior {x | φ x ≠ ⊥}`;
* `TauCeti.addHaar_sdiff_interior_setOf_cTransformSymm_ne_bot_eq_zero` — under continuity of `h` and
  the cone condition, `{x | φ x ≠ ⊥} \ interior {x | φ x ≠ ⊥}` is Haar-null;
* `TauCeti.locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le` and
  `TauCeti.locallyLipschitzOn_interior_toReal_cTransformSymm` — local Lipschitzness of the real
  representative of `cTransformSymm` for convex superlinear `h` where locally bounded below, and on
  `interior {x | φ x ≠ ⊥}` under the cone condition (H2);
* `TauCeti.ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm` — for convex superlinear
  `h` satisfying the cone condition (H2), avoiding `⊥` locally and differentiability of the real
  representative Haar-almost everywhere on `{x | φ x ≠ ⊥}` (the finiteness domain when `ψ ≢ ⊥`).

## References

* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113--161, Proposition 3.3, Theorem 3.7, and Proposition C.2.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 10.28.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace TauCeti

/-! ### Cone condition and regularity of `{x | cTransformSymm c ψ x ≠ ⊥}` -/

section ConeRegularity

private theorem cos_half_bounds {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    0 < Real.cos (θ / 2) ∧ Real.cos (θ / 2) < 1 := by
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩, ?_⟩
  simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
    (by linarith : θ / 2 ≤ Real.pi) (by positivity : 0 < θ / 2)

/-- For `θ ∈ (0, π)` and `κ = (1 - cos (θ / 2)) / 8`, any point of
`closedBall (x₀ + (δ / 2) • u) (κ * δ)` with `u` on the unit sphere within `κ` of `‖z‖⁻¹ • z` and
`0 < δ ≤ r` lies in the truncated cone of height `r` and aperture `θ` in direction `z`. -/
private theorem mem_truncatedCone_of_mem_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {z u x₀ x p : E} {r θ δ : ℝ} (hz : z ≠ 0)
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (hu : u ∈ sphere (0 : E) 1)
    (hzu : ‖(‖z‖⁻¹ : ℝ) • z - u‖ < (1 - Real.cos (θ / 2)) / 8)
    (hδ₀ : 0 < δ) (hδr : δ ≤ r)
    (hx : x ∈ closedBall (x₀ + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ)) :
    ‖(x - x₀ + p) - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, (x - x₀ + p) - p⟫ ∧
      ⟪z, (x - x₀ + p) - p⟫ ≤ r * ‖z‖ := by
  obtain ⟨hc₀, hc₁⟩ := cos_half_bounds hθ₀ hθπ
  set κ := (1 - Real.cos (θ / 2)) / 8 with hκ_def
  have hκ₀ : 0 < κ := by linarith
  have _ : κ < 1 / 8 := by linarith
  have hnorm_u : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set e := x - (x₀ + (δ / 2) • u)
  have he : ‖e‖ ≤ κ * δ := mem_closedBall_iff_norm.1 hx
  have hdiff : (x - x₀ + p) - p = (δ / 2) • u + e := by simp only [e]; abel
  have hnorm_diff : ‖(x - x₀ + p) - p‖ ≤ (1 / 2 + κ) * δ := by
    rw [hdiff]
    calc ‖(δ / 2) • u + e‖ ≤ ‖(δ / 2) • u‖ + ‖e‖ := norm_add_le _ _
      _ = δ / 2 + ‖e‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hnorm_u, mul_one]
      _ ≤ (1 / 2 + κ) * δ := by linarith
  have hnorm_le_δ : ‖(x - x₀ + p) - p‖ ≤ δ := hnorm_diff.trans (by nlinarith)
  refine ⟨?_, ?_⟩
  · set w := (‖z‖⁻¹ : ℝ) • z
    have h1 : ⟪u, e⟫ ≥ -(κ * δ) := by
      have := abs_real_inner_le_norm u e
      rw [hnorm_u, one_mul] at this
      linarith [(abs_le.1 this).1]
    have h2 : ⟪w - u, (x - x₀ + p) - p⟫ ≥ -(κ * δ) := by
      have := abs_real_inner_le_norm (w - u) ((x - x₀ + p) - p)
      linarith [(abs_le.1 this).1, mul_le_mul hzu.le hnorm_le_δ (norm_nonneg _) hκ₀.le]
    have h3 : (1 / 2 + κ) * δ * Real.cos (θ / 2) ≤ ⟪w, (x - x₀ + p) - p⟫ := by
      have hκc : ((1 / 2 + κ) * Real.cos (θ / 2)) * δ ≤ (1 / 2 - 2 * κ) * δ :=
        mul_le_mul_of_nonneg_right (by nlinarith) hδ₀.le
      have hwu : w = u + (w - u) := by abel
      have hu_diff : ⟪u, (x - x₀ + p) - p⟫ = δ / 2 + ⟪u, e⟫ := by
        rw [hdiff, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hnorm_u]
        ring
      rw [hwu, inner_add_left]
      linarith
    have hz_eq : ⟪z, (x - x₀ + p) - p⟫ = ‖z‖ * ⟪w, (x - x₀ + p) - p⟫ := by
      have : z = ‖z‖ • w := by simp [w, smul_smul, hz_pos.ne']
      conv_lhs => rw [this]
      rw [inner_smul_left, RCLike.conj_to_real]
    calc ‖(x - x₀ + p) - p‖ * ‖z‖ * Real.cos (θ / 2)
        = ‖z‖ * (‖(x - x₀ + p) - p‖ * Real.cos (θ / 2)) := by ring
      _ ≤ ‖z‖ * ((1 / 2 + κ) * δ * Real.cos (θ / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm_diff hc₀.le) hz_pos.le
      _ ≤ ‖z‖ * ⟪w, (x - x₀ + p) - p⟫ := mul_le_mul_of_nonneg_left h3 hz_pos.le
      _ = ⟪z, (x - x₀ + p) - p⟫ := hz_eq.symm
  · calc ⟪z, (x - x₀ + p) - p⟫ ≤ ‖z‖ * ‖(x - x₀ + p) - p‖ := real_inner_le_norm _ _
      _ ≤ ‖z‖ * r := mul_le_mul_of_nonneg_left (hnorm_le_δ.trans hδr) hz_pos.le
      _ = r * ‖z‖ := by ring

/-- On compact balls around `x₀`, continuity of `h` bounds `(h (x - y) : EReal) - ψ y` from below
whenever `cTransformSymm` avoids `⊥` at a reference point `x_ref` within distance `1` of `x₀`. -/
private theorem le_sub_of_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {h : E → ℝ} (hc : Continuous h) {ψ : E → EReal} {x₀ x_ref : E}
    {R : ℝ} (hR : 0 ≤ R) (href_dist : ‖x_ref - x₀‖ ≤ 1)
    (href_bot : cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x_ref ≠ ⊥) :
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
  have hψy : ψ y = ((ψ y).toReal : EReal) :=
    (EReal.coe_toReal (ne_top_of_cTransformSymm_ne_bot href_bot y) hybot).symm
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ}

/-- Cone-net propagation lemma: under the cone condition with height `r` and aperture `θ ∈ (0, π)`,
there exist `R ≥ 0` and a finite subset `F` of the unit sphere such that for every distant `p`
(`R < ‖p‖`), every center `x₀`, and every `δ ∈ (0, r]`, some `u ∈ F` satisfies
`h (x - x₀ + p) ≤ h p` throughout `closedBall (x₀ + (δ / 2) • u) ((1 - cos (θ / 2)) / 8 * δ)`. -/
private theorem exists_net_forall_closedBall_le [Nontrivial E] {r θ R₀ : ℝ}
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hR₀ : ∀ p, R₀ < ‖p‖ → ∃ z, z ≠ 0 ∧ ∀ x,
      ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ → ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p) :
    ∃ (R : ℝ) (F : Finset E), 0 ≤ R ∧ F.Nonempty ∧ (↑F : Set E) ⊆ sphere (0 : E) 1 ∧
      ∀ p, R < ‖p‖ → ∀ x₀ : E, ∀ δ : ℝ, 0 < δ → δ ≤ r →
        ∃ u ∈ F, ∀ x ∈ closedBall (x₀ + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ),
          h (x - x₀ + p) ≤ h p := by
  have hκ : 0 < (1 - Real.cos (θ / 2)) / 8 := by linarith [(cos_half_bounds hθ₀ hθπ).2]
  obtain ⟨t, htsub, htfin, htcov⟩ := (isCompact_sphere (0 : E) 1).finite_cover_balls hκ
  have htne : htfin.toFinset.Nonempty := by
    obtain ⟨w, hw⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0)).2 zero_le_one
    obtain ⟨u, hut, -⟩ := mem_iUnion₂.1 (htcov hw)
    exact ⟨u, htfin.mem_toFinset.2 hut⟩
  refine ⟨max R₀ 0, htfin.toFinset, le_max_right _ _, htne, by simpa using htsub,
    fun p hp x₀ δ hδ₀ hδr ↦ ?_⟩
  obtain ⟨z, hz, hcone_z⟩ := hR₀ p ((le_max_left R₀ 0).trans_lt hp)
  obtain ⟨u, hut, hzu⟩ := mem_iUnion₂.1
    (htcov (mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ) hz)))
  refine ⟨u, htfin.mem_toFinset.2 hut, fun x hx ↦ ?_⟩
  obtain ⟨hc₁, hc₂⟩ := mem_truncatedCone_of_mem_closedBall hz hθ₀ hθπ (htsub hut)
    (mem_ball_iff_norm.1 hzu) hδ₀ hδr hx
  exact hcone_z (x - x₀ + p) hc₁ hc₂

/-- Given witnesses `g u` in `closedBall (x₀ + (δ / 2) • u) ((1 - cos (θ / 2)) / 8 * δ)` where
`cTransformSymm` avoids `⊥`, continuity of `h` and the cone condition yield a uniform real lower
bound on `cTransformSymm` at every `x ∈ closedBall x₀ ((1 - cos (θ / 2)) / 8 * δ)` whose shifted
balls still contain `g u`. -/
private theorem exists_le_cTransformSymm_of_forall_sphere [Nontrivial E]
    (hc : Continuous h) {r θ R₀ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hR₀ : ∀ p, R₀ < ‖p‖ → ∃ z, z ≠ 0 ∧ ∀ x,
      ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ → ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {ψ : E → EReal} {x₀ : E} {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) (hδr : δ ≤ r) {g : E → E}
    (hg_mem : ∀ u ∈ sphere (0 : E) 1,
      g u ∈ closedBall (x₀ + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ))
    (hg_bot : ∀ u ∈ sphere (0 : E) 1,
      cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ (g u) ≠ ⊥) :
    ∃ m : ℝ, ∀ x ∈ closedBall x₀ ((1 - Real.cos (θ / 2)) / 8 * δ),
      (∀ u ∈ sphere (0 : E) 1,
        g u ∈ closedBall (x + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ)) →
      (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  have hκ₁ : (1 - Real.cos (θ / 2)) / 8 < 1 / 8 := by linarith [(cos_half_bounds hθ₀ hθπ).1]
  by_cases hall : ∀ y, ψ y = ⊥
  · exact ⟨0, fun _ _ _ ↦ le_cTransformSymm fun y ↦ by simp [hall y]⟩
  obtain ⟨y₁, hy₁⟩ : ∃ y, ψ y ≠ ⊥ := by simpa using hall
  obtain ⟨R, F, hR_nonneg, ⟨u₀, hu₀⟩, hFsub, hnet⟩ := exists_net_forall_closedBall_le hθ₀ hθπ hR₀
  have hgu₀_dist : ‖g u₀ - x₀‖ ≤ 1 := by
    have hmem := mem_closedBall_iff_norm.1 (hg_mem u₀ (hFsub hu₀))
    have hu₀_norm : ‖(δ / 2) • u₀‖ = δ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        mem_sphere_zero_iff_norm.1 (hFsub hu₀), mul_one]
    calc ‖g u₀ - x₀‖ = ‖(g u₀ - (x₀ + (δ / 2) • u₀)) + (δ / 2) • u₀‖ := by congr 1; abel
      _ ≤ ‖g u₀ - (x₀ + (δ / 2) • u₀)‖ + ‖(δ / 2) • u₀‖ := norm_add_le _ _
      _ ≤ 1 := by nlinarith
  obtain ⟨m₀, hm₀⟩ :=
    le_sub_of_norm_sub_le hc (by positivity : 0 ≤ R + 1) hgu₀_dist (hg_bot u₀ (hFsub hu₀))
  set m₁ := F.inf' ⟨u₀, hu₀⟩ fun u ↦ (φ (g u)).toReal
  refine ⟨min m₀ m₁, fun x hx hg_x ↦ le_cTransformSymm fun y ↦ ?_⟩
  have hx_dist : ‖x - x₀‖ ≤ (1 - Real.cos (θ / 2)) / 8 * δ := mem_closedBall_iff_norm.1 hx
  by_cases hyR : ‖x₀ - y‖ ≤ R + 1
  · exact (EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans
      (hm₀ x y (hx_dist.trans (by nlinarith)) hyR)
  push Not at hyR
  have hp : R < ‖x - y‖ := by
    have htri : ‖x₀ - y‖ - ‖x₀ - x‖ ≤ ‖x - y‖ := by
      simpa only [sub_sub_sub_cancel_left] using norm_sub_norm_le (x₀ - y) (x₀ - x)
    rw [norm_sub_rev x₀ x] at htri
    nlinarith
  obtain ⟨u, huF, hu_le⟩ := hnet (x - y) hp x δ hδ₀ hδr
  have hguy : h (g u - y) ≤ h (x - y) :=
    by simpa only [sub_add_sub_cancel] using hu_le (g u) (hg_x u (hFsub huF))
  calc ((min m₀ m₁ : ℝ) : EReal) ≤ (m₁ : EReal) := EReal.coe_le_coe_iff.2 (min_le_right _ _)
    _ ≤ ((φ (g u)).toReal : EReal) := EReal.coe_le_coe_iff.2 (Finset.inf'_le _ huF)
    _ = φ (g u) := EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ (g u)).ne
        (hg_bot u (hFsub huF))
    _ ≤ (h (g u - y) : EReal) - ψ y := cTransformSymm_le _ ψ (g u) y
    _ ≤ (h (x - y) : EReal) - ψ y := EReal.sub_le_sub (EReal.coe_le_coe_iff.2 hguy) le_rfl

/-- **Local lower bound on `interior {x | cTransformSymm c ψ x ≠ ⊥}`**
(Gangbo–McCann, Proposition 3.3). If `h` is continuous and satisfies the cone condition (H2), then
`cTransformSymm` for the cost `h (x - y)` is locally bounded below by a real constant around every
point of `interior {x | cTransformSymm c ψ x ≠ ⊥}` (the interior of the finiteness domain when
`ψ ≢ ⊥`). -/
theorem exists_eventually_le_cTransformSymm_of_mem_interior (hc : Continuous h)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {ψ : E → EReal} {x₀ : E}
    (hx₀ : x₀ ∈ interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}) :
    ∃ m : ℝ, ∀ᶠ x in 𝓝 x₀, (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · by_cases hall : ∀ y, ψ y = ⊥
    · exact ⟨0, Eventually.of_forall fun _ ↦ le_cTransformSymm fun y ↦ by simp [hall y]⟩
    obtain ⟨y₁, hy₁⟩ : ∃ y, ψ y ≠ ⊥ := by simpa using hall
    refine ⟨(φ x₀).toReal, Eventually.of_forall fun x ↦ ?_⟩
    rw [Subsingleton.elim x x₀,
      EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ x₀).ne (interior_subset hx₀)]
  obtain ⟨r, θ, R₀, hr, hθ₀, hθπ, hR₀⟩ := h_cone
  have hκ : 0 < (1 - Real.cos (θ / 2)) / 8 := by linarith [(cos_half_bounds hθ₀ hθπ).2]
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hx₀)
  set δ := min (δ₀ / 2) (min r 1)
  have hδ_pos : 0 < δ := by positivity
  have hcb_sub : closedBall x₀ δ ⊆ {x | φ x ≠ ⊥} :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hδ₀_sub
  obtain ⟨m, hm⟩ := exists_le_cTransformSymm_of_forall_sphere hc hθ₀ hθπ hR₀ hδ_pos
    ((min_le_right _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_left _ _))
    (g := fun u ↦ x₀ + (δ / 2) • u) (fun _ _ ↦ mem_closedBall_self (by positivity))
    fun u hu ↦ hcb_sub <| mem_closedBall_iff_norm.2 <| by
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < δ / 2), mem_sphere_zero_iff_norm.1 hu, mul_one]
      linarith
  refine ⟨m, eventually_of_mem
    (closedBall_mem_nhds x₀ (by positivity : 0 < (1 - Real.cos (θ / 2)) / 8 * δ))
    fun x hx ↦ hm x hx fun u _ ↦ mem_closedBall_iff_norm.2 ?_⟩
  simpa only [add_sub_add_right_eq_sub, norm_sub_rev] using mem_closedBall_iff_norm.1 hx

/-- If `cTransformSymm` takes `⊥` at `x₁`, then under continuity of `h` and the cone condition, it
takes `⊥` on an entire ball `closedBall (x₁ + (δ / 2) • u) ((1 - cos (θ / 2)) / 8 * δ)` for some
unit vector `u`. -/
private theorem exists_closedBall_subset_setOf_cTransformSymm_eq_bot [Nontrivial E]
    (hc : Continuous h) {r θ R₀ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi)
    (hR₀ : ∀ p, R₀ < ‖p‖ → ∃ z, z ≠ 0 ∧ ∀ x,
      ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ → ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    {ψ : E → EReal} {x₁ : E}
    (hx₁ : cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x₁ = ⊥) {δ : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1) (hδr : δ ≤ r) :
    ∃ u ∈ sphere (0 : E) 1,
      closedBall (x₁ + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ) ⊆
        {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x = ⊥} := by
  have hκ : 0 < (1 - Real.cos (θ / 2)) / 8 := by linarith [(cos_half_bounds hθ₀ hθπ).2]
  by_contra! hcon
  have hcon' : ∀ u, ∃ x, u ∈ sphere (0 : E) 1 →
      x ∈ closedBall (x₁ + (δ / 2) • u) ((1 - Real.cos (θ / 2)) / 8 * δ) ∧
        cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥ := fun u ↦ by
    by_cases hu : u ∈ sphere (0 : E) 1
    · obtain ⟨x, hx_cb, hx_bot⟩ := not_subset.1 (hcon u hu)
      exact ⟨x, fun _ ↦ ⟨hx_cb, hx_bot⟩⟩
    · exact ⟨x₁, fun h ↦ (hu h).elim⟩
  choose g hg using hcon'
  obtain ⟨m, hm⟩ := exists_le_cTransformSymm_of_forall_sphere hc hθ₀ hθπ hR₀ hδ₀ hδ₁ hδr
    (fun u hu ↦ (hg u hu).1) (fun u hu ↦ (hg u hu).2)
  have hle := hm x₁ (mem_closedBall_self (by positivity)) fun u hu ↦ (hg u hu).1
  exact EReal.coe_ne_bot m (eq_bot_iff.2 (hle.trans_eq hx₁))

/-- **The set `{x | cTransformSymm c ψ x ≠ ⊥}` equals its interior up to Haar measure zero**
(Gangbo–McCann, Proposition 3.3). Under continuity of `h` and the cone condition (H2), the
non-interior points `{x | cTransformSymm c ψ x ≠ ⊥} \ interior {x | cTransformSymm c ψ x ≠ ⊥}`
(the boundary points belonging to the finiteness domain when `ψ ≢ ⊥`) have zero additive Haar
measure. -/
theorem addHaar_sdiff_interior_setOf_cTransformSymm_ne_bot_eq_zero
    [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure] (hc : Continuous h)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    ρ ({x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥} \
      interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}) = 0 := by
  set S := {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥}
  rcases subsingleton_or_nontrivial E with hsub | hnon
  · have : DiscreteTopology E := Finite.instDiscreteTopology
    rw [(isOpen_discrete S).interior_eq, Set.sdiff_self, measure_empty]
  obtain ⟨r, θ, R₀, hr, hθ₀, hθπ, hR₀⟩ := h_cone
  obtain ⟨hc₀, hc₁⟩ := cos_half_bounds hθ₀ hθπ
  set κ : ℝ := (1 - Real.cos (θ / 2)) / 8 with hκ_def
  have hκ₀ : 0 < κ := by linarith
  have _ : κ < 1 / 8 := by linarith
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
  have hball_pos := eventually_measure_closedBall_ne_zero_ne_top ρ x₀
  have hcompl := (hS_meas.tendsto_measure_compl_inter_div_iff hball_pos).2 hx₀
  set α : ℝ≥0∞ := ENNReal.ofReal (κ ^ Module.finrank ℝ E)
  have hα : 0 < α := ENNReal.ofReal_pos.2 (by positivity)
  have hev := (hcompl.eventually (gt_mem_nhds hα)).and
    (Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < min r 1))
  obtain ⟨δ, ⟨hδ_lt, hδ₀, hδ_lt_min⟩, hρ0, hρtop⟩ := (hev.and hball_pos).exists
  have hnot_sub : ¬ ball x₀ (δ / 4) ⊆ S := fun hsub ↦
    hx₀_int (mem_interior.2 ⟨ball x₀ (δ / 4), hsub, isOpen_ball, mem_ball_self (by positivity)⟩)
  obtain ⟨x₁, hx₁_ball, hx₁_notS⟩ := not_subset.1 hnot_sub
  obtain ⟨u, hu_sph, hu_sub⟩ := exists_closedBall_subset_setOf_cTransformSymm_eq_bot hc hθ₀ hθπ hR₀
    (not_not.1 hx₁_notS) hδ₀ (hδ_lt_min.le.trans (min_le_right _ _))
    (hδ_lt_min.le.trans (min_le_left _ _))
  have hcb_sub : closedBall (x₁ + (δ / 2) • u) (κ * δ) ⊆ Sᶜ ∩ closedBall x₀ δ :=
    subset_inter
      (fun x hx hxS ↦ hxS (hu_sub hx))
      (closedBall_subset_closedBall' <| by
        have hd : dist (x₁ + (δ / 2) • u) x₁ = δ / 2 := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by positivity), mem_sphere_zero_iff_norm.1 hu_sph, mul_one]
        nlinarith [dist_triangle (x₁ + (δ / 2) • u) x₁ x₀, mem_ball.1 hx₁_ball])
  have hmeas_eq : ρ (closedBall (x₁ + (δ / 2) • u) (κ * δ)) = α * ρ (closedBall x₀ δ) := by
    rw [Measure.addHaar_closedBall_mul_of_pos ρ _ hκ₀ δ,
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
      ψ y ≠ ⊥ → h (x₁ - y) - (ψ y).toReal < M + 1 → ‖x₁ - y‖ ≤ R := by
  set C := max 0 (2 * (M + 1 - m) / η) + |h 0| / η + 1
  obtain ⟨R₀, -, hR₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1
    (h_superlinear.eventually_ge_atTop C)
  refine ⟨max R₀ η + 1, by positivity, fun x₁ hx₁ y hy_bot hlt ↦ ?_⟩
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
  have hx'_bot : cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hm x' hx'_mem)
  have hm_x' : (m : EReal) ≤ (h (x' - y) : EReal) - ((ψ y).toReal : EReal) := by
    rw [EReal.coe_toReal (ne_top_of_cTransformSymm_ne_bot hx'_bot y) hy_bot]
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
    rwa [hident, div_mul_eq_mul_div] at hmul
  have hdiv₂ : h 0 / ‖v‖ ≤ |h 0| / η :=
    (div_le_div_of_nonneg_right (le_abs_self _) hv_pos.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hη hv_η.le)
  have hsum : h v / ‖v‖ = (h v - h 0) / ‖v‖ + h 0 / ‖v‖ := by ring
  linarith [le_max_right 0 (2 * (M + 1 - m) / η)]

/-- On `ball x₀ (η / 2)`, uniform bounds `m ≤ φ < M` on `ball x₀ η` and a radius bound `R` on
nearly optimal shifts transfer Lipschitzness of `h` on `ball 0 (R + η + 1)` to `(φ ·).toReal`. -/
private theorem lipschitzOnWith_toReal_cTransformSymm {E : Type*} [NormedAddCommGroup E]
    {h : E → ℝ} {ψ : E → EReal} {y₁ x₀ : E}
    (hy₁ : ψ y₁ ≠ ⊥) {η m M R : ℝ} {K : ℝ≥0}
    (hball : ∀ x', dist x' x₀ < η →
      (m : EReal) ≤ cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ∧
        cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' < (M : EReal))
    (hR : ∀ x₁ ∈ ball x₀ (η / 2), ∀ y : E,
      ψ y ≠ ⊥ → h (x₁ - y) - (ψ y).toReal < M + 1 → ‖x₁ - y‖ ≤ R)
    (hK : LipschitzOnWith K h (ball (0 : E) (R + η + 1))) :
    LipschitzOnWith K (fun x ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x).toReal)
      (ball x₀ (η / 2)) := by
  set φ := cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ with hφ
  have oneside : ∀ x₁ ∈ ball x₀ (η / 2), ∀ x₂ ∈ ball x₀ (η / 2),
      (φ x₂).toReal - (φ x₁).toReal ≤ K * dist x₁ x₂ := by
    intro x₁ hx₁ x₂ hx₂
    have hη : 0 < η := by linarith [mem_ball.1 hx₁, dist_nonneg (x := x₁) (y := x₀)]
    have hx₁_η : dist x₁ x₀ < η := by linarith [mem_ball.1 hx₁]
    have hx₁_bot : φ x₁ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (hball x₁ hx₁_η).1
    have hφx₁_real : φ x₁ = ((φ x₁).toReal : EReal) :=
      (EReal.coe_toReal (cTransformSymm_lt_top_of_ne_bot _ hy₁ x₁).ne hx₁_bot).symm
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
    rw [hφ, cTransformSymm_lt_iff] at hlt_x₁
    obtain ⟨y, hy⟩ := hlt_x₁
    have hy_bot : ψ y ≠ ⊥ := fun hb ↦ by simp [hb] at hy
    have hy_top : ψ y ≠ ⊤ := ne_top_of_cTransformSymm_ne_bot hx₁_bot y
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_sub, EReal.coe_lt_coe_iff] at hy
    have hxy₁ : ‖x₁ - y‖ ≤ R := hR x₁ hx₁ y hy_bot (by linarith [min_le_right ε 1])
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
      rw [← EReal.coe_le_coe_iff, EReal.coe_sub, EReal.coe_toReal hy_top hy_bot, ← hφx₂_real]
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
  have hc : Continuous h := hh.locallyLipschitz.continuous
  have husc : UpperSemicontinuous φ :=
    upperSemicontinuous_cTransformSymm_of_continuous
      (fun y ↦ hc.comp (continuous_id.sub continuous_const)) ψ
  intro x₀ hx₀
  obtain ⟨m, hm_ev⟩ := hs x₀ hx₀
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
  obtain ⟨K, hK⟩ := hh.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) (R + η + 1))
  exact ⟨K, ball x₀ (η / 2), nhdsWithin_le_nhds (ball_mem_nhds x₀ (by positivity)),
    lipschitzOnWith_toReal_cTransformSymm hy₁ (fun _ hx' ↦ hball hx') hR
      (hK.mono ball_subset_closedBall)⟩

end LocallyLipschitz

section InteriorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {h : E → ℝ}

/-- **Local Lipschitzness on `interior {x | cTransformSymm c ψ x ≠ ⊥}`**
(Gangbo–McCann, Proposition C.2). Under convexity, superlinear growth, and the cone condition (H2),
the real representative of `cTransformSymm` for `h (x - y)` is locally Lipschitz on
`interior {x | cTransformSymm c ψ x ≠ ⊥}` (the interior of the finiteness domain when `ψ ≢ ⊥`). -/
theorem locallyLipschitzOn_interior_toReal_cTransformSymm (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    LocallyLipschitzOn (interior {x | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥})
      fun x ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x).toReal :=
  locallyLipschitzOn_toReal_cTransformSymm_of_eventually_le hh h_superlinear fun _ hx ↦
    exists_eventually_le_cTransformSymm_of_mem_interior hh.locallyLipschitz.continuous h_cone hx

/-- **Haar-almost everywhere differentiability of `cTransformSymm`** (Gangbo–McCann, Theorem 3.7).
Under convexity, superlinear growth, and the cone condition (H2), at Haar-almost every point where
`cTransformSymm` avoids `⊥`, it avoids `⊥` on a neighbourhood and its real representative is
differentiable. -/
theorem ae_eventually_ne_bot_and_differentiableAt_toReal_cTransformSymm
    [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure]
    (hh : ConvexOn ℝ univ h)
    (h_superlinear : Tendsto (fun x ↦ h x / ‖x‖) (Bornology.cobounded E) atTop)
    (h_cone : ∃ r θ R : ℝ, 0 < r ∧ 0 < θ ∧ θ < Real.pi ∧ ∀ p, R < ‖p‖ →
      ∃ z, z ≠ 0 ∧ ∀ x, ‖x - p‖ * ‖z‖ * Real.cos (θ / 2) ≤ ⟪z, x - p⟫ →
        ⟪z, x - p⟫ ≤ r * ‖z‖ → h x ≤ h p)
    (ψ : E → EReal) :
    ∀ᵐ x ∂ρ, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥ →
      (∀ᶠ x' in 𝓝 x, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ≠ ⊥) ∧
        DifferentiableAt ℝ
          (fun x' ↦ (cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x').toReal) x := by
  have hc : Continuous h := hh.locallyLipschitz.continuous
  have hint : ∀ᵐ x ∂ρ, cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x ≠ ⊥ →
      x ∈ interior {x' | cTransformSymm (fun z : E × E ↦ h (z.1 - z.2)) ψ x' ≠ ⊥} := by
    rw [ae_iff]
    convert addHaar_sdiff_interior_setOf_cTransformSymm_ne_bot_eq_zero ρ hc h_cone ψ using 2
    ext x
    simp
  have hdiff := (locallyLipschitzOn_interior_toReal_cTransformSymm hh h_superlinear h_cone
    ψ).ae_differentiableAt_of_mem (μ := ρ) isOpen_interior
  filter_upwards [hint, hdiff] with x hx₁ hx₂ hxbot
  exact ⟨mem_interior_iff_mem_nhds.1 (hx₁ hxbot), hx₂ (hx₁ hxbot)⟩

end InteriorRegularity

end TauCeti
