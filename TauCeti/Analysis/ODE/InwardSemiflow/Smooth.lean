/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InwardSemiflow.Existence
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Analysis.ODE.Gronwall

/-!
# Smoothness of inward forward semiflows and inward deformations of convex sets

Proves joint `C^m` smoothness up to `t = 0` and `∂C` (`Convex.contDiffOn_forwardSemiflow`, proved
at `m = 1` via `dysonSeriesLeft` and integral Grönwall, upgraded by induction on
`E × (E →L[ℝ] E)`), local/global `C^m` inward semiflows, and `C^m` inward deformations of convex
sets into their interiors.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.25–9.26.
-/

public section

open Filter Function Metric Set intervalIntegral
open scoped ContDiff NNReal Topology

namespace TauCeti

/-! ### Variational derivative and inductive `C^m` smoothness -/

section VariationalHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Spatial Taylor remainder estimate for the variational propagator `dysonSeriesLeft`: on `[0, τ]`,
`Φ t₀ y - Φ t₀ y₀ - A y₀ t₀ (y - y₀)` is bounded by `ε / 2 * ‖y - y₀‖` for `y ∈ ball x₀ r ∩ C`
sufficiently close to `y₀`. -/
private theorem exists_pos_norm_sub_sub_dysonSeriesLeft_le {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C))
    {x₀ y₀ : E} {r τ : ℝ} {KΦ : ℝ≥0} (hτ : 0 < τ) (h2rU : ball x₀ (2 * r) ⊆ U)
    (hy₀ : y₀ ∈ ball x₀ r ∩ C)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y =
        y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hLipΦ : ∀ t ∈ Icc 0 τ,
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    {t₀ ε : ℝ} (ht₀ : t₀ ∈ Icc 0 τ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ ball x₀ r ∩ C, dist y y₀ < δ →
      ‖forwardSemiflow X (U ∩ C) t₀ y - forwardSemiflow X (U ∩ C) t₀ y₀ -
        dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) y₀)) t₀ (y - y₀)‖ ≤
        ε / 2 * ‖y - y₀‖ := by
  set Φ := forwardSemiflow X (U ∩ C)
  set DX := fderivWithin ℝ X (U ∩ C)
  have hγ_cont {z : E} (hz : z ∈ ball x₀ r ∩ C) : ContinuousOn (fun s ↦ Φ s z) (Icc 0 τ) :=
    hcontΦ.comp (continuousOn_id.prodMk continuousOn_const) fun _ hs ↦ ⟨hs, hz⟩
  have hX_cont {z : E} (hz : z ∈ ball x₀ r ∩ C) : ContinuousOn (fun s ↦ X (Φ s z)) (Icc 0 τ) :=
    hX.continuousOn.comp (hγ_cont hz) fun s hs ↦ ⟨h2rU (hmem z hz s hs).1, (hmem z hz s hs).2⟩
  have hM₀_cont : Continuous (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀)) :=
    (hX.continuousOn_fderivWithin hU_uniq le_rfl).comp_continuous
      ((hγ_cont hy₀).comp_continuous (continuous_subtypeVal.comp continuous_projIcc)
        fun s ↦ (projIcc 0 τ hτ.le s).property)
      fun s ↦ ⟨h2rU (hmem y₀ hy₀ _ (projIcc 0 τ hτ.le s).property).1,
        (hmem y₀ hy₀ _ (projIcc 0 τ hτ.le s).property).2⟩
  obtain ⟨BD, hBD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hM₀_cont.norm).continuousOn (s := Icc 0 τ))
  set CD : ℝ := max BD 0; have hCD : 0 ≤ CD := le_max_right _ _
  have hCD_bound (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖DX (Φ s y₀)‖ ≤ CD :=
    (by simpa [projIcc_of_mem hτ.le hs] using hBD s hs : ‖DX (Φ s y₀)‖ ≤ BD).trans (le_max_left _ _)
  set K' : ℝ := (KΦ : ℝ) + 1 with hK'_def
  have hK' : 0 < K' := by positivity
  have hKΦ_le : (KΦ : ℝ) ≤ K' := by linarith [hK'_def]
  set η : ℝ := ε / (4 * τ * K' * Real.exp (CD * τ))
  obtain ⟨ρ, hρ, hTaylor⟩ := hC.exists_pos_norm_image_sub_sub_fderivWithin_le_of_isCompact
    hU hU_uniq hX (isCompact_Icc.image_of_continuousOn (hγ_cont hy₀))
    (by rintro _ ⟨s, hs, rfl⟩; exact ⟨h2rU (hmem y₀ hy₀ s hs).1, (hmem y₀ hy₀ s hs).2⟩)
    (by positivity : 0 < η)
  refine ⟨ρ / K', by positivity, fun y hy hdist ↦ ?_⟩
  let A := dysonSeriesLeft (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀))
  let w : ℝ → E := fun t ↦ Φ t y - Φ t y₀ - A t (y - y₀)
  set R₀ : ℝ := η * K' * ‖y - y₀‖
  have hw_cont : ContinuousOn (fun t ↦ ‖w t‖) (Icc 0 τ) :=
    ((hγ_cont hy).sub (hγ_cont hy₀) |>.sub
      ((continuous_dysonSeriesLeft hM₀_cont).clm_apply continuous_const).continuousOn).norm
  have hTaylor_s (s : ℝ) (hsI : s ∈ Icc 0 τ) :
      ‖X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀)‖ ≤ R₀ := by
    have hdist_s : dist (Φ s y) (Φ s y₀) < ρ :=
      ((hLipΦ s hsI).dist_le_mul y hy y₀ hy₀).trans_lt <|
        (mul_le_mul_of_nonneg_right hKΦ_le dist_nonneg).trans_lt
          ((mul_lt_mul_of_pos_left hdist hK').trans_eq (mul_div_cancel₀ ρ hK'.ne'))
    refine (hTaylor (Φ s y₀) (mem_image_of_mem _ hsI) (Φ s y) (hmem y hy s hsI).2 hdist_s).trans ?_
    calc η * ‖Φ s y - Φ s y₀‖ ≤ η * ((KΦ : ℝ) * ‖y - y₀‖) := by
          gcongr; simpa [dist_eq_norm] using (hLipΦ s hsI).dist_le_mul y hy y₀ hy₀
      _ ≤ R₀ := by simp only [R₀, mul_assoc]; gcongr
  have hw_bound (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖w t‖ ≤ R₀ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ :=
    calc ‖w t‖ ≤ R₀ * t + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ :=
          norm_sub_sub_dysonSeriesLeft_le_add_mul_integral hτ (hγ_cont hy) (hγ_cont hy₀)
            (hX_cont hy) (hX_cont hy₀) hM₀_cont hCD_bound (hint y hy) (hint y₀ hy₀) hTaylor_s ht
      _ ≤ R₀ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ := by gcongr; exact ht.2
  calc ‖w t₀‖ ≤ R₀ * τ * Real.exp (CD * (t₀ - 0)) :=
        le_mul_exp_of_le_add_mul_integral hw_cont.integrableOn_Icc hCD
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hw_bound) ht₀
          (hw_bound t₀ ht₀)
    _ ≤ R₀ * τ * Real.exp (CD * τ) := by gcongr; linarith [ht₀.2]
    _ = ε / 4 * ‖y - y₀‖ := by have := hτ.ne'; have := hK'.ne'; simp only [R₀, η]; field_simp
    _ ≤ ε / 2 * ‖y - y₀‖ := by nlinarith [norm_nonneg (y - y₀)]

/-- Joint Fréchet derivative of `uncurry (forwardSemiflow X (U ∩ C))` on
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)`, valid up to `t = 0` and `∂C`. -/
private theorem hasFDerivWithinAt_local_forwardSemiflow {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C))
    {x₀ : E} {r τ : ℝ} {KΦ : ℝ≥0} (hτ : 0 < τ) (h2rU : ball x₀ (2 * r) ⊆ U)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y = y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hLipΦ : ∀ t ∈ Icc 0 τ,
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    {p₀ : ℝ × E} (hp₀ : p₀ ∈ Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :
    HasFDerivWithinAt (uncurry (forwardSemiflow X (U ∩ C)))
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (X (forwardSemiflow X (U ∩ C) p₀.1 p₀.2)) +
        (dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) p₀.2)) p₀.1).comp
          (ContinuousLinearMap.snd ℝ ℝ E))
      (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) p₀ := by
  set Φ := forwardSemiflow X (U ∩ C)
  set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hXΦ_cont : ContinuousOn (X ∘ uncurry Φ) S := hX.continuousOn.comp hcontΦ
    fun p hp ↦ ⟨h2rU (hmem p.2 hp.2 p.1 hp.1).1, (hmem p.2 hp.2 p.1 hp.1).2⟩
  obtain ⟨δ₁, hδ₁, hcloseX⟩ :=
    Metric.continuousWithinAt_iff.mp (hXΦ_cont p₀ hp₀) (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hrem⟩ := exists_pos_norm_sub_sub_dysonSeriesLeft_le hC hU hU_uniq hX hτ h2rU
    hp₀.2 hmem hint hLipΦ hcontΦ hp₀.1 hε
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds p₀ (lt_min hδ₁ hδ₂)),
    self_mem_nhdsWithin] with p hpdist hpS
  rw [mem_ball] at hpdist
  have hp_d1 : dist p p₀ < δ₁ := hpdist.trans_le (min_le_left _ _)
  have hp_d2 : dist p.2 p₀.2 < δ₂ :=
    (le_max_right _ _).trans_lt (by rw [← Prod.dist_eq]; exact hpdist.trans_le (min_le_right _ _))
  let E₁ := Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)
  let E₂ := Φ p₀.1 p.2 - Φ p₀.1 p₀.2 - dysonSeriesLeft
    (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2)) p₀.1 (p.2 - p₀.2)
  have ht_inc : ‖E₁‖ ≤ ε / 2 * ‖p - p₀‖ := by
    have hX_y : ContinuousOn (fun s ↦ X (Φ s p.2)) (Icc 0 τ) :=
      hXΦ_cont.comp (continuousOn_id.prodMk continuousOn_const) fun _ hs ↦ ⟨hs, hpS.2⟩
    have hdiff_int : Φ p.1 p.2 - Φ p₀.1 p.2 = ∫ s in p₀.1..p.1, X (Φ s p.2) := by
      have hI1 : IntervalIntegrable (fun s ↦ X (Φ s p.2)) MeasureTheory.volume 0 p₀.1 :=
        (hX_y.mono (uIcc_of_le hp₀.1.1 ▸ Icc_subset_Icc_right hp₀.1.2)).intervalIntegrable
      have hI2 : IntervalIntegrable (fun s ↦ X (Φ s p.2)) MeasureTheory.volume p₀.1 p.1 :=
        (hX_y.mono (uIcc_subset_Icc hp₀.1 hpS.1)).intervalIntegrable
      rw [hint p.2 hpS.2 p.1 hpS.1, hint p.2 hpS.2 p₀.1 hp₀.1, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]; abel
    have hE₁_eq : E₁ = ∫ s in p₀.1..p.1, (X (Φ s p.2) - X (Φ p₀.1 p₀.2)) := by
      dsimp only [E₁]
      rw [hdiff_int, show (p.1 - p₀.1) • X (Φ p₀.1 p₀.2) =
          ∫ _ in p₀.1..p.1, X (Φ p₀.1 p₀.2) by simp, ← intervalIntegral.integral_sub
        (hX_y.mono (uIcc_subset_Icc hp₀.1 hpS.1)).intervalIntegrable intervalIntegrable_const]
    rw [hE₁_eq]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) fun s hs ↦ ?_).trans
      (Real.norm_eq_abs (p - p₀).1 ▸
        mul_le_mul_of_nonneg_left (norm_fst_le (p - p₀)) (half_pos hε).le)
    have habs : |s - p₀.1| ≤ |p.1 - p₀.1| := by
      rcases mem_uIcc.mp (uIoc_subset_uIcc hs) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by linarith [neg_abs_le (p.1 - p₀.1), abs_nonneg (p.1 - p₀.1)],
          by linarith [le_abs_self (p.1 - p₀.1), abs_nonneg (p.1 - p₀.1)]⟩
    have hs_dist : dist (s, p.2) p₀ < δ₁ := by
      rw [Prod.dist_eq] at hp_d1 ⊢
      exact max_lt (lt_of_le_of_lt (by simpa [Real.dist_eq] using habs)
        (max_lt_iff.mp hp_d1).1) (max_lt_iff.mp hp_d1).2
    refine le_of_lt ?_
    simpa only [Function.comp_apply, Function.uncurry_def, dist_eq_norm] using
      hcloseX (x := (s, p.2)) ⟨uIcc_subset_Icc hp₀.1 hpS.1 (uIoc_subset_uIcc hs), hpS.2⟩ hs_dist
  rw [show uncurry Φ p - uncurry Φ p₀ -
      ((ContinuousLinearMap.fst ℝ ℝ E).smulRight (X (Φ p₀.1 p₀.2)) +
        (dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2))
          p₀.1).comp (ContinuousLinearMap.snd ℝ ℝ E)) (p - p₀) = E₁ + E₂ by
    simp [uncurry, E₁, E₂]; abel]
  calc ‖E₁ + E₂‖ ≤ ‖E₁‖ + ‖E₂‖ := norm_add_le _ _
    _ ≤ ε / 2 * ‖p - p₀‖ + ε / 2 * ‖p.2 - p₀.2‖ := add_le_add ht_inc (hrem p.2 hpS.2 hp_d2)
    _ ≤ ε / 2 * ‖p - p₀‖ + ε / 2 * ‖p - p₀‖ := by gcongr; exact norm_snd_le (p - p₀)
    _ = ε * ‖p - p₀‖ := by ring

/-- Joint continuity of the variational propagator `dysonSeriesLeft` along `forwardSemiflow` on
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)`. -/
private theorem continuousOn_dysonSeriesLeft_forwardSemiflow {C U : Set E}
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C)) {x₀ : E}
    {r τ : ℝ} (hτ : 0 < τ) (h2rU : ball x₀ (2 * r) ⊆ U)
    (hmem : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C)
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C))) :
    ContinuousOn (fun p : ℝ × E ↦ dysonSeriesLeft
      (fun s ↦ fderivWithin ℝ X (U ∩ C)
        (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) p.2)) p.1)
      (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  let B := ↥(ball x₀ r ∩ C)
  let P : B → ℝ → E →L[ℝ] E := fun y s ↦
    fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) (projIcc 0 τ hτ.le s) y.val)
  have hΦP : Continuous (fun q : B × ℝ ↦
      uncurry (forwardSemiflow X (U ∩ C)) ((projIcc 0 τ hτ.le q.2 : ℝ), q.1.val)) :=
    hcontΦ.comp_continuous (((continuous_subtypeVal.comp continuous_projIcc).comp
      continuous_snd).prodMk (continuous_subtypeVal.comp continuous_fst))
      fun q ↦ ⟨(projIcc 0 τ hτ.le q.2).property, q.1.property⟩
  have hP_cont : Continuous (uncurry P) :=
    (hX.continuousOn_fderivWithin hU_uniq le_rfl).comp_continuous hΦP fun q ↦
      ⟨h2rU (hmem q.1.val q.1.property _ (projIcc 0 τ hτ.le q.2).property).1,
        (hmem q.1.val q.1.property _ (projIcc 0 τ hτ.le q.2).property).2⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_parametric_dysonSeriesLeft hP_cont).comp
    (((continuous_snd.comp continuous_subtypeVal).subtype_mk fun p ↦ p.property.2).prodMk
      (continuous_fst.comp continuous_subtypeVal))

/-- Identification of the variational semiflow on `E × (E →L[ℝ] E)` starting at `(y, 1)` with the
pair `(forwardSemiflow X (U ∩ C) · y, dysonSeriesLeft ·)`. -/
private theorem eq_forwardSemiflow_variational {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 2 X (U ∩ C))
    {x₀ y : E} {r₁ τ₁ b : ℝ} (hτ₁ : 0 < τ₁) (hb : 0 < b) (hb_le : b ≤ τ₁)
    (h2r₁U : ball x₀ (2 * r₁) ⊆ U)
    (hsub₁ : Ico 0 (2 * τ₁) ⊆ forwardSemiflowInterval X (U ∩ C) y)
    (hmem₁ : ∀ t ∈ Icc 0 τ₁, forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r₁) ∩ C)
    (hcont₁ : ContinuousOn (fun t ↦ forwardSemiflow X (U ∩ C) t y) (Icc 0 τ₁))
    {t : ℝ} (ht : t ∈ Ico 0 b) :
    let X' : E × (E →L[ℝ] E) → E × (E →L[ℝ] E) :=
      fun q ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2)
    forwardSemiflow X' ((U ×ˢ univ) ∩ (C ×ˢ univ)) t (y, (1 : E →L[ℝ] E)) =
      (forwardSemiflow X (U ∩ C) t y,
        dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) y)) t) := by
  intro X'
  have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (by norm_num)
  have hDX : ContDiffOn ℝ 1 (fderivWithin ℝ X (U ∩ C)) (U ∩ C) :=
    hX.fderivWithin hU_uniq (by norm_num)
  let S' : Set (E × (E →L[ℝ] E)) := (U ×ˢ univ) ∩ (C ×ˢ univ)
  have hX'_lip : LocallyLipschitzOn S' X' :=
    (hC.prod convex_univ).locallyLipschitzOn_inter_of_contDiffOn (hU.prod isOpen_univ) <|
      (hX1.comp contDiffOn_fst fun _ (hq : _ ∈ S') ↦ ⟨hq.1.1, hq.2.1⟩).prodMk
        ((hDX.comp contDiffOn_fst fun _ (hq : _ ∈ S') ↦ ⟨hq.1.1, hq.2.1⟩).clm_comp contDiffOn_snd)
  let M_y : ℝ → E →L[ℝ] E := fun s ↦
    fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) y)
  have hMy_cont : Continuous M_y := hDX.continuousOn.comp_continuous
    (hcont₁.comp_continuous (continuous_subtypeVal.comp continuous_projIcc)
      fun s ↦ (projIcc 0 τ₁ hτ₁.le s).property)
    fun s ↦ ⟨h2r₁U (hmem₁ _ (projIcc 0 τ₁ hτ₁.le s).property).1,
      (hmem₁ _ (projIcc 0 τ₁ hτ₁.le s).property).2⟩
  refine (hX'_lip.eqOn_forwardSemiflow
    (γ := fun s ↦ (forwardSemiflow X (U ∩ C) s y, dysonSeriesLeft M_y s))
    hb (Prod.ext (forwardSemiflow_zero _ _ _) (dysonSeriesLeft_zero _))
    (fun s hs ↦ ⟨⟨h2r₁U (hmem₁ s ⟨hs.1, hs.2.le.trans hb_le⟩).1, trivial⟩,
      ⟨(hmem₁ s ⟨hs.1, hs.2.le.trans hb_le⟩).2, trivial⟩⟩) (fun s hs ↦ ?_) ht).symm
  have hd₂ : HasDerivWithinAt (dysonSeriesLeft M_y)
      ((fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) s y)).comp (dysonSeriesLeft M_y s))
      (Ico 0 b) s := by
    simpa only [M_y, projIcc_of_mem hτ₁.le ⟨hs.1, hs.2.le.trans hb_le⟩,
      ContinuousLinearMap.mul_def] using (hasDerivAt_dysonSeriesLeft hMy_cont s).hasDerivWithinAt
  exact (((hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1).hasDerivWithinAt_forwardSemiflow_Ico
    hsub₁ ⟨hs.1, hs.2.trans_le (by linarith)⟩).mono (Ico_subset_Ico_right (by linarith))).prodMk hd₂

end VariationalHelpers

/-- Inductive short-time `C^{k+1}` regularity of `uncurry (forwardSemiflow X (U ∩ C))` on a uniform
neighborhood `Icc 0 τ ×ˢ (ball x₀ r ∩ C)`. -/
private theorem exists_local_forwardSemiflow_contDiffOn_nat.{u} (k : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {C U : Set E}
      (hC : Convex ℝ C) (hU : IsOpen U) {X : E → E} (hX : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C))
      {x₀ : E} (hx₀ : x₀ ∈ U ∩ C) (hX_in : X x₀ ∈ strictInwardCone C x₀),
      ∃ r > 0, ∃ τ > 0, ball x₀ r ⊆ U ∧
        (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
        ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C)))
          (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  induction k with
  | zero =>
    intro E _ _ _ C U hC hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := by simpa using hX
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hX_in
    obtain ⟨r, hr, τ, hτ, _, _, h2rU, _, hsub, hmem, hint, hLipΦ, hcontΦ⟩ :=
      hC.exists_local_forwardSemiflow_continuousOn hU
        (hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1) hx₀ hX_in
    have hS_uniq : UniqueDiffOn ℝ (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :=
      (uniqueDiffOn_Icc hτ).prod (hC.uniqueDiffOn_inter_of_mem_strictInwardCone isOpen_ball hX_in)
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith)).trans h2rU, hsub, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun _ hp ↦ hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1
      hτ h2rU hmem hint hLipΦ hcontΦ hp⟩
    exact (contDiffOn_const.smulRight (contDiffOn_zero.mpr <| hX1.continuousOn.comp hcontΦ
      fun p hp ↦ ⟨h2rU (hmem p.2 hp.2 p.1 hp.1).1, (hmem p.2 hp.2 p.1 hp.1).2⟩)).add
      ((contDiffOn_zero.mpr <| continuousOn_dysonSeriesLeft_forwardSemiflow
        hU_uniq hX1 hτ h2rU hmem hcontΦ).clm_comp contDiffOn_const)
  | succ k ih =>
    intro E _ _ _ C U hC hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (by norm_cast; omega)
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hX_in
    obtain ⟨r₁, hr₁, τ₁, hτ₁, _, _, h2r₁U, _, hsub₁, hmem₁, hint₁, hLip₁, hcont₁⟩ :=
      hC.exists_local_forwardSemiflow_continuousOn hU
        (hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1) hx₀ hX_in
    let F := E × (E →L[ℝ] E); let C' : Set F := C ×ˢ univ; let U' : Set F := U ×ˢ univ
    let X' : F → F := fun q ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2)
    have hX' : ContDiffOn ℝ (k + 1 : ℕ) X' (U' ∩ C') :=
      ((hX.of_le (by norm_cast; omega)).comp contDiffOn_fst
          fun _ (hq : _ ∈ U' ∩ C') ↦ ⟨hq.1.1, hq.2.1⟩).prodMk
        (((hX.fderivWithin hU_uniq (by norm_cast)).comp contDiffOn_fst
          fun _ (hq : _ ∈ U' ∩ C') ↦ ⟨hq.1.1, hq.2.1⟩).clm_comp contDiffOn_snd)
    let q₀ : F := (x₀, (1 : E →L[ℝ] E))
    have hq₀ : q₀ ∈ U' ∩ C' := ⟨⟨hx₀.1, trivial⟩, ⟨hx₀.2, trivial⟩⟩
    have hX'_in : X' q₀ ∈ strictInwardCone C' q₀ := by
      obtain ⟨t, ht_pos, ht_int⟩ := (hC.mem_strictInwardCone_iff hx₀.2).mp hX_in
      exact ((hC.prod convex_univ).mem_strictInwardCone_iff hq₀.2).mpr
        ⟨t, ht_pos, by rw [interior_prod_eq, interior_univ]; exact ⟨ht_int, trivial⟩⟩
    obtain ⟨r₂, hr₂, τ₂, hτ₂, _, _, hCD₂⟩ :=
      ih (hC.prod convex_univ) (hU.prod isOpen_univ) hX' hq₀ hX'_in
    set r := min r₁ r₂; have hr : 0 < r := lt_min hr₁ hr₂
    set τ := min (τ₁ / 2) τ₂; have hτ : 0 < τ := lt_min (half_pos hτ₁) hτ₂
    have hτ_le₁ : 2 * τ ≤ τ₁ := by linarith [min_le_left (τ₁ / 2) τ₂]
    set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
    have hS_uniq : UniqueDiffOn ℝ S :=
      (uniqueDiffOn_Icc hτ).prod (hC.uniqueDiffOn_inter_of_mem_strictInwardCone isOpen_ball hX_in)
    have hS_sub₁ : S ⊆ Icc 0 τ₁ ×ˢ (ball x₀ r₁ ∩ C) :=
      prod_mono (Icc_subset_Icc_right (by linarith))
        (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _)))
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith [min_le_left r₁ r₂])).trans h2r₁U,
      fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans
        (hsub₁ y ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩), ?_⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun _ hp ↦ (hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1
      hτ₁ h2r₁U hmem₁ hint₁ hLip₁ hcont₁ (hS_sub₁ hp)).mono hS_sub₁⟩
    let embed : ℝ × E → ℝ × F := fun p ↦ (p.1, (p.2, (1 : E →L[ℝ] E)))
    have hΨ_cd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X' (U' ∩ C')) ∘ embed) S :=
      hCD₂.comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const)) fun p hp ↦
        ⟨⟨hp.1.1, hp.1.2.trans (min_le_right _ _)⟩, mem_ball.mpr <| by
          rw [Prod.dist_eq]
          exact max_lt (lt_of_lt_of_le hp.2.1 (min_le_right _ _)) (by simp [embed, q₀, hr₂]),
          ⟨hp.2.2, trivial⟩⟩
    have hΨ_eq (p : ℝ × E) (hp : p ∈ S) : (uncurry (forwardSemiflow X' (U' ∩ C')) ∘ embed) p =
        (forwardSemiflow X (U ∩ C) p.1 p.2, dysonSeriesLeft (fun s ↦ fderivWithin ℝ X (U ∩ C)
          (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) p.2)) p.1) :=
      eq_forwardSemiflow_variational hC hU hU_uniq (hX.of_le (by norm_cast; omega)) hτ₁
        (by positivity : 0 < 2 * τ) hτ_le₁ h2r₁U (hsub₁ p.2 (hS_sub₁ hp).2)
        (hmem₁ p.2 (hS_sub₁ hp).2)
        (hcont₁.comp (continuousOn_id.prodMk continuousOn_const) fun _ hs ↦ ⟨hs, (hS_sub₁ hp).2⟩)
        ⟨hp.1.1, by linarith [hp.1.2]⟩
    have hΦ_cd : ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C))) S :=
      (contDiffOn_fst.comp hΨ_cd (mapsTo_univ _ _)).congr
        fun p hp ↦ congr_arg Prod.fst (hΨ_eq p hp).symm
    have hA_cd : ContDiffOn ℝ (k + 1 : ℕ) (fun p : ℝ × E ↦ dysonSeriesLeft (fun s ↦ fderivWithin
        ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) (projIcc 0 τ₁ hτ₁.le s) p.2)) p.1) S :=
      (contDiffOn_snd.comp hΨ_cd (mapsTo_univ _ _)).congr
        fun p hp ↦ congr_arg Prod.snd (hΨ_eq p hp).symm
    exact (contDiffOn_const.smulRight <| (hX.of_le (by norm_cast; omega)).comp hΦ_cd fun p hp ↦
      ⟨h2r₁U (hmem₁ p.2 (hS_sub₁ hp).2 p.1 (hS_sub₁ hp).1).1,
        (hmem₁ p.2 (hS_sub₁ hp).2 p.1 (hS_sub₁ hp).1).2⟩).add (hA_cd.clm_comp contDiffOn_const)

end TauCeti

section VariationalGlobal

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Propagation of `C^{k+1}` joint regularity of `forwardSemiflow` along any forward trajectory up
to time `T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
private theorem exists_contDiffOn_Icc_of_mem_forwardSemiflowInterval {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {k : ℕ} {X : E → E} (hX : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {x₀ : E} {T : ℝ}
    (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0,
      ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C)))
        (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU (hX.of_le (by norm_cast; omega))
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨r, hr, δ, hδ, _, hcd⟩ := hX_lip.exists_Icc_prod_of_mem_forwardSemiflowInterval
    (Q := ContDiffOn ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C))))
    (fun _ _ h hsub ↦ h.mono hsub) (fun _ h ↦ h.continuousOn)
    (fun _ h p hp ↦ let ⟨W, hW, hpW, hfW⟩ := h p hp
      (hfW p ⟨hp, hpW⟩).mono_of_mem_nhdsWithin
        (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (hW.mem_nhds hpW))))
    (fun {s δ' τ B₁ B₂} hQ₁ hQ₂ hs0 hδ' hmaps hcocycle ↦ by
      have hΦs : ContDiffOn ℝ (k + 1 : ℕ)
          (fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) s p.2) (Icc s (s + τ) ×ˢ B₁) :=
        hQ₁.comp (contDiffOn_const.prodMk contDiffOn_snd) fun _ hp ↦ ⟨⟨hs0, by linarith⟩, hp.2⟩
      exact (hQ₂.comp ((contDiffOn_fst.sub contDiffOn_const).prodMk hΦs)
        fun p hp ↦ ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hmaps p.2 hp.2⟩).congr hcocycle)
    (fun x hx ↦ by
      obtain ⟨r, hr, τ, hτ, _, hsub, hcd⟩ :=
        exists_local_forwardSemiflow_contDiffOn_nat k hC hU hX hx (hX_in x hx)
      exact ⟨r, hr, τ, hτ, fun y hy ↦ hsub y ⟨hy.1, hy.2.2⟩,
        hcd.mono (prod_mono Subset.rfl fun _ hy ↦ ⟨hy.1, hy.2.2⟩)⟩)
    hx₀ hT
  exact ⟨min r rU, lt_min hr hrU, δ, hδ, hcd.mono (prod_mono Subset.rfl fun _ hy ↦
    ⟨ball_subset_ball (min_le_left _ _) hy.1,
      hballU (ball_subset_ball (min_le_right _ _) hy.1), hy.2⟩)⟩

/-- **Joint `C^m` smoothness of the maximal forward semiflow.** For `1 ≤ m` (`m : ℕ∞`, including
`m = ∞`), if `X` is `C^m` on `U ∩ C` and strictly inward to the convex set `C` at every point of
`U ∩ C`, then `uncurry (forwardSemiflow X (U ∩ C))` is `C^m` on the entire maximal domain
`forwardSemiflowDomain X (U ∩ C)` — including at `t = 0` and along `∂C`. -/
theorem Convex.contDiffOn_forwardSemiflow {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U) {m : ℕ∞}
    (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ContDiffOn ℝ m (uncurry (forwardSemiflow X (U ∩ C))) (forwardSemiflowDomain X (U ∩ C)) := by
  rw [contDiffOn_iff_forall_nat_le]; intro j hj p hp
  set k : ℕ := max j 1 - 1
  have hk_eq : k + 1 = max j 1 := Nat.sub_add_cancel (le_max_right j 1)
  have hXk : ContDiffOn ℝ (k + 1 : ℕ) X (U ∩ C) := hX.of_le (mod_cast hk_eq ▸ max_le hj hm)
  obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp hp
  obtain ⟨r, hr, δ, hδ, hcd⟩ :=
    exists_contDiffOn_Icc_of_mem_forwardSemiflowInterval hC hU hXk hX_in hpU hpJ
  exact ((hcd p ⟨⟨nonneg_of_mem_forwardSemiflowInterval hpJ, by linarith⟩,
    mem_ball_self hr, hpU.2⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio (p.1 + δ) ×ˢ ball p.2 r, isOpen_Iio.prod isOpen_ball,
        ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩,
        fun _ (hq : _ ∈ _ ∩ forwardSemiflowDomain X (U ∩ C)) ↦
          ⟨⟨nonneg_of_mem_forwardSemiflowInterval (mem_forwardSemiflowDomain_iff.mp hq.2).2,
            hq.1.1.le⟩, hq.1.2, (mem_forwardSemiflowDomain_iff.mp hq.2).1.2⟩⟩).of_le
    (by norm_cast; omega)

/-- **Global `C^m` smoothness of a forward-complete inward semiflow on `Ici 0 ×ˢ C`.** -/
theorem Convex.contDiffOn_forwardSemiflow_Ici {C : Set E} (hC : Convex ℝ C) {m : ℕ∞} (hm : 1 ≤ m)
    {X : E → E} (hX : ContDiffOn ℝ m X C) (hX_in : ∀ x ∈ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ C, forwardSemiflowInterval X C x = Ici 0) :
    ContDiffOn ℝ m (uncurry (forwardSemiflow X C)) (Ici 0 ×ˢ C) := by
  simpa only [univ_inter, forwardSemiflowDomain_eq_Ici_prod hglob] using
    hC.contDiffOn_forwardSemiflow isOpen_univ hm
      (by simpa only [univ_inter] using hX) (fun x hx ↦ hX_in x hx.2)

/-- **Finite-time `C^m` smoothness of an inward semiflow on `Icc 0 T ×ˢ C`.** -/
theorem Convex.contDiffOn_forwardSemiflow_Icc {C : Set E} (hC : Convex ℝ C) {m : ℕ∞} (hm : 1 ≤ m)
    {X : E → E} (hX : ContDiffOn ℝ m X C) (hX_in : ∀ x ∈ C, X x ∈ strictInwardCone C x)
    {T : ℝ} (hT : ∀ x ∈ C, T ∈ forwardSemiflowInterval X C x) :
    ContDiffOn ℝ m (uncurry (forwardSemiflow X C)) (Icc 0 T ×ˢ C) := by
  have hCD : ContDiffOn ℝ m (uncurry (forwardSemiflow X C)) (forwardSemiflowDomain X C) := by
    simpa only [univ_inter] using hC.contDiffOn_forwardSemiflow isOpen_univ hm
      (by simpa only [univ_inter] using hX) (fun x hx ↦ hX_in x hx.2)
  exact hCD.mono fun ⟨t, x⟩ ⟨ht, hx⟩ ↦
    mem_forwardSemiflowDomain_iff.mpr ⟨hx, Icc_subset_forwardSemiflowInterval_of_mem (hT x hx) ht⟩

end VariationalGlobal

section ConvexDeformation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Local `C^m` forward semiflow of a vector field strictly inward at a point.** If `C` is a
convex subset of a Banach space `E`, `U` is open, `X` is `C^m` on `U ∩ C` (`1 ≤ m`, including
`m = ∞`), and `X x₀ ∈ strictInwardCone C x₀` at `x₀ ∈ U ∩ C`, then on a neighborhood
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)` there exists a jointly `C^m` map `Φ : ℝ → E → E` integrating `X`,
mapping positive times into `interior C`, and satisfying the local semiflow cocycle law. -/
theorem Convex.exists_contDiffOn_inwardSemiflow {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C)) {x₀ : E}
    (hx₀ : x₀ ∈ U ∩ C) (hX_in : X x₀ ∈ TauCeti.strictInwardCone C x₀) :
    ∃ r > 0, ∃ τ > 0, ∃ Φ : ℝ → E → E,
      ball x₀ r ⊆ U ∧ ContDiffOn ℝ m (uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) ∧
      (∀ y ∈ ball x₀ r ∩ C, Φ 0 y = y) ∧
      MapsTo (uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) (U ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Ioc 0 τ, Φ t y ∈ interior C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        HasDerivWithinAt (fun s ↦ Φ s y) (X (Φ t y)) (Icc 0 τ) t) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → t + s ≤ τ →
        Φ s y ∈ ball x₀ r → Φ (t + s) y = Φ t (Φ s y)) := by
  -- Step 1: Shrink to an open ball `U' ⊆ U` on which `X` stays strictly inward to `C`.
  have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (mod_cast hm)
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp
    (hC.eventually_mem_strictInwardCone_of_continuousWithinAt hX_in (hX1.continuousOn x₀ hx₀))
  set U' := ball x₀ (min rU rI)
  have hU'_sub : U' ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hballU
  have hX_lip_U' : LocallyLipschitzOn (U' ∩ C) X :=
    hC.locallyLipschitzOn_inter_of_contDiffOn isOpen_ball
      (hX1.mono (inter_subset_inter_left C hU'_sub))
  have hX_in_U' (y : E) (hy : y ∈ U' ∩ C) : X y ∈ TauCeti.strictInwardCone C y :=
    hballI ⟨ball_subset_ball (min_le_right _ _) hy.1, hU'_sub hy.1, hy.2⟩ hy.2
  -- Step 2: Restrict the maximal `C^m` semiflow on `U' ∩ C` to a uniform short-time box.
  obtain ⟨r, hr, τ, hτ, _, _, h2rU', _, hsub, -⟩ :=
    hC.exists_local_forwardSemiflow_continuousOn isOpen_ball hX_lip_U'
      ⟨mem_ball_self (lt_min hrU hrI), hx₀.2⟩ hX_in
  have hrU' : ball x₀ r ⊆ U' := (ball_subset_ball (by linarith)).trans h2rU'
  let Φ := TauCeti.forwardSemiflow X (U' ∩ C)
  have hdom : Icc 0 τ ×ˢ (ball x₀ r ∩ C) ⊆ TauCeti.forwardSemiflowDomain X (U' ∩ C) :=
    fun p hp ↦ TauCeti.mem_forwardSemiflowDomain_iff.mpr
      ⟨⟨hrU' hp.2.1, hp.2.2⟩, hsub p.2 hp.2 ⟨hp.1.1, by linarith [hp.1.2]⟩⟩
  have hmaps : MapsTo (uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) (U ∩ C) := fun _ hp ↦ by
    have h := TauCeti.forwardSemiflow_mem (TauCeti.mem_forwardSemiflowDomain_iff.mp (hdom hp)).2
    exact ⟨hU'_sub h.1, h.2⟩
  refine ⟨r, hr, τ, hτ, Φ, hrU'.trans hU'_sub,
    (hC.contDiffOn_forwardSemiflow isOpen_ball hm
      (hX.mono (inter_subset_inter_left C hU'_sub)) hX_in_U').mono hdom,
    fun _ _ ↦ TauCeti.forwardSemiflow_zero _ _ _, hmaps,
    fun y hy _ ht ↦ hC.forwardSemiflow_mem_interior inter_subset_right hX_in_U'
      (hsub y hy ⟨ht.1.le, by linarith [ht.2]⟩) ht.1,
    fun y hy _ ht ↦ (hX_lip_U'.hasDerivWithinAt_forwardSemiflow
      (hsub y hy ⟨ht.1, by linarith [ht.2]⟩)).mono
        (fun _ (hs : _ ∈ Icc 0 τ) ↦ hsub y hy ⟨hs.1, by linarith [hs.2]⟩),
    fun y hy t s ht hs hts hΦs ↦ ?_⟩
  have hsJ := hsub y hy ⟨hs, by linarith⟩
  exact hX_lip_U'.forwardSemiflow_add hsJ
    (hsub (Φ s y) ⟨hΦs, (TauCeti.forwardSemiflow_mem hsJ).2⟩ ⟨ht, by linarith⟩)

/-- **`C^m` inward deformation of a convex set into its interior.** Given a `C^m` (`1 ≤ m`,
including `m = ∞`) strictly inward vector field `X` on a convex set `C` whose forward semiflow is
defined through time `T > 0` for every `x ∈ C`, the time-`T` map `r := forwardSemiflow X C T` and
the reparametrized semiflow `H (t, x) := forwardSemiflow X C (T * (1 - t) ^ 2) x` deform `C` into
`interior C` while preserving `interior C` at every time. -/
theorem Convex.exists_contDiffOn_inward_deformation {C : Set E} (hC : Convex ℝ C) {m : ℕ∞}
    (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X C)
    (hX_in : ∀ x ∈ C, X x ∈ TauCeti.strictInwardCone C x)
    {T : ℝ} (hT_pos : 0 < T) (hT : ∀ x ∈ C, T ∈ TauCeti.forwardSemiflowInterval X C x) :
    ∃ (r : E → E) (H : ℝ × E → E),
      ContDiffOn ℝ m r C ∧ MapsTo r C (interior C) ∧ ContDiffOn ℝ m H (Icc 0 1 ×ˢ C) ∧
      (∀ x ∈ C, H (0, x) = r x) ∧ (∀ x ∈ C, H (1, x) = x) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ C, H (t, x) ∈ interior C) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ interior C, H (t, x) ∈ interior C) := by
  have hCD := hC.contDiffOn_forwardSemiflow_Icc hm hX hX_in hT
  refine ⟨TauCeti.forwardSemiflow X C T,
    fun p ↦ TauCeti.forwardSemiflow X C (T * (1 - p.1) ^ 2) p.2,
    hCD.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx ↦ ⟨⟨hT_pos.le, le_rfl⟩, hx⟩),
    fun x hx ↦ hC.forwardSemiflow_mem_interior Subset.rfl hX_in (hT x hx) hT_pos,
    hCD.comp ((contDiffOn_const.mul ((contDiffOn_const.sub contDiffOn_fst).pow 2)).prodMk
      contDiffOn_snd)
      (fun _ hp ↦ ⟨⟨mul_nonneg hT_pos.le (sq_nonneg _),
        mul_le_of_le_one_right hT_pos.le (by nlinarith [hp.1.1, hp.1.2])⟩, hp.2⟩),
    fun _ _ ↦ by simp, fun _ _ ↦ by simp,
    fun t ht x hx ↦ let hpos := mul_pos hT_pos (sq_pos_of_pos (sub_pos.mpr ht.2))
      hC.forwardSemiflow_mem_interior Subset.rfl hX_in
        (TauCeti.Icc_subset_forwardSemiflowInterval_of_mem (hT x hx)
          ⟨hpos.le, mul_le_of_le_one_right hT_pos.le (by nlinarith [ht.1, ht.2])⟩) hpos,
    fun t ht x hx ↦ hC.forwardSemiflow_mem_interior_of_mem_interior Subset.rfl hX_in hx
      (TauCeti.Icc_subset_forwardSemiflowInterval_of_mem (hT x (interior_subset hx))
        ⟨mul_nonneg hT_pos.le (sq_nonneg _),
          mul_le_of_le_one_right hT_pos.le (by nlinarith [ht.1, ht.2])⟩)⟩

end ConvexDeformation
