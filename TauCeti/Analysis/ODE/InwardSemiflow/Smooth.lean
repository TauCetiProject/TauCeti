/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.ODE.InwardSemiflow.Existence
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
    {x₀ y₀ : E} {r τ : ℝ} {KΦ : ℝ≥0} (hτ : 0 < τ) (hy₀ : y₀ ∈ ball x₀ r ∩ C)
    (hmemU : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ U ∩ C)
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
    hX.continuousOn.comp (hγ_cont hz) fun s hs ↦ hmemU z hz s hs
  -- Step 1: Bound `‖DX (Φ s y₀)‖` uniformly on `[0, τ]` by `CD ≥ 0`.
  have hM₀_cont : Continuous (fun s ↦ DX (Φ (projIcc 0 τ hτ.le s) y₀)) :=
    (hX.continuousOn_fderivWithin hU_uniq le_rfl).comp_continuous
      ((hγ_cont hy₀).comp_continuous (continuous_subtypeVal.comp continuous_projIcc)
        fun s ↦ (projIcc 0 τ hτ.le s).property)
      fun s ↦ hmemU y₀ hy₀ _ (projIcc 0 τ hτ.le s).property
  obtain ⟨BD, hBD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hM₀_cont.norm).continuousOn (s := Icc 0 τ))
  set CD : ℝ := max BD 0; have hCD : 0 ≤ CD := le_max_right _ _
  have hCD_bound (s : ℝ) (hs : s ∈ Icc 0 τ) : ‖DX (Φ s y₀)‖ ≤ CD :=
    (by simpa [projIcc_of_mem hτ.le hs] using hBD s hs : ‖DX (Φ s y₀)‖ ≤ BD).trans (le_max_left _ _)
  -- Step 2: Obtain a uniform Taylor radius `ρ` along the compact image `Φ ([0, τ] × {y₀})`.
  set K' : ℝ := (KΦ : ℝ) + 1 with hK'_def
  have hK' : 0 < K' := by positivity
  have hKΦ_le : (KΦ : ℝ) ≤ K' := by linarith [hK'_def]
  set η : ℝ := ε / (4 * τ * K' * Real.exp (CD * τ))
  obtain ⟨ρ, hρ, hTaylor⟩ := hC.exists_pos_norm_image_sub_sub_fderivWithin_le_of_isCompact
    hU hU_uniq hX (isCompact_Icc.image_of_continuousOn (hγ_cont hy₀))
    (by rintro _ ⟨s, hs, rfl⟩; exact hmemU y₀ hy₀ s hs)
    (by positivity : 0 < η)
  refine ⟨ρ / K', by positivity, fun y hy hdist ↦ ?_⟩
  -- Step 3: Bound the nonlinear Taylor remainder and form the forced Volterra integral equation.
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
    refine (hTaylor (Φ s y₀) (mem_image_of_mem _ hsI) (Φ s y) (hmemU y hy s hsI).2 hdist_s).trans ?_
    calc η * ‖Φ s y - Φ s y₀‖ ≤ η * ((KΦ : ℝ) * ‖y - y₀‖) := by
          gcongr; simpa [dist_eq_norm] using (hLipΦ s hsI).dist_le_mul y hy y₀ hy₀
      _ ≤ R₀ := by simp only [R₀, mul_assoc]; gcongr
  have hδ_cont : ContinuousOn (fun s ↦ Φ s y - Φ s y₀) (Icc 0 τ) := (hγ_cont hy).sub (hγ_cont hy₀)
  have hM₀_contOn : ContinuousOn (fun s ↦ DX (Φ s y₀)) (Icc 0 τ) :=
    hM₀_cont.continuousOn.congr fun s hs ↦ by simp [projIcc_of_mem hτ.le hs]
  have hr_cont : ContinuousOn (fun s ↦ X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀))
      (Icc 0 τ) :=
    ((hX_cont hy).sub (hX_cont hy₀)).sub (hM₀_contOn.clm_apply hδ_cont)
  have h0y : Φ 0 y = y := forwardSemiflow_zero _ _ _
  have h0y₀ : Φ 0 y₀ = y₀ := forwardSemiflow_zero _ _ _
  have hδ_int (t : ℝ) (ht : t ∈ Icc 0 τ) :
      Φ t y - Φ t y₀ = (Φ 0 y - Φ 0 y₀) + ∫ s in (0 : ℝ)..t,
        (DX (Φ (projIcc 0 τ hτ.le s) y₀) (Φ s y - Φ s y₀) +
          (X (Φ s y) - X (Φ s y₀) - DX (Φ s y₀) (Φ s y - Φ s y₀))) := by
    have hsub_t : uIcc 0 t ⊆ Icc 0 τ := uIcc_of_le ht.1 ▸ Icc_subset_Icc_right ht.2
    have hI1 := ((hX_cont hy).mono hsub_t).intervalIntegrable (μ := MeasureTheory.volume)
    have hI2 := ((hX_cont hy₀).mono hsub_t).intervalIntegrable (μ := MeasureTheory.volume)
    rw [hint y hy t ht, hint y₀ hy₀ t ht, h0y, h0y₀, add_sub_add_comm,
      ← intervalIntegral.integral_sub hI1 hI2]
    refine congr_arg ((y - y₀) + ·) (intervalIntegral.integral_congr fun s hs ↦ ?_)
    simp only [projIcc_of_mem hτ.le (hsub_t hs)]; abel
  -- Step 4: Apply the linear Volterra bound and Grönwall's inequality.
  have hw_bound (t : ℝ) (ht : t ∈ Icc 0 τ) : ‖w t‖ ≤ R₀ * τ + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ := by
    have hbound : ‖w t‖ ≤ R₀ * t + CD * ∫ s in (0 : ℝ)..t, ‖w s‖ := by
      simpa only [w, A, h0y, h0y₀] using
        norm_sub_dysonSeriesLeft_apply_le_add_mul_integral hM₀_cont hδ_cont
          (uIcc_of_le hτ.le ▸ hr_cont).intervalIntegrable
          (fun s hs ↦ by simpa [projIcc_of_mem hτ.le hs] using hCD_bound s hs)
          hTaylor_s hδ_int ht
    exact hbound.trans (by gcongr; exact ht.2)
  calc ‖w t₀‖ ≤ R₀ * τ * Real.exp (CD * (t₀ - 0)) :=
        le_mul_exp_of_le_add_mul_integral hw_cont.integrableOn_Icc hCD
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hw_bound) ht₀
          (hw_bound t₀ ht₀)
    _ ≤ R₀ * τ * Real.exp (CD * τ) := by gcongr; linarith [ht₀.2]
    _ = ε / 4 * ‖y - y₀‖ := by have := hτ.ne'; have := hK'.ne'; simp only [R₀, η]; field_simp
    _ ≤ ε / 2 * ‖y - y₀‖ := by nlinarith [norm_nonneg (y - y₀)]

/-- Time-increment remainder estimate on `Icc 0 τ ×ˢ (ball x₀ r ∩ C)`: for `p` close enough to
`p₀` so `X ∘ uncurry Φ` stays within `ε / 2` of `X (Φ p₀.1 p₀.2)`, the difference
`Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)` has norm at most `ε / 2 * ‖p - p₀‖`. -/
private theorem norm_forwardSemiflow_time_increment_le {C U : Set E} {X : E → E}
    (hX : ContDiffOn ℝ 1 X (U ∩ C)) {x₀ : E} {r τ ε δ₁ : ℝ} (hε : 0 < ε)
    (hmemU : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ U ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y = y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hcontΦ : ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)))
    {p₀ p : ℝ × E} (hp₀ : p₀ ∈ Icc 0 τ ×ˢ (ball x₀ r ∩ C)) (hpS : p ∈ Icc 0 τ ×ˢ (ball x₀ r ∩ C))
    (hp_d1 : dist p p₀ < δ₁)
    (hcloseX : ∀ ⦃q⦄, q ∈ Icc 0 τ ×ˢ (ball x₀ r ∩ C) → dist q p₀ < δ₁ →
      dist (X (uncurry (forwardSemiflow X (U ∩ C)) q))
        (X (uncurry (forwardSemiflow X (U ∩ C)) p₀)) < ε / 2) :
    ‖forwardSemiflow X (U ∩ C) p.1 p.2 - forwardSemiflow X (U ∩ C) p₀.1 p.2 -
        (p.1 - p₀.1) • X (forwardSemiflow X (U ∩ C) p₀.1 p₀.2)‖ ≤
      ε / 2 * ‖p - p₀‖ := by
  set Φ := forwardSemiflow X (U ∩ C)
  have hXΦ_cont : ContinuousOn (X ∘ uncurry Φ) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :=
    hX.continuousOn.comp hcontΦ fun q hq ↦ hmemU q.2 hq.2 q.1 hq.1
  have hX_y : ContinuousOn (fun s ↦ X (Φ s p.2)) (Icc 0 τ) :=
    hXΦ_cont.comp (continuousOn_id.prodMk continuousOn_const) fun _ hs ↦ ⟨hs, hpS.2⟩
  have hdiff_int : Φ p.1 p.2 - Φ p₀.1 p.2 = ∫ s in p₀.1..p.1, X (Φ s p.2) := by
    have hI1 : IntervalIntegrable (fun s ↦ X (Φ s p.2)) MeasureTheory.volume 0 p₀.1 :=
      (hX_y.mono (uIcc_of_le hp₀.1.1 ▸ Icc_subset_Icc_right hp₀.1.2)).intervalIntegrable
    have hI2 : IntervalIntegrable (fun s ↦ X (Φ s p.2)) MeasureTheory.volume p₀.1 p.1 :=
      (hX_y.mono (uIcc_subset_Icc hp₀.1 hpS.1)).intervalIntegrable
    rw [hint p.2 hpS.2 p.1 hpS.1, hint p.2 hpS.2 p₀.1 hp₀.1, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]; abel
  have hE₁_eq : Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2) =
      ∫ s in p₀.1..p.1, (X (Φ s p.2) - X (Φ p₀.1 p₀.2)) := by
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
  simpa only [Function.uncurry_def, dist_eq_norm] using
    hcloseX (q := (s, p.2)) ⟨uIcc_subset_Icc hp₀.1 hpS.1 (uIoc_subset_uIcc hs), hpS.2⟩ hs_dist

/-- Joint Fréchet derivative of `uncurry (forwardSemiflow X (U ∩ C))` on
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)`, valid up to `t = 0` and `∂C`. -/
private theorem hasFDerivWithinAt_local_forwardSemiflow {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 1 X (U ∩ C))
    {x₀ : E} {r τ : ℝ} {K : ℝ≥0} (hτ : 0 < τ)
    (hmemU : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ U ∩ C)
    (hint : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
      forwardSemiflow X (U ∩ C) t y = y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y))
    (hLipΦ : ∀ t ∈ Icc 0 τ,
      LipschitzOnWith (Real.toNNReal (Real.exp ((K : ℝ) * t)))
        (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C))
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
  have hXΦ_cont : ContinuousOn (X ∘ uncurry Φ) S :=
    hX.continuousOn.comp hcontΦ fun p hp ↦ hmemU p.2 hp.2 p.1 hp.1
  obtain ⟨δ₁, hδ₁, hcloseX⟩ :=
    Metric.continuousWithinAt_iff.mp (hXΦ_cont p₀ hp₀) (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, hrem⟩ := exists_pos_norm_sub_sub_dysonSeriesLeft_le hC hU hU_uniq hX hτ
    hp₀.2 hmemU hint (fun t ht ↦ (hLipΦ t ht).weaken (Real.toNNReal_mono
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))))
    hcontΦ hp₀.1 hε
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds p₀ (lt_min hδ₁ hδ₂)),
    self_mem_nhdsWithin] with p hpdist hpS
  rw [mem_ball] at hpdist
  have hp_d1 : dist p p₀ < δ₁ := hpdist.trans_le (min_le_left _ _)
  have hp_d2 : dist p.2 p₀.2 < δ₂ :=
    (le_max_right _ _).trans_lt (by rw [← Prod.dist_eq]; exact hpdist.trans_le (min_le_right _ _))
  let E₁ := Φ p.1 p.2 - Φ p₀.1 p.2 - (p.1 - p₀.1) • X (Φ p₀.1 p₀.2)
  let E₂ := Φ p₀.1 p.2 - Φ p₀.1 p₀.2 - dysonSeriesLeft
    (fun s ↦ fderivWithin ℝ X (U ∩ C) (Φ (projIcc 0 τ hτ.le s) p₀.2)) p₀.1 (p.2 - p₀.2)
  have ht_inc : ‖E₁‖ ≤ ε / 2 * ‖p - p₀‖ :=
    norm_forwardSemiflow_time_increment_le hX hε hmemU hint hcontΦ hp₀ hpS hp_d1
      (fun q hq hdist ↦ hcloseX hq hdist)
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
    {r τ : ℝ} (hτ : 0 < τ)
    (hmemU : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ U ∩ C)
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
    (hX.continuousOn_fderivWithin hU_uniq le_rfl).comp_continuous hΦP
      fun q ↦ hmemU q.1.val q.1.property _ (projIcc 0 τ hτ.le q.2).property
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_parametric_dysonSeriesLeft hP_cont).comp
    (((continuous_snd.comp continuous_subtypeVal).subtype_mk fun p ↦ p.property.2).prodMk
      (continuous_fst.comp continuous_subtypeVal))

/-- Identification of the variational semiflow on `E × (E →L[ℝ] E)` starting at `(y, 1)` with the
pair `(forwardSemiflow X (U ∩ C) · y, dysonSeriesLeft ·)`. -/
private theorem eq_forwardSemiflow_variational {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    (hU_uniq : UniqueDiffOn ℝ (U ∩ C)) {X : E → E} (hX : ContDiffOn ℝ 2 X (U ∩ C))
    {y : E} {τ₁ b : ℝ} (hτ₁ : 0 < τ₁) (hb : 0 < b) (hb_le : b ≤ τ₁)
    (hsub₁ : Ico 0 (2 * τ₁) ⊆ forwardSemiflowInterval X (U ∩ C) y)
    (hmemU₁ : ∀ t ∈ Icc 0 τ₁, forwardSemiflow X (U ∩ C) t y ∈ U ∩ C)
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
    fun s ↦ hmemU₁ _ (projIcc 0 τ₁ hτ₁.le s).property
  refine (hX'_lip.eqOn_forwardSemiflow
    (γ := fun s ↦ (forwardSemiflow X (U ∩ C) s y, dysonSeriesLeft M_y s))
    hb (Prod.ext (forwardSemiflow_zero _ _ _) (dysonSeriesLeft_zero _))
    (fun s hs ↦ ⟨⟨(hmemU₁ s ⟨hs.1, hs.2.le.trans hb_le⟩).1, trivial⟩,
      ⟨(hmemU₁ s ⟨hs.1, hs.2.le.trans hb_le⟩).2, trivial⟩⟩) (fun s hs ↦ ?_) ht).symm
  have hd₂ : HasDerivWithinAt (dysonSeriesLeft M_y)
      ((fderivWithin ℝ X (U ∩ C) (forwardSemiflow X (U ∩ C) s y)).comp (dysonSeriesLeft M_y s))
      (Ico 0 b) s := by
    simpa only [M_y, projIcc_of_mem hτ₁.le ⟨hs.1, hs.2.le.trans hb_le⟩,
      ContinuousLinearMap.mul_def] using (hasDerivAt_dysonSeriesLeft hMy_cont s).hasDerivWithinAt
  exact (((hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1).hasDerivWithinAt_forwardSemiflow_Ico
    hsub₁ ⟨hs.1, hs.2.trans_le (by linarith)⟩).mono (Ico_subset_Ico_right (by linarith))).prodMk hd₂

omit [CompleteSpace E] in
/-- `C^{k+1}` regularity of the lifted variational vector field on `(U ×ˢ univ) ∩ (C ×ˢ univ)`. -/
private theorem contDiffOn_variationalField {C U : Set E} (hU_uniq : UniqueDiffOn ℝ (U ∩ C))
    {k : ℕ} {X : E → E} (hX : ContDiffOn ℝ ((k + 1 : ℕ) + 1 : ℕ) X (U ∩ C)) :
    ContDiffOn ℝ (k + 1 : ℕ)
      (fun q : E × (E →L[ℝ] E) ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2))
      ((U ×ˢ univ) ∩ (C ×ˢ univ)) :=
  ((hX.of_le (by norm_cast; omega)).comp contDiffOn_fst
      fun _ (hq : _ ∈ (U ×ˢ univ) ∩ (C ×ˢ univ)) ↦ ⟨hq.1.1, hq.2.1⟩).prodMk
    (((hX.fderivWithin hU_uniq (by norm_cast)).comp contDiffOn_fst
      fun _ (hq : _ ∈ (U ×ˢ univ) ∩ (C ×ˢ univ)) ↦ ⟨hq.1.1, hq.2.1⟩).clm_comp contDiffOn_snd)

omit [CompleteSpace E] in
/-- Strict inwardness of the lifted variational vector field at `(x₀, 1)` on `C ×ˢ univ`. -/
private theorem variationalField_mem_strictInwardCone {C U : Set E} (hC : Convex ℝ C) {X : E → E}
    {x₀ : E} (hx₀ : x₀ ∈ C) (hX_in : X x₀ ∈ strictInwardCone C x₀) :
    (X x₀, (fderivWithin ℝ X (U ∩ C) x₀).comp (1 : E →L[ℝ] E)) ∈
      strictInwardCone (C ×ˢ (univ : Set (E →L[ℝ] E))) (x₀, (1 : E →L[ℝ] E)) := by
  obtain ⟨t, ht_pos, ht_int⟩ := (hC.mem_strictInwardCone_iff hx₀).mp hX_in
  refine ((hC.prod convex_univ).mem_strictInwardCone_iff (x := (x₀, (1 : E →L[ℝ] E)))
    ⟨hx₀, trivial⟩).mpr ⟨t, ht_pos, ?_⟩
  rw [interior_prod_eq, interior_univ]
  exact ⟨ht_int, trivial⟩

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
    -- Base case (`k = 0`, `C^1`): compute the joint Fréchet derivative via `dysonSeriesLeft` and
    -- verify its continuity on `Icc 0 τ ×ˢ (ball x₀ r ∩ C)`.
    intro E _ _ _ C U hC hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := by simpa using hX
    have hC_uniq := hC.uniqueDiffOn_of_mem_strictInwardCone hX_in
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hX_in
    obtain ⟨r, hr, τ, hτ, _, h2rU, _, hsub, hmem, hint, hLipΦ, hcontΦ⟩ :=
      hC.exists_local_forwardSemiflow_continuousOn hU
        (hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1) hx₀ hX_in
    have hmemU (y : E) (hy : y ∈ ball x₀ r ∩ C) (t : ℝ) (ht : t ∈ Icc 0 τ) :
        forwardSemiflow X (U ∩ C) t y ∈ U ∩ C := inter_subset_inter_left C h2rU (hmem y hy t ht)
    have hS_uniq : UniqueDiffOn ℝ (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :=
      (uniqueDiffOn_Icc hτ).prod (inter_comm C _ ▸ hC_uniq.inter isOpen_ball)
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith)).trans h2rU, hsub, ?_⟩
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun _ hp ↦ hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1
      hτ hmemU hint hLipΦ hcontΦ hp⟩
    exact (contDiffOn_const.smulRight (contDiffOn_zero.mpr <| hX1.continuousOn.comp hcontΦ
      fun p hp ↦ hmemU p.2 hp.2 p.1 hp.1)).add
      ((contDiffOn_zero.mpr <| continuousOn_dysonSeriesLeft_forwardSemiflow
        hU_uniq hX1 hτ hmemU hcontΦ).clm_comp contDiffOn_const)
  | succ k ih =>
    -- Step 1: Obtain local `C^0`/Lipschitz semiflow data for `X` on `(r₁, τ₁)`.
    intro E _ _ _ C U hC hU X hX x₀ hx₀ hX_in
    have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (by norm_cast; omega)
    have hC_uniq := hC.uniqueDiffOn_of_mem_strictInwardCone hX_in
    have hU_uniq := hC.uniqueDiffOn_inter_of_mem_strictInwardCone hU hX_in
    obtain ⟨r₁, hr₁, τ₁, hτ₁, _, h2r₁U, _, hsub₁, hmem₁, hint₁, hLip₁, hcont₁⟩ :=
      hC.exists_local_forwardSemiflow_continuousOn hU
        (hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1) hx₀ hX_in
    have hmem₁U (y : E) (hy : y ∈ ball x₀ r₁ ∩ C) (t : ℝ) (ht : t ∈ Icc 0 τ₁) :
        forwardSemiflow X (U ∩ C) t y ∈ U ∩ C := inter_subset_inter_left C h2r₁U (hmem₁ y hy t ht)
    -- Step 2: Lift to the variational vector field `X'` on `E × (E →L[ℝ] E)` and apply `ih`.
    let F := E × (E →L[ℝ] E); let C' : Set F := C ×ˢ univ; let U' : Set F := U ×ˢ univ
    let X' : F → F := fun q ↦ (X q.1, (fderivWithin ℝ X (U ∩ C) q.1).comp q.2)
    have hX' : ContDiffOn ℝ (k + 1 : ℕ) X' (U' ∩ C') :=
      contDiffOn_variationalField hU_uniq hX
    let q₀ : F := (x₀, (1 : E →L[ℝ] E))
    have hq₀ : q₀ ∈ U' ∩ C' := ⟨⟨hx₀.1, trivial⟩, ⟨hx₀.2, trivial⟩⟩
    have hX'_in : X' q₀ ∈ strictInwardCone C' q₀ :=
      variationalField_mem_strictInwardCone hC (U := U) hx₀.2 hX_in
    obtain ⟨r₂, hr₂, τ₂, hτ₂, _, _, hCD₂⟩ :=
      ih (hC.prod convex_univ) (hU.prod isOpen_univ) hX' hq₀ hX'_in
    -- Step 3: Intersect neighborhoods to `S = Icc 0 τ ×ˢ (ball x₀ r ∩ C)`.
    set r := min r₁ r₂; have hr : 0 < r := lt_min hr₁ hr₂
    set τ := min (τ₁ / 2) τ₂; have hτ : 0 < τ := lt_min (half_pos hτ₁) hτ₂
    have hτ_le₁ : 2 * τ ≤ τ₁ := by linarith [min_le_left (τ₁ / 2) τ₂]
    set S := Icc 0 τ ×ˢ (ball x₀ r ∩ C)
    have hS_uniq : UniqueDiffOn ℝ S :=
      (uniqueDiffOn_Icc hτ).prod (inter_comm C _ ▸ hC_uniq.inter isOpen_ball)
    have hS_sub₁ : S ⊆ Icc 0 τ₁ ×ˢ (ball x₀ r₁ ∩ C) :=
      prod_mono (Icc_subset_Icc_right (by linarith))
        (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _)))
    refine ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith [min_le_left r₁ r₂])).trans h2r₁U,
      fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans
        (hsub₁ y ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩), ?_⟩
    -- Step 4: Identify the variational semiflow components with `(Φ, dysonSeriesLeft)` and
    -- bootstrap `C^{k+2}` regularity from `HasFDerivWithinAt` and `C^{k+1}` derivative components.
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS_uniq]
    refine ⟨by simp, _, ?_, fun _ hp ↦ (hasFDerivWithinAt_local_forwardSemiflow hC hU hU_uniq hX1
      hτ₁ hmem₁U hint₁ hLip₁ hcont₁ (hS_sub₁ hp)).mono hS_sub₁⟩
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
        (by positivity : 0 < 2 * τ) hτ_le₁ (hsub₁ p.2 (hS_sub₁ hp).2)
        (hmem₁U p.2 (hS_sub₁ hp).2)
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
      hmem₁U p.2 (hS_sub₁ hp).2 p.1 (hS_sub₁ hp).1).add (hA_cd.clm_comp contDiffOn_const)

end TauCeti

section VariationalGlobal

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

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
  have hX_lip := hC.locallyLipschitzOn_inter_of_contDiffOn hU (hXk.of_le (by norm_cast; omega))
  have hCD := (hX_lip.forwardSemiflow_prod_inter_induction hU
    (Q := ContDiffWithinAt ℝ (k + 1 : ℕ) (uncurry (forwardSemiflow X (U ∩ C))))
    (fun _ _ _ _ hsub h ↦ h.mono hsub) (fun _ h _ hq ↦ (h _ hq).continuousWithinAt)
    (fun _ _ _ _ hmem h ↦ h.mono_of_mem_nhdsWithin hmem)
    (fun {s _ τ B₁ B₂} hQ₁ hQ₂ hs0 _ hmaps hcocycle ↦ by
      have hΦs : ContDiffOn ℝ (k + 1 : ℕ)
          (fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) s p.2) (Icc s (s + τ) ×ˢ B₁) :=
        ContDiffOn.comp (g := uncurry (forwardSemiflow X (U ∩ C))) hQ₁
          (contDiffOn_const.prodMk contDiffOn_snd) fun _ hq ↦ ⟨⟨hs0, by linarith⟩, hq.2⟩
      exact (ContDiffOn.comp (g := uncurry (forwardSemiflow X (U ∩ C))) hQ₂
        ((contDiffOn_fst.sub contDiffOn_const).prodMk hΦs)
        fun q hq ↦ ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, hmaps q.2 hq.2⟩).congr
        hcocycle)
    (fun x hx ↦ by
      obtain ⟨r, hr, τ, hτ, _, hsub, hcd⟩ :=
        exists_local_forwardSemiflow_contDiffOn_nat k hC hU hXk hx (hX_in x hx)
      exact ⟨r, hr, τ, hτ, hsub, hcd⟩)).2 p hp
  exact hCD.of_le (by norm_cast; omega)

end VariationalGlobal

section ConvexDeformation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Local `C^m` forward semiflow of a vector field strictly inward at a point.** If `C` is a
convex subset of a Banach space `E`, `U` is open, `X` is `C^m` on `U ∩ C` (`1 ≤ m`, including
`m = ∞`), and `X x₀ ∈ strictInwardCone C x₀` at `x₀ ∈ U ∩ C`, then on a neighborhood
`Icc 0 τ ×ˢ (ball x₀ r ∩ C)` the canonical semiflow `TauCeti.forwardSemiflow X (U ∩ C)` is defined
through `[0, 2 * τ)`, jointly `C^m`, maps into `U ∩ C` (and into `interior C` for `t > 0`),
solves `γ' = X ∘ γ`, and satisfies the semiflow cocycle law for all `t, s ≥ 0` with `t + s ≤ τ`. -/
theorem Convex.exists_local_forwardSemiflow_contDiffOn {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C)) {x₀ : E}
    (hx₀ : x₀ ∈ U ∩ C) (hX_in : X x₀ ∈ TauCeti.strictInwardCone C x₀) :
    ∃ r > 0, ∃ τ > 0,
      ball x₀ r ⊆ U ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ TauCeti.forwardSemiflowInterval X (U ∩ C) y) ∧
      ContDiffOn ℝ m (uncurry (TauCeti.forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) ∧
      MapsTo (uncurry (TauCeti.forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) (U ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Ioc 0 τ,
        TauCeti.forwardSemiflow X (U ∩ C) t y ∈ interior C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        HasDerivWithinAt (fun s ↦ TauCeti.forwardSemiflow X (U ∩ C) s y)
          (X (TauCeti.forwardSemiflow X (U ∩ C) t y)) (Icc 0 τ) t) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t s : ℝ, 0 ≤ t → 0 ≤ s → t + s ≤ τ →
        TauCeti.forwardSemiflow X (U ∩ C) (t + s) y =
          TauCeti.forwardSemiflow X (U ∩ C) t (TauCeti.forwardSemiflow X (U ∩ C) s y)) := by
  -- Step 1: Shrink to an open ball `U' ⊆ U` on which `X` stays strictly inward to `C`.
  have hX1 : ContDiffOn ℝ 1 X (U ∩ C) := hX.of_le (mod_cast hm)
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp
    (hC.eventually_mem_strictInwardCone_of_continuousWithinAt hX_in (hX1.continuousOn x₀ hx₀))
  set U' := ball x₀ (min rU rI)
  have hU'_sub : U' ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hballU
  have hX_lip_U : LocallyLipschitzOn (U ∩ C) X :=
    hC.locallyLipschitzOn_inter_of_contDiffOn hU hX1
  have hX_lip_U' : LocallyLipschitzOn (U' ∩ C) X :=
    hC.locallyLipschitzOn_inter_of_contDiffOn isOpen_ball
      (hX1.mono (inter_subset_inter_left C hU'_sub))
  have hX_in_U' (y : E) (hy : y ∈ U' ∩ C) : X y ∈ TauCeti.strictInwardCone C y :=
    hballI ⟨ball_subset_ball (min_le_right _ _) hy.1, hU'_sub hy.1, hy.2⟩ hy.2
  -- Step 2: Restrict the `C^m` semiflow on `U' ∩ C` to a uniform short-time box and identify it
  -- with `forwardSemiflow X (U ∩ C)` by forward uniqueness.
  obtain ⟨r, hr, τ, hτ, _, h2rU', _, hsub, -⟩ :=
    hC.exists_local_forwardSemiflow_continuousOn isOpen_ball hX_lip_U'
      ⟨mem_ball_self (lt_min hrU hrI), hx₀.2⟩ hX_in
  have hrU' : ball x₀ r ⊆ U' := (ball_subset_ball (by linarith)).trans h2rU'
  let Φ' := TauCeti.forwardSemiflow X (U' ∩ C)
  have hsub_U (y : E) (hy : y ∈ ball x₀ r ∩ C) :
      Ico 0 (2 * τ) ⊆ TauCeti.forwardSemiflowInterval X (U ∩ C) y :=
    TauCeti.Ico_subset_forwardSemiflowInterval (γ := fun t ↦ Φ' t y) (by positivity)
      (TauCeti.forwardSemiflow_zero _ _ _)
      (fun _ hs ↦ let h := TauCeti.forwardSemiflow_mem (hsub y hy hs); ⟨hU'_sub h.1, h.2⟩)
      fun _ hs ↦ hX_lip_U'.hasDerivWithinAt_forwardSemiflow_Ico (hsub y hy) hs
  have heq_U (y : E) (hy : y ∈ ball x₀ r ∩ C) :
      EqOn (fun t ↦ Φ' t y) (fun t ↦ TauCeti.forwardSemiflow X (U ∩ C) t y) (Ico 0 (2 * τ)) :=
    hX_lip_U.eqOn_forwardSemiflow (by positivity) (TauCeti.forwardSemiflow_zero _ _ _)
      (fun _ hs ↦ let h := TauCeti.forwardSemiflow_mem (hsub y hy hs); ⟨hU'_sub h.1, h.2⟩)
      fun _ hs ↦ hX_lip_U'.hasDerivWithinAt_forwardSemiflow_Ico (hsub y hy) hs
  have hdom' : Icc 0 τ ×ˢ (ball x₀ r ∩ C) ⊆ TauCeti.forwardSemiflowDomain X (U' ∩ C) :=
    fun p hp ↦ TauCeti.mem_forwardSemiflowDomain_iff.mpr
      ⟨⟨hrU' hp.2.1, hp.2.2⟩, hsub p.2 hp.2 ⟨hp.1.1, by linarith [hp.1.2]⟩⟩
  have hCD' : ContDiffOn ℝ m (uncurry Φ') (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) :=
    (hC.contDiffOn_forwardSemiflow isOpen_ball hm
      (hX.mono (inter_subset_inter_left C hU'_sub)) hX_in_U').mono hdom'
  refine ⟨r, hr, τ, hτ, hrU'.trans hU'_sub, hsub_U,
    hCD'.congr fun p hp ↦ (heq_U p.2 hp.2 ⟨hp.1.1, by linarith [hp.1.2]⟩).symm,
    fun p hp ↦ TauCeti.forwardSemiflow_mem (hsub_U p.2 hp.2 ⟨hp.1.1, by linarith [hp.1.2]⟩),
    fun y hy t ht ↦ by
      have heq : Φ' t y = TauCeti.forwardSemiflow X (U ∩ C) t y :=
        heq_U y hy ⟨ht.1.le, by linarith [ht.2]⟩
      exact heq ▸ hC.forwardSemiflow_mem_interior inter_subset_right hX_in_U'
        (hsub y hy ⟨ht.1.le, by linarith [ht.2]⟩) ht.1,
    fun y hy t ht ↦ (hX_lip_U.hasDerivWithinAt_forwardSemiflow
      (hsub_U y hy ⟨ht.1, by linarith [ht.2]⟩)).mono
        fun _ (hs : _ ∈ Icc 0 τ) ↦ hsub_U y hy ⟨hs.1, by linarith [hs.2]⟩,
    fun y hy t s ht hs hts ↦ ?_⟩
  have hsJ := hsub_U y hy ⟨hs, by linarith⟩
  have htsJ := hsub_U y hy (⟨by linarith, by linarith⟩ : t + s ∈ Ico 0 (2 * τ))
  exact hX_lip_U.forwardSemiflow_add hsJ
    ((hX_lip_U.add_mem_forwardSemiflowInterval_iff hsJ ht).mp htsJ)

/-- **Joint `C^m` smoothness of an inward semiflow under a smooth time change.** Given a `C^m`
(`1 ≤ m`, including `m = ∞`) vector field `X` on `U ∩ C` (`U` open, `C` convex) that is strictly
inward to `C` on `U ∩ C`, and a `C^m` time change `σ : ℝ → ℝ` on `J : Set ℝ` taking values in
`forwardSemiflowInterval X (U ∩ C) x` for every `x ∈ U ∩ C`, the reparametrized semiflow
`(t, x) ↦ forwardSemiflow X (U ∩ C) (σ t) x` is `C^m` on `J ×ˢ (U ∩ C)`. -/
theorem Convex.contDiffOn_forwardSemiflow_comp {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    {J : Set ℝ} {σ : ℝ → ℝ} (hσ : ContDiffOn ℝ m σ J)
    (hσ_mem : ∀ t ∈ J, ∀ x ∈ U ∩ C, σ t ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) :
    ContDiffOn ℝ m (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (σ p.1) p.2)
      (J ×ˢ (U ∩ C)) := by
  have hCD := hC.contDiffOn_forwardSemiflow hU hm hX hX_in
  have hσ_fst : ContDiffOn ℝ m (fun p : ℝ × E ↦ σ p.1) (J ×ˢ (U ∩ C)) :=
    hσ.comp contDiffOn_fst fun _ hp ↦ hp.1
  exact hCD.comp (hσ_fst.prodMk contDiffOn_snd)
    fun p hp ↦ TauCeti.mem_forwardSemiflowDomain_iff.mpr ⟨hp.2, hσ_mem p.1 hp.1 p.2 hp.2⟩

omit [CompleteSpace E] in
/-- Interior entry and preservation along a reparametrized inward semiflow on `U ∩ C`. -/
private theorem mapsTo_inter_interior_forwardSemiflow_comp {C U : Set E} (hC : Convex ℝ C)
    {X : E → E} (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    {J : Set ℝ} {σ : ℝ → ℝ}
    (hσ_mem : ∀ t ∈ J, ∀ x ∈ U ∩ C, σ t ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) :
    (∀ t ∈ J, 0 < σ t → ∀ x ∈ U ∩ C,
      TauCeti.forwardSemiflow X (U ∩ C) (σ t) x ∈ U ∩ interior C) ∧
      (∀ t ∈ J, ∀ x ∈ U ∩ interior C,
        TauCeti.forwardSemiflow X (U ∩ C) (σ t) x ∈ U ∩ interior C) :=
  ⟨fun t ht hσt x hx ↦ ⟨(TauCeti.forwardSemiflow_mem (hσ_mem t ht x hx)).1,
      hC.forwardSemiflow_mem_interior inter_subset_right hX_in (hσ_mem t ht x hx) hσt⟩,
    fun t ht x hx ↦ ⟨(TauCeti.forwardSemiflow_mem (hσ_mem t ht x ⟨hx.1, interior_subset hx.2⟩)).1,
      hC.forwardSemiflow_mem_interior_of_mem_interior inter_subset_right hX_in hx.2
        (hσ_mem t ht x ⟨hx.1, interior_subset hx.2⟩)⟩⟩

/-- Shared core for `C^m` inward deformations on an arbitrary time set `J : Set ℝ`. -/
private theorem contDiffOn_inward_deformation_of_mem {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x) {T : ℝ} (hT_pos : 0 < T)
    (hT : ∀ x ∈ U ∩ C, T ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) {J : Set ℝ}
    (hσ_mem : ∀ t ∈ J, ∀ x ∈ U ∩ C,
      T * (1 - t) ^ 2 ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) :
    ContDiffOn ℝ m (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) ∧
      MapsTo (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) (U ∩ interior C) ∧
      ContDiffOn ℝ m (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2)
        (J ×ˢ (U ∩ C)) ∧
      (∀ t ∈ J, t ≠ 1 → ∀ x ∈ U ∩ C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) ∧
      (∀ t ∈ J, ∀ x ∈ U ∩ interior C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) := by
  have hCD_T : ContDiffOn ℝ m (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) :=
    (hC.contDiffOn_forwardSemiflow hU hm hX hX_in).comp (contDiffOn_const.prodMk contDiffOn_id)
      fun x hx ↦ TauCeti.mem_forwardSemiflowDomain_iff.mpr ⟨hx, hT x hx⟩
  have hCD := hC.contDiffOn_forwardSemiflow_comp hU hm hX hX_in
    (contDiffOn_const.mul ((contDiffOn_const.sub contDiffOn_id).pow 2)) hσ_mem
  have hint := mapsTo_inter_interior_forwardSemiflow_comp hC hX_in hσ_mem
  exact ⟨hCD_T, fun x hx ↦ ⟨(TauCeti.forwardSemiflow_mem (hT x hx)).1,
      hC.forwardSemiflow_mem_interior inter_subset_right hX_in (hT x hx) hT_pos⟩,
    hCD,
    fun t ht hne x hx ↦ hint.1 t ht (mul_pos hT_pos (sq_pos_iff.mpr (sub_ne_zero.mpr hne.symm)))
      x hx,
    hint.2⟩

/-- **Global real-time `C^m` inward deformation of `U ∩ C` into `U ∩ interior C`.** Given a `C^m`
(`1 ≤ m`, including `m = ∞`) vector field `X` on `U ∩ C` (`U` open, `C` convex) that is strictly
inward to `C` on `U ∩ C` and globally forward complete on `U ∩ C`
(`forwardSemiflowInterval X (U ∩ C) x = Ici 0`), and `T > 0`, the time-`T` map
`forwardSemiflow X (U ∩ C) T` and the reparametrized semiflow
`fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2` deform `U ∩ C` into
`U ∩ interior C` smoothly across all `univ ×ˢ (U ∩ C)` (agreeing with `forwardSemiflow X (U ∩ C) T`
at `t = 0` and the identity at `t = 1`, both by `simp`), mapping `U ∩ C` into `U ∩ interior C` for
all `t ≠ 1` and preserving `U ∩ interior C` for all `t : ℝ`. -/
theorem Convex.contDiffOn_inward_deformation {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, TauCeti.forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T : ℝ} (hT_pos : 0 < T) :
    ContDiffOn ℝ m (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) ∧
      MapsTo (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) (U ∩ interior C) ∧
      ContDiffOn ℝ m (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2)
        (univ ×ˢ (U ∩ C)) ∧
      (∀ t : ℝ, t ≠ 1 → ∀ x ∈ U ∩ C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) ∧
      (∀ t : ℝ, ∀ x ∈ U ∩ interior C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) :=
  let h := contDiffOn_inward_deformation_of_mem hC hU hm hX hX_in hT_pos
    (fun x hx ↦ hglob x hx ▸ hT_pos.le)
    (J := univ) (fun _ _ x hx ↦ hglob x hx ▸ mul_nonneg hT_pos.le (sq_nonneg _))
  ⟨h.1, h.2.1, h.2.2.1, fun t ht ↦ h.2.2.2.1 t trivial ht, fun t ↦ h.2.2.2.2 t trivial⟩

/-- **Finite-time `C^m` inward deformation of `U ∩ C` into `U ∩ interior C`.** Given a `C^m`
(`1 ≤ m`, including `m = ∞`) vector field `X` on `U ∩ C` (`U` open, `C` convex) that is strictly
inward to `C` on `U ∩ C` and whose forward semiflow is defined through time `T > 0` for every
`x ∈ U ∩ C`, the time-`T` map `forwardSemiflow X (U ∩ C) T` and the reparametrized semiflow
`fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2` deform `U ∩ C` into
`U ∩ interior C` on `Icc 0 1 ×ˢ (U ∩ C)` while preserving `U ∩ interior C` at every time. -/
theorem Convex.contDiffOn_inward_deformation_Icc_prod {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    {T : ℝ} (hT_pos : 0 < T) (hT : ∀ x ∈ U ∩ C, T ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) :
    ContDiffOn ℝ m (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) ∧
      MapsTo (TauCeti.forwardSemiflow X (U ∩ C) T) (U ∩ C) (U ∩ interior C) ∧
      ContDiffOn ℝ m (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2)
        (Icc 0 1 ×ˢ (U ∩ C)) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, ∀ x ∈ U ∩ C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U ∩ interior C,
        TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x ∈ U ∩ interior C) :=
  let h := contDiffOn_inward_deformation_of_mem hC hU hm hX hX_in hT_pos hT
    (J := Icc 0 1) fun _ ht _ hx ↦ TauCeti.Icc_subset_forwardSemiflowInterval_of_mem (hT _ hx)
      ⟨mul_nonneg hT_pos.le (sq_nonneg _),
        mul_le_of_le_one_right hT_pos.le (by nlinarith [ht.1, ht.2])⟩
  ⟨h.1, h.2.1, h.2.2.1, fun t ht ↦ h.2.2.2.1 t (Ico_subset_Icc_self ht) ht.2.ne, h.2.2.2.2⟩

end ConvexDeformation
