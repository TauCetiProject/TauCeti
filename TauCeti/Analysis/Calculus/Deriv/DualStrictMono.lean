/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Regular curves are locally monotone along a functional

A `C¹` curve `γ : ℝ → E` in a real normed space with nowhere vanishing derivative is, on every short
parameter window `[s, s + δ]`, strictly increasing after composing with a continuous linear
functional: one of norm one that takes the value `‖γ' s‖` at `γ' s`. On a compact interval of
starting parameters the window width `δ` can be chosen uniformly. The same holds uniformly along a
jointly `C¹` family `Γ t` of such curves, for the curves `u ↦ Γ (τ u) u` whose time `τ` stays in a
compact interval and moves slowly with the parameter.

## Main results

* `ContDiff.exists_strictMonoOn_dual_comp`: uniform windows on which a regular `C¹` curve is
  strictly increasing along a continuous linear functional.
* `ContDiff.exists_strictMonoOn_dual_comp_uncurry`: the same uniformly along a `C¹` family of
  regular curves, even when the time moves slowly with the curve parameter.
-/

public section

open Function Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E}

/-- **Uniform windows along a `C¹` family of curves.** Let `Γ t` be a family of curves, jointly
`C¹` in the time `t` and the curve parameter, such that each `Γ t` with `t ∈ [t₀, t₁]` has nowhere
vanishing derivative. Then there are a window width `δ > 0` and a speed `lam > 0` such that, for
every time function `τ` with values in `[t₀, t₁]` which is `lam`-Lipschitz, the curve
`u ↦ Γ (τ u) u` is strictly increasing after a suitable continuous linear functional on every
window `[s, s + δ]` with `s ∈ [a, b]`. -/
theorem ContDiff.exists_strictMonoOn_dual_comp_uncurry {Γ : ℝ → ℝ → E}
    (hΓ : ContDiff ℝ 1 (uncurry Γ)) {t₀ t₁ : ℝ} (hderiv : ∀ t ∈ Icc t₀ t₁, ∀ s, deriv (Γ t) s ≠ 0)
    (a b : ℝ) :
    ∃ δ > 0, ∃ lam > 0, ∀ τ : ℝ → ℝ, (∀ u, τ u ∈ Icc t₀ t₁) →
      (∀ x y, |τ x - τ y| ≤ lam * |x - y|) → ∀ s ∈ Icc a b, ∃ φ : StrongDual ℝ E,
        StrictMonoOn (fun u ↦ φ (Γ (τ u) u)) (Icc s (s + δ)) := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨1, one_pos, 1, one_pos, fun _ _ _ s hs ↦ absurd (hs.1.trans hs.2) (not_le.2 hba)⟩
  rcases lt_or_ge t₁ t₀ with ht | ht
  · exact ⟨1, one_pos, 1, one_pos, fun τ hτ _ ↦ absurd ((hτ 0).1.trans (hτ 0).2) (not_le.2 ht)⟩
  -- The constants come from compactness of `Q = [t₀, t₁] × [a, b + 1]`: a bound `B` on the
  -- derivative of `Γ`, a lower bound `m` for the derivative of the curves, and a modulus `δ₁` of
  -- uniform continuity of that derivative.
  set Q : Set (ℝ × ℝ) := Icc t₀ t₁ ×ˢ Icc a (b + 1) with hQ
  have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQv : Convex ℝ Q := (convex_Icc _ _).prod (convex_Icc _ _)
  have hQ0 : (t₀, a) ∈ Q := ⟨⟨le_rfl, ht⟩, ⟨le_rfl, by linarith⟩⟩
  have hdiff : Differentiable ℝ (uncurry Γ) := hΓ.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ (uncurry Γ)) := hΓ.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn hfc.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hQ0)
  have hlipΓ {t₁ t₂ s : ℝ} (h₁ : (t₁, s) ∈ Q) (h₂ : (t₂, s) ∈ Q) :
      ‖Γ t₁ s - Γ t₂ s‖ ≤ B * |t₁ - t₂| := by
    have := hQv.norm_image_sub_le_of_norm_fderiv_le (fun x _ ↦ hdiff x) hB h₂ h₁
    simpa [Prod.norm_def, Real.norm_eq_abs] using this
  -- The derivative `v (t, s)` of the curve `Γ t` at `s`.
  set v : ℝ × ℝ → E := fun p ↦ fderiv ℝ (uncurry Γ) p ((0 : ℝ), (1 : ℝ)) with hv
  have hvc : Continuous v := hfc.clm_apply continuous_const
  have hvd (t s : ℝ) : HasDerivAt (Γ t) (v (t, s)) s := by
    have h := (hdiff (t, s)).hasFDerivAt.comp_hasDerivAt s
      (HasDerivAt.prodMk (hasDerivAt_const s t) (hasDerivAt_id s))
    have e : (uncurry Γ ∘ Prod.mk t) = Γ t := by funext s; simp
    rwa [e] at h
  obtain ⟨p₀, hp₀, hmin⟩ := hQc.exists_isMinOn ⟨_, hQ0⟩ hvc.norm.continuousOn
  set m := ‖v p₀‖ with hm_def
  have hm : 0 < m := norm_pos_iff.2 fun h0 ↦
    hderiv _ hp₀.1 p₀.2 (by rw [(hvd p₀.1 p₀.2).deriv, Prod.mk.eta, h0])
  obtain ⟨δ₁, hδ₁, huc⟩ := Metric.uniformContinuousOn_iff.1
    (hQc.uniformContinuousOn_of_continuous hvc.continuousOn) (m / 4) (by positivity)
  set δ := min (δ₁ / 2) 1 with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ₁' : δ ≤ δ₁ / 2 := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set lam := min 1 (m / (2 * (B + 1))) with hlam_def
  have hlam : 0 < lam := lt_min one_pos (by positivity)
  have hlam1 : lam ≤ 1 := min_le_left _ _
  have hBlam : B * lam ≤ m / 2 := by
    have h₁ : lam * (2 * (B + 1)) ≤ m := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, lam, hlam, fun τ hτI hlip s hs ↦ ?_⟩
  have memQ {u : ℝ} (hu : u ∈ Icc s (s + δ)) (t : ℝ) : (τ t, u) ∈ Q :=
    ⟨hτI t, by linarith [hu.1, hs.1], by linarith [hu.2, hs.2]⟩
  have hs' : s ∈ Icc s (s + δ) := ⟨le_rfl, by linarith⟩
  -- Along `φ`, the dual vector of `v (τ s, s)`, the curve increases on `[s, s + δ]`.
  obtain ⟨φ, hφ, hφv⟩ := exists_dual_vector'' ℝ (v (τ s, s))
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hφv
  have hφle (w : E) : |φ w| ≤ ‖w‖ := by
    simpa [Real.norm_eq_abs] using
      (φ.le_opNorm w).trans (mul_le_of_le_one_left (norm_nonneg _) hφ)
  have hnear {y u : ℝ} (hy : y ∈ Icc s (s + δ)) (hu : u ∈ Icc s (s + δ)) :
      3 * m / 4 ≤ φ (v (τ y, u)) := by
    have hd : dist (τ y, u) (τ s, s) < δ₁ := by
      simp only [Prod.dist_eq, Real.dist_eq]
      have h₁ : |τ y - τ s| ≤ |y - s| :=
        (hlip y s).trans (mul_le_of_le_one_left (abs_nonneg _) hlam1)
      have h₂ : |y - s| ≤ δ := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h₃ : |u - s| ≤ δ := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
      exact max_lt (by linarith) (by linarith)
    have h₁ := huc _ (memQ hu y) _ (memQ hs' s) hd
    rw [dist_eq_norm] at h₁
    have h₂ : m ≤ ‖v (τ s, s)‖ := isMinOn_iff.1 hmin _ (memQ hs' s)
    have h₃ := hφle (v (τ y, u) - v (τ s, s))
    rw [map_sub, hφv] at h₃
    linarith [neg_abs_le (φ (v (τ y, u)) - ‖v (τ s, s)‖)]
  refine ⟨φ, fun x hx y hy hxy ↦ ?_⟩
  -- Moving the curve parameter from `x` to `y` at the fixed time `τ y` gains at least `3m/4` per
  -- unit, while changing the time from `τ x` to `τ y` costs at most `B lam ≤ m/2` per unit.
  have hg : 3 * m / 4 * (y - x) ≤ φ (Γ (τ y) y) - φ (Γ (τ y) x) := by
    have hderg (u : ℝ) : HasDerivAt (fun u ↦ φ (Γ (τ y) u)) (φ (v (τ y, u))) u :=
      φ.hasFDerivAt.comp_hasDerivAt u (hvd (τ y) u)
    refine (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
      (fun u _ ↦ (hderg u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hderg u).differentiableAt.differentiableWithinAt) (fun u hu ↦ ?_)
      x (left_mem_Icc.2 hxy.le) y (right_mem_Icc.2 hxy.le) hxy.le
    rw [interior_Icc] at hu
    rw [(hderg u).deriv]
    exact hnear hy ⟨by linarith [hx.1, hu.1], by linarith [hy.2, hu.2]⟩
  have htime : |φ (Γ (τ y) x) - φ (Γ (τ x) x)| ≤ m / 2 * (y - x) := by
    rw [← map_sub]
    refine (hφle _).trans ((hlipΓ (memQ hx y) (memQ hx x)).trans ?_)
    have h₁ : |τ y - τ x| ≤ lam * (y - x) := by
      simpa [abs_of_pos (sub_pos.2 hxy)] using hlip y x
    calc B * |τ y - τ x| ≤ B * (lam * (y - x)) := by gcongr
      _ = B * lam * (y - x) := by ring
      _ ≤ m / 2 * (y - x) := by gcongr
  dsimp only
  nlinarith [abs_le.1 htime, sub_pos.2 hxy]

/-- A `C¹` curve with nowhere vanishing derivative is strictly increasing after a suitable
continuous linear functional on every window `[s, s + δ]` of a uniform width `δ > 0`, for starting
parameters `s` in a compact interval `[a, b]`. -/
theorem ContDiff.exists_strictMonoOn_dual_comp (hγ : ContDiff ℝ 1 γ)
    (hderiv : ∀ t, deriv γ t ≠ 0) (a b : ℝ) :
    ∃ δ > 0, ∀ s ∈ Icc a b, ∃ φ : StrongDual ℝ E,
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc s (s + δ)) := by
  have hΓ : ContDiff ℝ 1 (uncurry fun _ : ℝ ↦ γ) := by
    have e : (uncurry fun _ : ℝ ↦ γ) = γ ∘ Prod.snd := by funext p; simp [uncurry_def]
    rw [e]
    exact hγ.comp contDiff_snd
  obtain ⟨δ, hδ, lam, hlam, h⟩ :=
    hΓ.exists_strictMonoOn_dual_comp_uncurry (t₀ := 0) (t₁ := 0) (fun _ _ ↦ hderiv) a b
  exact ⟨δ, hδ, h (fun _ ↦ 0) (fun _ ↦ left_mem_Icc.2 le_rfl)
    (fun _ _ ↦ by simpa using mul_nonneg hlam.le (abs_nonneg _))⟩
