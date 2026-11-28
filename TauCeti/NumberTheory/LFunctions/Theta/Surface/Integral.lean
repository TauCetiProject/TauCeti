/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Integrability, continuity, and decay of surface integrals

Generic helpers for integrating functions of the form `x ↦ w x * g (surfaceScale x t)` over a
bounded subset `D` of the norm-one surface `normOneSurface K` with respect to `surfaceHaar K`:

* `integrableOn_mul_surfaceScale`: integrability on `D` whenever `w` is continuous on
  `normOneSurface K` and `g` is continuous on the positive orthant.
* `continuousOn_const_mul_integral_surfaceScale`: continuity on `(0, ∞)` of the radial family
  `u ↦ A * ∫ x in D, w x * g (surfaceScale x (u / lam)) ∂surfaceHaar K`.
* `exists_norm_mul_integral_surfaceScale_sub_le`: transfer of a uniform stretched-exponential
  decay bound on `g (surfaceScale x u) - ε` through the surface integral and radial rescaling.

Both integrability and local continuity follow by enclosing `Subtype.val ⁻¹' D` in a compact
box inside `normOneSurface K` via `exists_isCompact_superset_preimage`.
-/

public section

noncomputable section

open Filter MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- A continuous surface weight `w` multiplied by a positive-orthant continuous function
`g (surfaceScale x t)` is integrable over any bounded surface set `D` for `t > 0`. -/
theorem integrableOn_mul_surfaceScale {w : normOneSurface K → ℂ} {g : realSpace K → ℂ}
    (hwc : Continuous w)
    (hg : ∀ {y₀ : realSpace K}, (∀ w, 0 < y₀ w) → ContinuousAt g y₀)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : normOneSurface K ↦ w x * g (surfaceScale (x : realSpace K) t))
      (Subtype.val ⁻¹' D) (surfaceHaar K) := by
  obtain ⟨S, hS, hsub⟩ := exists_isCompact_superset_preimage hD
  have : IsFiniteMeasure ((surfaceHaar K).restrict (Subtype.val ⁻¹' D)) :=
    isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  have hcont : Continuous fun x : normOneSurface K ↦ w x * g (surfaceScale (x : realSpace K) t) :=
    hwc.mul (continuous_comp_surfaceScale hg ht)
  have hint := hcont.continuousOn.integrableOn_compact
    (μ := (surfaceHaar K).restrict (Subtype.val ⁻¹' D)) hS
  rwa [IntegrableOn, Measure.restrict_restrict hS.measurableSet,
    Set.inter_eq_right.mpr hsub] at hint

open scoped Classical in
/-- Continuity on `(0, ∞)` of `u ↦ A * ∫ x in D, w x * g (surfaceScale x (u / lam)) d*x` for a
bounded surface set `D`, continuous surface weight `w`, and positive-orthant continuous function
`g`. -/
theorem continuousOn_const_mul_integral_surfaceScale (A : ℂ) {w : normOneSurface K → ℂ}
    {g : realSpace K → ℂ} (hwc : Continuous w)
    (hg : ∀ {y₀ : realSpace K}, (∀ w, 0 < y₀ w) → ContinuousAt g y₀)
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (fun u ↦ A * ∫ x in Subtype.val ⁻¹' D,
      w x * g (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K) (Set.Ioi 0) := by
  obtain ⟨S, hS, hsub⟩ := exists_isCompact_superset_preimage hD
  let μ := (surfaceHaar K).restrict (Subtype.val ⁻¹' D)
  have : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (surfaceHaar_preimage_lt_top hD).ne
  have : LocallyCompactSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  have hμS : μ.restrict S = μ := by
    rw [Measure.restrict_restrict hS.measurableSet, Set.inter_eq_right.mpr hsub]
  let F : Set.Ioi (0 : ℝ) → normOneSurface K → ℂ := fun u x ↦
    w x * g (surfaceScale (x : realSpace K) ((u : ℝ) / lam))
  have hF : Continuous F.uncurry := by
    refine (hwc.comp continuous_snd).mul ?_
    rw [continuous_iff_continuousAt]
    rintro ⟨u, x⟩
    have hu : ContinuousAt (fun p : Set.Ioi (0 : ℝ) × normOneSurface K ↦
        surfaceScale (p.2 : realSpace K) ((p.1 : ℝ) / lam)) (u, x) :=
      (continuous_surfaceScale.comp ((continuous_subtypeVal.comp continuous_snd).prodMk
        ((continuous_subtypeVal.comp continuous_fst).div_const lam))).continuousAt
    exact ContinuousAt.comp' (g := g)
      (hg (surfaceScale_pos (mem_normOneSurface.mp x.property).1 (div_pos u.property hlam))) hu
  have hcont : Continuous fun u : Set.Ioi (0 : ℝ) ↦ ∫ x in S, F u x ∂μ :=
    continuous_parametric_integral_of_continuous hF hS
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Set.Ioi (0 : ℝ)).domRestrict (fun u ↦ A * ∫ x in Subtype.val ⁻¹' D,
      w x * g (surfaceScale (x : realSpace K) (u / lam)) ∂surfaceHaar K) =
      fun u : Set.Ioi (0 : ℝ) ↦ A * ∫ x in S, F u x ∂μ := by
    ext u
    simp only [Set.domRestrict_apply, F, μ, hμS]
  rw [heq]
  exact continuous_const.mul hcont

open scoped Classical in
/-- Transfer a uniform stretched-exponential decay bound on `g (surfaceScale x u) - ε` over a
bounded surface set `D` through the surface integral against a bounded weight `w` and radial
level `lam > 0`. -/
theorem exists_norm_mul_integral_surfaceScale_sub_le
    {w : normOneSurface K → ℂ} {g : realSpace K → ℂ} {ε : ℂ}
    {D : Set (realSpace K)} (hD : Bornology.IsBounded D)
    (hw : ∃ W ≥ 0, ∀ x : normOneSurface K, (x : realSpace K) ∈ D → ‖w x‖ ≤ W)
    (hg : ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop, ∀ x ∈ D ∩ normOneSurface K,
      ‖g (surfaceScale x u) - ε‖ ≤ C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹))
    (A : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c > 0, ∃ C ≥ 0, ∀ᶠ u : ℝ in atTop,
      ‖A * ∫ x in Subtype.val ⁻¹' D,
        w x * (g (surfaceScale (x : realSpace K) (u / lam)) - ε) ∂surfaceHaar K‖ ≤
        C * Real.exp (-c * u ^ (Module.finrank ℚ K : ℝ)⁻¹) := by
  set n : ℝ := (Module.finrank ℚ K : ℝ)⁻¹
  set S : Set (normOneSurface K) := Subtype.val ⁻¹' D
  have hfin : surfaceHaar K S < ⊤ := surfaceHaar_preimage_lt_top hD
  obtain ⟨W, hW, hWx⟩ := hw
  obtain ⟨c, hc, C, _, h⟩ := hg
  let F : ℝ → ℂ := fun t ↦ A * ∫ x in S,
    w x * (g (surfaceScale (x : realSpace K) t) - ε) ∂surfaceHaar K
  have hO : F =O[atTop] fun t ↦ Real.exp (-c * t ^ n) := by
    refine Asymptotics.IsBigO.of_bound (‖A‖ * (W * C * (surfaceHaar K).real S)) ?_
    filter_upwards [h] with t ht
    have hnorm (x : normOneSurface K) (hx : x ∈ S) :
        ‖w x * (g (surfaceScale (x : realSpace K) t) - ε)‖ ≤ W * C * Real.exp (-c * t ^ n) := by
      rw [norm_mul]
      calc ‖w x‖ * ‖g (surfaceScale (x : realSpace K) t) - ε‖
          ≤ W * (C * Real.exp (-c * t ^ n)) :=
            mul_le_mul (hWx x hx) (ht x ⟨hx, x.property⟩) (norm_nonneg _) hW
        _ = W * C * Real.exp (-c * t ^ n) := by ring
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    dsimp only [F]
    rw [norm_mul]
    calc ‖A‖ * ‖∫ x in S, w x * (g (surfaceScale (x : realSpace K) t) - ε) ∂surfaceHaar K‖
        ≤ ‖A‖ * (W * C * Real.exp (-c * t ^ n) * (surfaceHaar K).real S) :=
          mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin hnorm)
            (norm_nonneg _)
      _ = ‖A‖ * (W * C * (surfaceHaar K).real S) * Real.exp (-c * t ^ n) := by ring
  obtain ⟨C', hC', hbound⟩ := (isBigO_comp_div_exp_neg_mul_rpow hlam hO).exists_nonneg
  refine ⟨c / lam ^ n, by positivity, C', hC', ?_⟩
  filter_upwards [hbound.bound] with u hu
  simpa only [F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hu

end TauCeti.LFunctions
