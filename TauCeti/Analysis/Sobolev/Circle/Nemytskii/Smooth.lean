/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Nemytskii.Bootstrap
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.Hadamard
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.MeasureTheory.Constructions.UnitInterval

/-!
# Smooth Nemytskii maps on the circle Sobolev spaces

Building on `TauCeti/Analysis/Sobolev/Circle/Nemytskii/Bootstrap.lean`, this file proves local
Lipschitz bounds, strict Fréchet differentiability, and `C^k` / `C^∞` smoothness of
`u ↦ nemytskii f u` on `{u ∈ H^s(E) | ∀ x, u x ∈ U}` (`s > 1/2`) for finite-dimensional complex
normed spaces `E` and `F`. Lifting `f y - f x = hadamardFactor f x y (y - x)` via
`TauCeti.CircleSobolev.realConvolution` expresses `nemytskii f u₂ - nemytskii f u₁` as a bounded
bilinear product against `u₂ - u₁`, yielding local Lipschitz continuity, `HasStrictFDerivAt` from
continuity at the diagonal `(u₀, u₀)`, and `C^k` / `C^∞` regularity by induction on `k`.

## Main statements

* `TauCeti.CircleSobolev.exists_lipschitzOnWith_nemytskii` and
  `TauCeti.CircleSobolev.continuousOn_nemytskii`: local Lipschitz continuity and continuity
  (`⌊2s⌋₊ + 1 ≤ n`).
* `TauCeti.CircleSobolev.hasStrictFDerivAt_nemytskii_of_contDiffOn` and
  `TauCeti.CircleSobolev.toContinuousMap_fderiv_nemytskii_of_contDiffOn`: strict Fréchet
  differentiability and pointwise derivative formula (`⌊2s⌋₊ + 2 ≤ n`).
* `TauCeti.CircleSobolev.contDiffOn_nemytskii` and `TauCeti.CircleSobolev.contDiff_nemytskii`:
  `C^∞` smoothness on `{u ∈ H^s(E) | ∀ x, u x ∈ U}` and globally on `H^s(E)`.

## References

* R. S. Palais, *Foundations of Global Non-Linear Analysis*, W. A. Benjamin, 1968, Chapter 9.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699.
-/

public section

noncomputable section

open MeasureTheory Complex Filter Set
open scoped ContDiff ENNReal NNReal Real Topology

universe u v

namespace TauCeti

namespace CircleSobolev

attribute [local instance] instCompleteSpaceOfFiniteDimensional

/-! ### Hadamard factorization, strict Fréchet differentiability, and `C^∞` smoothness -/

section Smoothness

private def segmentPreimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set E) :
    Set (E × E) :=
  {p : E × E | ∀ τ : unitInterval, p.1 + (τ : ℝ) • (p.2 - p.1) ∈ U}

private theorem isOpen_segmentPreimage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) : IsOpen (segmentPreimage U) :=
  isOpen_forall_prodMk_mem continuous_subtype_val
    (hU.preimage (by fun_prop : Continuous fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)))

private theorem mem_segmentPreimage_diag {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {x : E} (hx : x ∈ U) : (x, x) ∈ segmentPreimage U := fun _ ↦ by simpa using hx

private theorem contDiffOn_uncurry_hadamardFactor {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) f U) :
    ContDiffOn ℝ (m : ℕ∞ω) (Function.uncurry (hadamardFactor f)) (segmentPreimage U) := by
  have hseg : ContDiff ℝ (m : ℕ∞)
      (fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)) := by fun_prop
  have hd : ContDiffOn ℝ (m : ℕ∞) (fderiv ℝ f) U := by
    exact_mod_cast hf.fderiv_of_isOpen hU (m := (m : ℕ∞ω)) (by norm_cast)
  have hint := contDiffOn_integral_smul_of_contDiffOn (μ := (volume : Measure unitInterval))
    (U := segmentPreimage U) (integrable_const (1 : ℝ)) continuous_subtype_val
    (hU.preimage (by fun_prop : Continuous fun q : (E × E) × ℝ ↦ q.1.1 + q.2 • (q.1.2 - q.1.1)))
    (hd.comp hseg.contDiffOn fun _ h ↦ h) fun p hp τ ↦ hp τ
  exact_mod_cast hint.congr fun ⟨x, y⟩ _ ↦ by
    change hadamardFactor f x y = _
    rw [congrFun (hadamardFactor_eq_integral_Icc f x) y, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral_eq_integral_unitInterval]
    simp only [Function.comp_apply, one_smul]

private theorem sub_eq_hadamardFactor_apply_of_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ 1 f U)
    {p : E × E} (hp : p ∈ segmentPreimage U) :
    f p.2 - f p.1 = hadamardFactor f p.1 p.2 (p.2 - p.1) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (f := f) (x := p.1)
    (y := p.2 - p.1) fun τ hτ ↦ hf.contDiffAt (hU.mem_nhds (hp ⟨τ, hτ⟩))
  have hInt : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (p.1 + t • (p.2 - p.1))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hf.continuousOn_fderiv_of_isOpen hU le_rfl).comp
      (by fun_prop : Continuous fun t : ℝ ↦ p.1 + t • (p.2 - p.1)).continuousOn
      fun t ht ↦ hp ⟨t, ht⟩
  rw [congrFun (hadamardFactor_eq_integral_Icc f p.1) p.2, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    ContinuousLinearMap.intervalIntegral_apply hInt (p.2 - p.1)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

variable (T : ℝ) [hT : Fact (0 < T)] {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem nemytskii_sub_eq_realConvolution_hadamardFactor {U : Set E} (hU : IsOpen U)
    {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U)
    (u₁ u₂ : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hseg : ∀ x, (toContinuousMap T hs.out u₁ x, toContinuousMap T hs.out u₂ x) ∈
      segmentPreimage U) :
    nemytskii f u₂ - nemytskii f u₁ =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F))
        (nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₁, u₂)))
        (u₂ - u₁) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have : FiniteDimensional ℂ (E × E) := inferInstance
  have hu₁ (x : AddCircle T) : toContinuousMap T hs.out u₁ x ∈ U := by
    simpa only [Subtype.coe_mk, zero_smul, add_zero] using hseg x ⟨0, unitInterval.zero_mem⟩
  have hu₂ (x : AddCircle T) : toContinuousMap T hs.out u₂ x ∈ U := by
    simpa only [Subtype.coe_mk, one_smul, add_sub_cancel] using hseg x ⟨1, unitInterval.one_mem⟩
  have hp12 (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]; exact hseg y
  have hn0 : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hn1 : (1 : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hH := contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [map_sub, ContinuousMap.sub_apply,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu₂ hn0 x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf hu₁ hn0 x,
    toContinuousMap_realConvolution_apply,
    toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp12 le_rfl x,
    map_sub (toContinuousMap T hs.out) u₂ u₁, ContinuousMap.sub_apply]
  simp only [toContinuousMap_prodEquiv_symm_apply, Function.uncurry_apply_pair,
    ContinuousLinearMap.id_apply]
  exact sub_eq_hadamardFactor_apply_of_contDiffOn hU (hf.of_le hn1) (hseg x)

private theorem nemytskii_hadamardFactor_diag {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (u₀ : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U) :
    nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₀, u₀)) =
      nemytskii (fderiv ℝ f) u₀ := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hH := contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)
  have hdf : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (fderiv ℝ f) U :=
    (hf.of_le hn).fderiv_of_isOpen hU (m := (⌊2 * s⌋₊ : ℕ∞ω)) (by norm_cast)
  have hp₀ (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]; exact mem_segmentPreimage_diag (hu₀ y)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp₀ le_rfl x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hdf hu₀ le_rfl x]
  simp [toContinuousMap_prodEquiv_symm_apply, hadamardFactor_self]

private theorem exists_ball_prodEquiv_symm_mem_cthickening (u₀ : CircleSobolev s E)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ⦃u₁ u₂ : CircleSobolev s E⦄,
      u₁ ∈ Metric.ball u₀ r → u₂ ∈ Metric.ball u₀ r →
        (∀ x, toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) x ∈
          Metric.cthickening δ (Set.range (toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀))))) ∧
        ‖prodEquiv.symm (u₁, u₂)‖ ≤ ‖prodEquiv.symm (u₀, u₀)‖ + 1 := by
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  have hnhds : prodEquiv.symm ⁻¹' (Metric.ball p₀ 1 ∩
      (toContinuousMap T hs.out) ⁻¹' Metric.ball (toContinuousMap T hs.out p₀) δ) ∈
      𝓝 (u₀, u₀) :=
    prodEquiv.symm.continuous.continuousAt.preimage_mem_nhds <| Filter.inter_mem
      (Metric.ball_mem_nhds p₀ one_pos)
      ((toContinuousMap T hs.out).continuous.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hδ))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨r, hr, fun u₁ u₂ hu₁ hu₂ ↦ ?_⟩
  have hmem : (u₁, u₂) ∈ Metric.ball (u₀, u₀) r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.1 hu₁) (Metric.mem_ball.1 hu₂)
  obtain ⟨h1, h2⟩ := hsub hmem
  rw [Metric.mem_ball, dist_eq_norm] at h1
  refine ⟨fun x ↦ Metric.mem_cthickening_of_dist_le _ _ δ _ ⟨x, rfl⟩
    ((ContinuousMap.dist_apply_le_dist x).trans (Metric.mem_ball.1 h2).le), ?_⟩
  linarith [norm_le_norm_sub_add (prodEquiv.symm (u₁, u₂)) p₀]

/-- **Local Lipschitz continuity of `nemytskii f`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 1 ≤ n` and `u₀ ∈ H^s(E)` maps into `U`, then `nemytskii f` is Lipschitz on a ball
around `u₀` inside `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem exists_lipschitzOnWith_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ∃ (r : ℝ) (L : ℝ≥0), 0 < r ∧
      Metric.ball u₀ r ⊆ {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} ∧
      LipschitzOnWith L (nemytskii (s := s) f) (Metric.ball u₀ r) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  set K₀ := Set.range (toContinuousMap T hs.out p₀)
  have hK₀ : IsCompact K₀ := isCompact_range (toContinuousMap T hs.out p₀).continuous
  have hK₀_sub : K₀ ⊆ segmentPreimage U := by
    rintro _ ⟨x, rfl⟩
    change toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) x ∈ segmentPreimage U
    rw [toContinuousMap_prodEquiv_symm_apply]; exact mem_segmentPreimage_diag (hu₀ x)
  obtain ⟨δ, hδ, hKδ_sub⟩ := hK₀.exists_cthickening_subset_open (isOpen_segmentPreimage hU) hK₀_sub
  obtain ⟨B, hB, hB_bound⟩ := exists_norm_nemytskii_le_of_isCompact T (isOpen_segmentPreimage hU)
    (contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)) hK₀.cthickening hKδ_sub (‖p₀‖ + 1) le_rfl
  obtain ⟨r, hr, hmem_Kδ⟩ := exists_ball_prodEquiv_symm_mem_cthickening T u₀ hδ
  let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  refine ⟨r, ⟨‖A‖ * B, mul_nonneg (norm_nonneg A) hB⟩, hr, fun u hu x ↦ ?_,
    LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_⟩
  · have hseg : (toContinuousMap T hs.out u x, toContinuousMap T hs.out u x) ∈ segmentPreimage U :=
      by simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub ((hmem_Kδ hu hu).1 x)
    simpa only [Subtype.coe_mk, zero_smul, add_zero] using hseg ⟨0, unitInterval.zero_mem⟩
  · obtain ⟨hK12, hN12⟩ := hmem_Kδ hu₂ hu₁
    have hseg12 (x : AddCircle T) :
        (toContinuousMap T hs.out u₂ x, toContinuousMap T hs.out u₁ x) ∈ segmentPreimage U := by
      simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub (hK12 x)
    rw [dist_eq_norm, dist_eq_norm,
      nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn hseg12]
    exact (A.le_opNorm₂ _ _).trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB_bound _ hK12 hN12) (norm_nonneg A)) (norm_nonneg _)

/-- **Continuity of `nemytskii f` on `H^s(E)`.** If `f : E → F` is `C^n` on an open set `U` with
`⌊2s⌋₊ + 1 ≤ n`, then `nemytskii f` is continuous on `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem continuousOn_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContinuousOn (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := fun u₀ hu₀ ↦
  let ⟨_, _, hr, _, hLip⟩ := exists_lipschitzOnWith_nemytskii T hU hf hu₀ hn
  (hLip.continuousOn.continuousAt (Metric.ball_mem_nhds u₀ hr)).continuousWithinAt

/-- Global version of `continuousOn_nemytskii` for `f : E → F` of class `C^n`
(`⌊2s⌋₊ + 1 ≤ n`). -/
theorem continuous_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    Continuous (nemytskii (s := s) f) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  continuousOn_univ.1
    ((continuousOn_nemytskii 1 isOpen_univ hf.contDiffOn hn).mono fun _ _ _ ↦ mem_univ _)

/-- **Strict Fréchet derivative of `nemytskii f`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 2 ≤ n` (in particular if `f` is `C^∞`) and `u₀ ∈ H^s(E)` takes values in `U`, then
`nemytskii f` is strictly Fréchet differentiable at `u₀`, with derivative
`v ↦ realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u₀) v`. -/
theorem hasStrictFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u₀)) u₀ := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  let H := Function.uncurry (hadamardFactor f)
  let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  let ΩH : Set (CircleSobolev s (E × E)) :=
    {w | ∀ x, toContinuousMap T hs.out w x ∈ segmentPreimage U}
  have hΩH_open : IsOpen ΩH :=
    isOpen_setOf_forall_toContinuousMap_mem T hs.out (isOpen_segmentPreimage hU)
  have hp₀_mem : p₀ ∈ ΩH := fun x ↦ by
    change toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) x ∈ segmentPreimage U
    rw [toContinuousMap_prodEquiv_symm_apply]; exact mem_segmentPreimage_diag (hu₀ x)
  have hswap : Continuous (fun q : CircleSobolev s E × CircleSobolev s E ↦
      prodEquiv.symm (q.2, q.1)) :=
    prodEquiv.symm.continuous.comp (continuous_snd.prodMk continuous_fst)
  have hH_contAt : ContinuousAt (nemytskii (s := s) H) p₀ :=
    (continuousOn_nemytskii T (isOpen_segmentPreimage hU)
      (contDiffOn_uncurry_hadamardFactor hU (hf.of_le hn)) le_rfl).continuousAt
      (hΩH_open.mem_nhds hp₀_mem)
  have hdiff_tendsto : Tendsto
      (fun q : CircleSobolev s E × CircleSobolev s E ↦
        ‖A‖ * ‖nemytskii H (prodEquiv.symm (q.2, q.1)) - nemytskii H p₀‖)
      (𝓝 (u₀, u₀)) (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.2
      (hH_contAt.tendsto.comp (hswap.tendsto (u₀, u₀)))).norm.const_mul ‖A‖
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hswap.tendsto (u₀, u₀) (hΩH_open.mem_nhds hp₀_mem),
    (tendsto_order.1 hdiff_tendsto).2 c hc] with ⟨u₁, u₂⟩ hseg hc_lt
  have hseg21 (x : AddCircle T) :
      (toContinuousMap T hs.out u₂ x, toContinuousMap T hs.out u₁ x) ∈ segmentPreimage U := by
    simpa only [toContinuousMap_prodEquiv_symm_apply] using hseg x
  have hn1 : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  dsimp only
  rw [nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn1 hseg21,
    ← nemytskii_hadamardFactor_diag T hU hf u₀ hn1 hu₀, ← sub_apply, ← map_sub]
  exact (A.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right hc_lt.le (norm_nonneg _))

/-- Global version of `hasStrictFDerivAt_nemytskii_of_contDiffOn` for `f : E → F` of class `C^n`
(`⌊2s⌋₊ + 2 ≤ n`). -/
theorem hasStrictFDerivAt_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  hasStrictFDerivAt_nemytskii_of_contDiffOn 1 isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _) hn

/-- **Fréchet derivative of `nemytskii f` on an open set.** -/
theorem hasFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).hasFDerivAt

/-- Global Fréchet derivative of `nemytskii f`. -/
theorem hasFDerivAt_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii hf u hn).hasFDerivAt

/-- Formula for `fderiv ℝ (nemytskii f) u` when `u` takes values in an open set `U` where `f` is
`C^n` (`⌊2s⌋₊ + 2 ≤ n`). -/
theorem fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).fderiv

/-- Global formula for `fderiv ℝ (nemytskii f) u`. -/
theorem fderiv_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiff hf u hn).fderiv

/-- Pointwise action of `fderiv ℝ (nemytskii f) u v` on continuous representatives: at every point
`x : AddCircle T`, `(d(nemytskii f)_u v)(x) = df_{u(x)}(v(x))`. -/
theorem toContinuousMap_fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (v : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (fderiv ℝ (nemytskii (s := s) f) u v) x =
      fderiv ℝ f (toContinuousMap T hs.out u x) (toContinuousMap T hs.out v x) := by
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  have : FiniteDimensional ℂ (E →L[ℝ] F) := ContinuousLinearMap.finiteDimensional_of_isScalarTower
  have hn1 : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hdf : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (fderiv ℝ f) U :=
    (hf.of_le hn1).fderiv_of_isOpen hU (m := (⌊2 * s⌋₊ : ℕ∞ω)) (by norm_cast)
  rw [fderiv_nemytskii_of_contDiffOn T hU hf hu hn, toContinuousMap_realConvolution_apply,
    ContinuousLinearMap.id_apply, toContinuousMap_nemytskii_of_contDiffOn T hU hdf hu le_rfl x]

/-- Global pointwise action of `fderiv ℝ (nemytskii f) u v` on continuous representatives. -/
theorem toContinuousMap_fderiv_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u v : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (fderiv ℝ (nemytskii (s := s) f) u v) x =
      fderiv ℝ f (toContinuousMap T hs.out u x) (toContinuousMap T hs.out v x) :=
  toContinuousMap_fderiv_nemytskii_of_contDiffOn T isOpen_univ hf.contDiffOn
    (fun _ ↦ mem_univ _) v hn x

private theorem contDiffOn_nemytskii_nat_aux :
    ∀ (k : ℕ) {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
      {U : Set E} (_hU : IsOpen U) {n : ℕ∞ω} {f : E → F'} (_hf : ContDiffOn ℝ n f U)
      (_hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n),
      ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
        {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U}
  | 0, F', _, _, _, U, hU, _, f, hf, hn =>
      contDiffOn_zero.2 (continuousOn_nemytskii T hU hf (by simpa using hn))
  | k + 1, F', _, _, _, U, hU, n, f, hf, hn => by
      have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
      have : FiniteDimensional ℂ (E →L[ℝ] F') :=
        ContinuousLinearMap.finiteDimensional_of_isScalarTower
      let Ω := {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U}
      have hΩ : IsOpen Ω := isOpen_setOf_forall_toContinuousMap_mem T hs.out hU
      have hn2 : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
      push_cast
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hΩ).2 ⟨fun u hu ↦
        (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn2).differentiableAt
          |>.differentiableWithinAt,
        by simp, ?_⟩
      have hdf : ContDiffOn ℝ ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) (fderiv ℝ f) U :=
        (hf.of_le hn).fderiv_of_isOpen hU (m := ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω)) (by norm_cast)
      exact ((realConvolution hs.out (.id ℝ (E →L[ℝ] F'))).contDiff.comp_contDiffOn
        (contDiffOn_nemytskii_nat_aux k hU hdf le_rfl)).congr fun u hu ↦
          fderiv_nemytskii_of_contDiffOn T hU hf hu hn2

/-- **`C^k` regularity of `nemytskii f` on `H^s(E)`.** If `f : E → F` is `C^n` on an open set `U`
with `⌊2s⌋₊ + 1 + k ≤ n`, then `nemytskii f` is `C^k` on `{u ∈ H^s(E) | ∀ x, u x ∈ U}`. -/
theorem contDiffOn_nemytskii_nat (k : ℕ) {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  let eF : F ≃L[ℂ] (ULift.{u} (Fin (Module.finrank ℂ F)) → ℂ) :=
    ((Module.finBasis ℂ F).reindex Equiv.ulift.symm).equivFun.toContinuousLinearEquiv
  let L := eF.symm.toContinuousLinearMap
  have hf' : ContDiffOn ℝ n (eF ∘ f) U :=
    (eF.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have hn0 : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  refine (((mapCLM (s := s) L).restrictScalars ℝ).contDiff.comp_contDiffOn
    (contDiffOn_nemytskii_nat_aux T k hU hf' hn)).congr fun u hu ↦ ?_
  refine nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ ?_
  rw [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    toContinuousMap_mapCLM_apply T hs.out L _ x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf' hu hn0 x]
  exact eF.symm_apply_apply (f (toContinuousMap T hs.out u x))

/-- Global `C^k` regularity of `nemytskii f` when `f : E → F` is `C^n` (`⌊2s⌋₊ + 1 + k ≤ n`). -/
theorem contDiff_nemytskii_nat (k : ℕ) {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiff ℝ (k : ℕ∞ω) (nemytskii (s := s) f) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  contDiffOn_univ.1
    ((contDiffOn_nemytskii_nat 1 k isOpen_univ hf.contDiffOn hn).mono fun _ _ _ ↦ mem_univ _)

/-- **`C^∞` smoothness of `nemytskii f` on open subsets of `H^s(E)`.** If `f : E → F` is smooth
on an open set `U ⊆ E`, then `u ↦ nemytskii f u` is smooth (`ContDiffOn ℝ ∞`) on the open subset
`{u ∈ H^s(E) | ∀ x, u x ∈ U}` for every `s > 1/2`. -/
theorem contDiffOn_nemytskii {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} :=
  contDiffOn_infty.2 fun k ↦ contDiffOn_nemytskii_nat T k hU hf (by simp)

/-- **Global `C^∞` smoothness of `nemytskii f` on `H^s(E)`.** If `f : E → F` is smooth on `E`,
then `u ↦ nemytskii f u` is smooth (`ContDiff ℝ ∞`) on `H^s(E)` for every `s > 1/2`. -/
theorem contDiff_nemytskii {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nemytskii (s := s) f) :=
  contDiff_infty.2 fun k ↦ contDiff_nemytskii_nat k hf (by simp)

end Smoothness

end CircleSobolev

end TauCeti
