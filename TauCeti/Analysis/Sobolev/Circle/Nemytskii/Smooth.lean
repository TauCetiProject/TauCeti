/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Nemytskii.Bootstrap
import TauCeti.Analysis.Calculus.Hadamard.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth Nemytskii maps on the circle Sobolev spaces

Building on `TauCeti/Analysis/Sobolev/Circle/Nemytskii/Bootstrap.lean`, this file proves local
Lipschitz bounds, strict Fréchet differentiability, and `C^k` / `C^∞` smoothness of
`u ↦ nemytskii f u` on `{u ∈ H^s(E) | ∀ x, u x ∈ U}` (`s > 1/2`) for finite-dimensional complex
normed spaces `E` and `F`. Lifting `f y - f x = hadamardFactor f x y (y - x)` via
`CircleSobolev.realConvolution` expresses `nemytskii f u₂ - nemytskii f u₁` as a bounded bilinear
product against `u₂ - u₁`, giving local Lipschitz continuity, `HasStrictFDerivAt` from continuity at
`(u₀, u₀)`, and `C^k` / `C^∞` regularity by induction on `k`.

## Main statements

* `TauCeti.CircleSobolev.exists_lipschitzOnWith_nemytskii`, `continuousOn_nemytskii`,
  `hasStrictFDerivAt_nemytskii_of_contDiffOn`, `toContinuousMap_fderiv_nemytskii_of_contDiffOn`,
  `contDiffOn_nemytskii`, and `contDiff_nemytskii`.

## References

* R. S. Palais, *Foundations of Global Non-Linear Analysis*, W. A. Benjamin, 1968, Chapter 9.
* J. W. Robbin and D. A. Salamon, *J. Eur. Math. Soc.* **8** (2006), 611–699.
-/

public section
noncomputable section

open MeasureTheory Complex Filter Set
open scoped ContDiff ENNReal NNReal Real Topology

universe u v

namespace TauCeti
namespace CircleSobolev

attribute [local instance] instCompleteSpaceOfFiniteDimensional
private instance {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G] :
    FiniteDimensional ℝ G := Module.Finite.trans ℂ G
private instance {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [FiniteDimensional ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂] :
    FiniteDimensional ℂ (G₁ →L[ℝ] G₂) :=
  ContinuousLinearMap.finiteDimensional_of_smulCommClass

section Smoothness

variable (T : ℝ) [hT : Fact (0 < T)] {s : ℝ} [hs : Fact (1 / 2 < s)]
  {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

private theorem nemytskii_sub_eq_realConvolution_hadamardFactor {U : Set E} (hU : IsOpen U)
    {n : ℕ∞ω} {f : E → F} (hf : ContDiffOn ℝ n f U) (u₁ u₂ : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hseg : ∀ x, (toContinuousMap T hs.out u₁ x, toContinuousMap T hs.out u₂ x) ∈
      segmentPreimage U) :
    nemytskii f u₂ - nemytskii f u₁ = realConvolution hs.out (.id ℝ (E →L[ℝ] F))
      (nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₁, u₂))) (u₂ - u₁) := by
  have hp12 (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]; exact hseg y
  have hn0 : (⌊2 * s⌋₊ : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  have hH := contDiffOn_uncurry_hadamardFactor hU (m := ⌊2 * s⌋₊) (by exact_mod_cast hf.of_le hn)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [map_sub, ContinuousMap.sub_apply,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf
      (fun y ↦ snd_mem_of_mem_segmentPreimage (hseg y)) hn0 x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf
      (fun y ↦ fst_mem_of_mem_segmentPreimage (hseg y)) hn0 x,
    toContinuousMap_realConvolution_apply,
    toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp12 (by simp) x,
    map_sub (toContinuousMap T hs.out) u₂ u₁, ContinuousMap.sub_apply]
  simp only [toContinuousMap_prodEquiv_symm_apply, Function.uncurry_apply_pair,
    ContinuousLinearMap.id_apply]
  exact sub_eq_hadamardFactor_apply_of_contDiffOn hU
    (hf.of_le (le_trans (by norm_cast; omega) hn)) (hseg x)

private theorem nemytskii_hadamardFactor_diag {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (u₀ : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U) :
    nemytskii (Function.uncurry (hadamardFactor f)) (prodEquiv.symm (u₀, u₀)) =
      nemytskii (fderiv ℝ f) u₀ := by
  have hH := contDiffOn_uncurry_hadamardFactor hU (m := ⌊2 * s⌋₊) (by exact_mod_cast hf.of_le hn)
  have hdf : ContDiffOn ℝ (⌊2 * s⌋₊ : ℕ∞ω) (fderiv ℝ f) U :=
    (hf.of_le hn).fderiv_of_isOpen hU (m := (⌊2 * s⌋₊ : ℕ∞ω)) (by norm_cast)
  have hp₀ (y : AddCircle T) :
      toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀)) y ∈ segmentPreimage U := by
    rw [toContinuousMap_prodEquiv_symm_apply]; exact mem_segmentPreimage_diag (hu₀ y)
  refine toContinuousMap_injective T hs.out <| ContinuousMap.ext fun x ↦ ?_
  rw [toContinuousMap_nemytskii_of_contDiffOn T (isOpen_segmentPreimage hU) hH hp₀ (by simp) x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hdf hu₀ le_rfl x]
  simp [toContinuousMap_prodEquiv_symm_apply, hadamardFactor_self]

private theorem exists_ball_prodEquiv_symm_mem_cthickening (u₀ : CircleSobolev s E) {δ : ℝ}
    (hδ : 0 < δ) : ∃ r : ℝ, 0 < r ∧ ∀ ⦃u₁ u₂ : CircleSobolev s E⦄,
      u₁ ∈ Metric.ball u₀ r → u₂ ∈ Metric.ball u₀ r →
        (∀ x, toContinuousMap T hs.out (prodEquiv.symm (u₁, u₂)) x ∈
          Metric.cthickening δ (Set.range (toContinuousMap T hs.out (prodEquiv.symm (u₀, u₀))))) ∧
        ‖prodEquiv.symm (u₁, u₂)‖ ≤ ‖prodEquiv.symm (u₀, u₀)‖ + 1 := by
  let p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀)
  have hnhds : prodEquiv.symm ⁻¹' (Metric.ball p₀ 1 ∩
      (toContinuousMap T hs.out) ⁻¹' Metric.ball (toContinuousMap T hs.out p₀) δ) ∈ 𝓝 (u₀, u₀) :=
    prodEquiv.symm.continuous.continuousAt.preimage_mem_nhds <| Filter.inter_mem
      (Metric.ball_mem_nhds p₀ one_pos)
      ((toContinuousMap T hs.out).continuous.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hδ))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 hnhds; refine ⟨r, hr, fun u₁ u₂ hu₁ hu₂ ↦ ?_⟩
  have hball : (u₁, u₂) ∈ Metric.ball (u₀, u₀) r := by
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.1 hu₁) (Metric.mem_ball.1 hu₂)
  obtain ⟨h1, h2⟩ := hsub hball
  rw [Metric.mem_ball, dist_eq_norm] at h1
  exact ⟨fun x ↦ Metric.mem_cthickening_of_dist_le _ _ δ _ ⟨x, rfl⟩
    ((ContinuousMap.dist_apply_le_dist x).trans (Metric.mem_ball.1 h2).le),
    by linarith [norm_le_norm_sub_add (prodEquiv.symm (u₁, u₂)) p₀]⟩

/-- **Local Lipschitz continuity of `nemytskii f` (`⌊2s⌋₊ + 1 ≤ n`).** -/
theorem exists_lipschitzOnWith_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ∃ (r : ℝ) (L : ℝ≥0), 0 < r ∧
      Metric.ball u₀ r ⊆ {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} ∧
      LipschitzOnWith L (nemytskii (s := s) f) (Metric.ball u₀ r) := by
  set p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀) with hp₀
  set K₀ := Set.range (toContinuousMap T hs.out p₀)
  have hK₀ : IsCompact K₀ := isCompact_range (toContinuousMap T hs.out p₀).continuous
  have hK₀_sub : K₀ ⊆ segmentPreimage U := by
    rintro _ ⟨x, rfl⟩; rw [hp₀, toContinuousMap_prodEquiv_symm_apply]
    exact mem_segmentPreimage_diag (hu₀ x)
  obtain ⟨δ, hδ, hKδ_sub⟩ := hK₀.exists_cthickening_subset_open (isOpen_segmentPreimage hU) hK₀_sub
  obtain ⟨B, hB, hB_bound⟩ := exists_norm_nemytskii_le_of_isCompact T (s := s)
    (isOpen_segmentPreimage hU)
    (contDiffOn_uncurry_hadamardFactor hU (m := ⌊2 * s⌋₊) (by exact_mod_cast hf.of_le hn))
    hK₀.cthickening hKδ_sub (‖p₀‖ + 1) le_rfl
  obtain ⟨r, hr, hmem_Kδ⟩ := exists_ball_prodEquiv_symm_mem_cthickening T u₀ hδ
  let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  refine ⟨r, ⟨‖A‖ * B, mul_nonneg (norm_nonneg A) hB⟩, hr, fun u hu x ↦
    fst_mem_of_mem_segmentPreimage <| by
      simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub ((hmem_Kδ hu hu).1 x),
    LipschitzOnWith.of_dist_le_mul fun u₁ hu₁ u₂ hu₂ ↦ ?_⟩
  obtain ⟨hK12, hN12⟩ := hmem_Kδ hu₂ hu₁
  rw [dist_eq_norm, dist_eq_norm, nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn
    fun x ↦ by simpa only [toContinuousMap_prodEquiv_symm_apply] using hKδ_sub (hK12 x)]
  exact (A.le_opNorm₂ _ _).trans <| mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hB_bound _ hK12 hN12) (norm_nonneg A)) (norm_nonneg _)

/-- **Continuity of `nemytskii f` on `{u ∈ H^s(E) | ∀ x, u x ∈ U}` (`⌊2s⌋₊ + 1 ≤ n`).** -/
theorem continuousOn_nemytskii {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContinuousOn (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := fun u₀ hu₀ ↦
  let ⟨_, _, hr, _, hLip⟩ := exists_lipschitzOnWith_nemytskii T hU hf hu₀ hn
  (hLip.continuousOn.continuousAt (Metric.ball_mem_nhds u₀ hr)).continuousWithinAt

/-- Global version of `continuousOn_nemytskii` for `f : E → F` of class `C^n` (`⌊2s⌋₊ + 1 ≤ n`). -/
theorem continuous_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := by simp) : Continuous (nemytskii (s := s) f) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  continuousOn_univ.1 ((continuousOn_nemytskii 1 isOpen_univ hf.contDiffOn hn).mono
    fun _ _ _ ↦ mem_univ _)

/-- **Strict Fréchet derivative of `nemytskii f` (`⌊2s⌋₊ + 2 ≤ n`).** -/
theorem hasStrictFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u₀ : CircleSobolev s E}
    (hu₀ : ∀ x, toContinuousMap T hs.out u₀ x ∈ U)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u₀)) u₀ := by
  let H := Function.uncurry (hadamardFactor f); let A := realConvolution hs.out (.id ℝ (E →L[ℝ] F))
  set p₀ : CircleSobolev s (E × E) := prodEquiv.symm (u₀, u₀) with hp₀
  have hΩH_nhds : {w | ∀ x, toContinuousMap T hs.out w x ∈ segmentPreimage U} ∈ 𝓝 p₀ :=
    (isOpen_setOf_forall_toContinuousMap_mem T hs.out (isOpen_segmentPreimage hU)).mem_nhds fun x ↦
      by rw [hp₀, toContinuousMap_prodEquiv_symm_apply]; exact mem_segmentPreimage_diag (hu₀ x)
  have hswap : Continuous (fun q : CircleSobolev s E × CircleSobolev s E ↦
      prodEquiv.symm (q.2, q.1)) :=
    prodEquiv.symm.continuous.comp (continuous_snd.prodMk continuous_fst)
  have hH_contAt : ContinuousAt (nemytskii (s := s) H) p₀ :=
    (continuousOn_nemytskii T (isOpen_segmentPreimage hU)
      (contDiffOn_uncurry_hadamardFactor hU (m := (⌊2 * s⌋₊ + 1 : ℕ))
        (by exact_mod_cast hf.of_le hn))).continuousAt hΩH_nhds
  have hdiff_tendsto : Tendsto (fun q : CircleSobolev s E × CircleSobolev s E ↦
      ‖A‖ * ‖nemytskii H (prodEquiv.symm (q.2, q.1)) - nemytskii H p₀‖) (𝓝 (u₀, u₀)) (𝓝 0) := by
    simpa using (tendsto_sub_nhds_zero_iff.2
      (hH_contAt.tendsto.comp (hswap.tendsto (u₀, u₀)))).norm.const_mul ‖A‖
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]; intro c hc
  filter_upwards [hswap.tendsto (u₀, u₀) hΩH_nhds,
    (tendsto_order.1 hdiff_tendsto).2 c hc] with ⟨u₁, u₂⟩ hseg hc_lt
  have hn1 : ((⌊2 * s⌋₊ + 1 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
  dsimp only; rw [nemytskii_sub_eq_realConvolution_hadamardFactor T hU hf u₂ u₁ hn1
      (fun x ↦ by simpa only [toContinuousMap_prodEquiv_symm_apply] using hseg x),
    ← nemytskii_hadamardFactor_diag T hU hf u₀ hn1 hu₀, ← sub_apply, ← map_sub]
  exact (A.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_right hc_lt.le (norm_nonneg _))

/-- Global version of `hasStrictFDerivAt_nemytskii_of_contDiffOn` for `f : E → F` of class `C^n`. -/
theorem hasStrictFDerivAt_nemytskii {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasStrictFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  hasStrictFDerivAt_nemytskii_of_contDiffOn 1 isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _) hn

/-- **Fréchet derivative of `nemytskii f` on an open set.** -/
theorem hasFDerivAt_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).hasFDerivAt

/-- Global Fréchet derivative of `nemytskii f`. -/
theorem hasFDerivAt_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    HasFDerivAt (nemytskii (s := s) f)
      (realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u)) u :=
  (hasStrictFDerivAt_nemytskii hf u hn).hasFDerivAt

/-- Formula for `fderiv ℝ (nemytskii f) u` when `u` takes values in open `U`. -/
theorem fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn).fderiv

/-- Global formula for `fderiv ℝ (nemytskii f) u`. -/
theorem fderiv_nemytskii_of_contDiff {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (u : CircleSobolev s E) (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) :
    fderiv ℝ (nemytskii (s := s) f) u =
      realConvolution hs.out (.id ℝ (E →L[ℝ] F)) (nemytskii (fderiv ℝ f) u) :=
  (hasFDerivAt_nemytskii_of_contDiff hf u hn).fderiv

/-- Pointwise action of `fderiv ℝ (nemytskii f) u v` on continuous representatives. -/
theorem toContinuousMap_fderiv_nemytskii_of_contDiffOn {U : Set E} (hU : IsOpen U) {n : ℕ∞ω}
    {f : E → F} (hf : ContDiffOn ℝ n f U) {u : CircleSobolev s E}
    (hu : ∀ x, toContinuousMap T hs.out u x ∈ U) (v : CircleSobolev s E)
    (hn : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := by simp) (x : AddCircle T) :
    toContinuousMap T hs.out (fderiv ℝ (nemytskii (s := s) f) u v) x =
      fderiv ℝ f (toContinuousMap T hs.out u x) (toContinuousMap T hs.out v x) := by
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
  toContinuousMap_fderiv_nemytskii_of_contDiffOn T isOpen_univ hf.contDiffOn (fun _ ↦ mem_univ _)
    v hn x

private theorem contDiffOn_nemytskii_nat_aux :
    ∀ (k : ℕ) {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
      {U : Set E} (_ : IsOpen U) {n : ℕ∞ω} {f : E → F'} (_ : ContDiffOn ℝ n f U)
      (_ : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n), ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
        {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U}
  | 0, F', _, _, _, U, hU, _, f, hf, hn =>
      contDiffOn_zero.2 (continuousOn_nemytskii T hU hf (by simpa using hn))
  | k + 1, F', _, _, _, U, hU, n, f, hf, hn => by
      have hn2 : ((⌊2 * s⌋₊ + 2 : ℕ) : ℕ∞ω) ≤ n := le_trans (by norm_cast; omega) hn
      push_cast; refine (contDiffOn_succ_iff_fderiv_of_isOpen
        (isOpen_setOf_forall_toContinuousMap_mem (E := E) T hs.out hU)).2 ⟨fun u hu ↦
          (hasFDerivAt_nemytskii_of_contDiffOn T hU hf hu hn2).differentiableAt
            |>.differentiableWithinAt, by simp, ?_⟩
      exact ((realConvolution hs.out (.id ℝ (E →L[ℝ] F'))).contDiff.comp_contDiffOn
        (contDiffOn_nemytskii_nat_aux k hU
          ((hf.of_le hn).fderiv_of_isOpen hU (m := ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω)) (by norm_cast))
          le_rfl)).congr fun u hu ↦ fderiv_nemytskii_of_contDiffOn T hU hf hu hn2

/-- **`C^k` regularity of `nemytskii f` on `H^s(E)` (`⌊2s⌋₊ + 1 + k ≤ n`).** -/
theorem contDiffOn_nemytskii_nat (k : ℕ) {U : Set E} (hU : IsOpen U) {n : ℕ∞ω} {f : E → F}
    (hf : ContDiffOn ℝ n f U) (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiffOn ℝ (k : ℕ∞ω) (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} := by
  let eF : F ≃L[ℂ] (ULift.{u} (Fin (Module.finrank ℂ F)) → ℂ) :=
    ((Module.finBasis ℂ F).reindex Equiv.ulift.symm).equivFun.toContinuousLinearEquiv
  let L := eF.symm.toContinuousLinearMap
  have hf' := (eF.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  refine (((mapCLM (s := s) L).restrictScalars ℝ).contDiff.comp_contDiffOn
    (contDiffOn_nemytskii_nat_aux T k hU hf' hn)).congr fun u hu ↦
      nemytskii_eq_of_forall_toContinuousMap_apply T fun x ↦ ?_
  rw [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    toContinuousMap_mapCLM_apply T hs.out L _ x,
    toContinuousMap_nemytskii_of_contDiffOn T hU hf' hu (le_trans (by norm_cast; omega) hn) x]
  exact eF.symm_apply_apply (f (toContinuousMap T hs.out u x))

/-- Global `C^k` regularity of `nemytskii f` when `f : E → F` is `C^n` (`⌊2s⌋₊ + 1 + k ≤ n`). -/
theorem contDiff_nemytskii_nat (k : ℕ) {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (hn : ((⌊2 * s⌋₊ + 1 + k : ℕ) : ℕ∞ω) ≤ n := by simp) :
    ContDiff ℝ (k : ℕ∞ω) (nemytskii (s := s) f) :=
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  contDiffOn_univ.1 ((contDiffOn_nemytskii_nat 1 k isOpen_univ hf.contDiffOn hn).mono
    fun _ _ _ ↦ mem_univ _)

/-- **`C^∞` smoothness of `nemytskii f` on open subsets of `H^s(E)`.** -/
theorem contDiffOn_nemytskii {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (nemytskii (s := s) f)
      {u : CircleSobolev s E | ∀ x, toContinuousMap T hs.out u x ∈ U} :=
  contDiffOn_infty.2 fun k ↦ contDiffOn_nemytskii_nat T k hU hf (by simp)

/-- **Global `C^∞` smoothness of `nemytskii f` on `H^s(E)`.** -/
theorem contDiff_nemytskii {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (nemytskii (s := s) f) :=
  contDiff_infty.2 fun k ↦ contDiff_nemytskii_nat k hf (by simp)

end Smoothness
end CircleSobolev
end TauCeti
