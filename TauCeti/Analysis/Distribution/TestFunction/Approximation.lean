/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Uniform approximation of continuous and `C¹` functions by test functions

Let `Ω` be an open set of a finite-dimensional real normed space `E`. Mollifying a continuous
function supported in a compact set `K` by normalized bumps of small radius gives test functions
on `Ω` supported in a fixed closed thickening of `K` that converge to it uniformly, as long as that
thickening lies in `Ω`. For a `C¹` function the derivatives of the mollifications are the
mollifications of its derivative (Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right`), so
they converge uniformly as well. Shrinking the mollifications by a factor close to `1` keeps them
below any bound `‖f‖ ≤ ρ` by a function `ρ` that is continuous and positive near the support.
The construction follows Mathlib's
`MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le` and
`UniformContinuous.exists_contDiff_dist_le` (in
`Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox`), with added control of the support; the
error estimate is Mathlib's `ContDiffBump.dist_normed_convolution_le`.

## Main results

* `MeasureTheory.LocallyIntegrable.exists_testFunction_eq_normed_convolution`: the mollification
  of a locally integrable function supported in a compact set `K` by a normalized bump of outer
  radius at most `δ` is a test function on `Ω` supported in `cthickening δ K`, if that thickening
  lies in `Ω`.
* `Continuous.exists_testFunction_dist_le`: a continuous function supported in a compact set `K`
  is uniformly approximated by test functions supported in any closed thickening of `K` that lies
  in `Ω`.
* `CompactlySupportedContinuousMap.exists_isCompact_forall_exists_testFunction_dist_le`: a
  compactly supported continuous function on the subspace `Ω` is uniformly approximated by test
  functions supported in one compact subset of `Ω`.
* `ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le`: a `C¹` function supported in a
  compact set `K` is approximated in the same way, uniformly together with its derivative.
* `ContDiff.exists_testFunction_norm_le_and_dist_le_and_dist_fderiv_le`: the approximations can
  moreover be chosen to respect a pointwise bound `‖f x‖ ≤ ρ x` by a function `ρ` that is
  continuous and positive near the support.
* `TestFunction.exists_isCompact_forall_exists_dist_le`: a test function of class `C^n` is a
  uniform limit of smooth test functions supported in a fixed compact subset of `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Chapter I
  (regularization by convolution).
-/

public section

open MeasureTheory TopologicalSpace Metric Set
open scoped Distributions Convolution CompactlySupported

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Mollifying a locally integrable function supported in a compact set `K` by a normalized bump of
outer radius at most `δ` gives a test function on `Ω` supported in `cthickening δ K`, as long as
that thickening lies in `Ω`. -/
theorem MeasureTheory.LocallyIntegrable.exists_testFunction_eq_normed_convolution
    [HasContDiffBump E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {f : E → F}
    (hf : LocallyIntegrable f μ) {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ K)
    {δ : ℝ} (hKΩ : cthickening δ K ⊆ Ω) (ρ : ContDiffBump (0 : E)) (hρ : ρ.rOut ≤ δ) :
    ∃ φ : 𝓓(Ω, F), ⇑φ = ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f ∧
      tsupport φ ⊆ cthickening δ K := by
  set g := ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f
  have hgs : tsupport g ⊆ cthickening δ K := by
    have hsupp : Function.support g ⊆ thickening ρ.rOut K := by
      refine (support_convolution_subset _).trans ?_
      rw [ρ.support_normed_eq, ← ball_add_zero]
      exact add_subset_add_left ((subset_tsupport f).trans hfK)
    exact (closure_mono hsupp).trans <| (closure_thickening_subset_cthickening _ _).trans <|
      cthickening_mono hρ K
  exact ⟨⟨g, ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed hf,
      hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hgs, hgs.trans hKΩ⟩, rfl, hgs⟩

/-- A continuous function supported in a compact set `K` is uniformly approximated by test
functions on `Ω`, as long as a closed thickening `cthickening δ K` lies in `Ω`: for every `ε > 0`
there is a test function on `Ω`, supported in `cthickening δ K`, within `ε` of `f` everywhere. -/
theorem Continuous.exists_testFunction_dist_le {f : E → F} (hf : Continuous f) {K : Set E}
    (hK : IsCompact K) (hfK : tsupport f ⊆ K) {δ : ℝ} (hδ : 0 < δ)
    (hKΩ : cthickening δ K ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ cthickening δ K ∧ ∀ x, dist (φ x) (f x) ≤ ε := by
  borelize E
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
  obtain ⟨η, hη, hfη⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf) ε hε
  -- Mollify `f` by a normalized bump of outer radius `min η δ`.
  have hr : 0 < min η δ := lt_min hη hδ
  let ρ : ContDiffBump (0 : E) := ⟨min η δ / 2, min η δ, half_pos hr, half_lt_self hr⟩
  have hfi : LocallyIntegrable f Measure.addHaar := hf.locallyIntegrable
  obtain ⟨φ, hφ, hφs⟩ :=
    hfi.exists_testFunction_eq_normed_convolution hK hfK hKΩ ρ (min_le_right _ _)
  refine ⟨φ, hφs, fun x => ?_⟩
  rw [hφ]
  exact ρ.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy =>
    (hfη ((mem_ball.mp hy).trans_le (min_le_left _ _))).le

/-- A compactly supported continuous function on the subspace `Ω` is a uniform limit of test
functions on `Ω` supported in one compact subset of `Ω`: there is a compact `K ⊆ Ω` containing the
support of `f` such that for every `ε > 0` some test function supported in `K` is within `ε` of `f`
at every point of `Ω`. -/
theorem CompactlySupportedContinuousMap.exists_isCompact_forall_exists_testFunction_dist_le
    (f : C_c(Ω, F)) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ (↑) '' tsupport f ⊆ K ∧
      ∀ ε > 0, ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ K ∧ ∀ x : Ω, dist (φ x) (f x) ≤ ε := by
  have hK : IsCompact (((↑) : Ω → E) '' tsupport f) :=
    f.hasCompactSupport.isCompact.image continuous_subtypeVal
  obtain ⟨δ, hδ, hδΩ⟩ :=
    hK.exists_cthickening_subset_open Ω.isOpen (Subtype.coe_image_subset _ _)
  refine ⟨cthickening δ _, hK.cthickening, hδΩ, self_subset_cthickening _, fun ε hε => ?_⟩
  -- Approximate the extension of `f` by zero to `E`.
  obtain ⟨φ, hφK, hφ⟩ := (f.hasCompactSupport.continuous_extend_zero Ω.isOpen
    f.continuous).exists_testFunction_dist_le hK
    (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtypeVal) hδ hδΩ hε
  refine ⟨φ, hφK, fun x => ?_⟩
  simpa [Subtype.val_injective.extend_apply] using hφ x

omit [FiniteDimensional ℝ E] in
/-- A `C¹` function supported in a compact set `K` is approximated by test functions on `Ω`
uniformly together with its derivative, as long as a closed thickening `cthickening δ K` lies in
`Ω`: for every `ε > 0` there is a test function on `Ω`, supported in `cthickening δ K`, within `ε`
of `f` everywhere and whose derivative is within `ε` of `fderiv ℝ f` everywhere. -/
theorem ContDiff.exists_testFunction_dist_le_and_dist_fderiv_le {f : E → F}
    (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hKΩ : cthickening δ K ⊆ Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ cthickening δ K ∧
      ∀ x, dist (φ x) (f x) ≤ ε ∧ dist (fderiv ℝ φ x) (fderiv ℝ f x) ≤ ε := by
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
  by_cases hfd : FiniteDimensional ℝ E
  swap
  · -- In infinite dimensions a compactly supported continuous function vanishes.
    have hf0 : f = 0 := (hfc.eq_zero_or_finiteDimensional ℝ hf.continuous).resolve_right hfd
    subst hf0
    exact ⟨0, by simp, fun x ↦ by simp [hε.le]⟩
  borelize E
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  obtain ⟨η₁, hη₁, hfη⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf.continuous) ε hε
  obtain ⟨η₂, hη₂, hDfη⟩ :=
    Metric.uniformContinuous_iff.mp ((hfc.fderiv ℝ).uniformContinuous_of_continuous hDf) ε hε
  -- Mollify `f` by a normalized bump of outer radius `r = min (min η₁ η₂) δ`.
  set r := min (min η₁ η₂) δ
  have hr : 0 < r := lt_min (lt_min hη₁ hη₂) hδ
  let ρ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hfi : LocallyIntegrable f Measure.addHaar := hf.continuous.locallyIntegrable
  obtain ⟨φ, hφ, hφs⟩ :=
    hfi.exists_testFunction_eq_normed_convolution hK hfK hKΩ ρ (min_le_right _ _)
  refine ⟨φ, hφs, fun x => ⟨?_, ?_⟩⟩
  · rw [hφ]
    exact ρ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable fun y hy =>
      (hfη ((mem_ball.mp hy).trans_le ((min_le_left _ _).trans (min_le_left _ _)))).le
  · -- The derivative of the mollification is the mollification of the derivative.
    have hD : fderiv ℝ φ x =
        (ρ.normed Measure.addHaar ⋆[ContinuousLinearMap.lsmul ℝ ℝ, Measure.addHaar]
          fderiv ℝ f) x := by
      rw [hφ, (hfc.hasFDerivAt_convolution_right _
        ρ.continuous_normed.locallyIntegrable hf x).fderiv, convolution_def, convolution_def]
      -- Both kernels multiply `fderiv ℝ f (x - t) v` by the bump value at `t`.
      refine congrArg _ (funext fun t => ContinuousLinearMap.ext fun v => ?_)
      simp only [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.lsmul_apply,
        smul_apply]
    rw [hD]
    exact ρ.dist_normed_convolution_le hDf.aestronglyMeasurable fun y hy =>
      (hDfη ((mem_ball.mp hy).trans_le ((min_le_left _ _).trans (min_le_right _ _)))).le

omit [CompleteSpace F] in
/-- If `‖a - b‖ ≤ η` and `‖b‖ ≤ R`, shrinking `a` by the factor `(1 + η / m)⁻¹` keeps it within
`η (1 + R / m)` of `b`. -/
private theorem norm_inv_one_add_div_smul_sub_le {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {a b : G} {η m R : ℝ} (hη : 0 ≤ η) (hm : 0 < m)
    (hab : ‖a - b‖ ≤ η) (hb : ‖b‖ ≤ R) :
    ‖(1 + η / m)⁻¹ • a - b‖ ≤ η * (1 + R / m) := by
  have hd : 0 < 1 + η / m := by positivity
  have hsplit : (1 + η / m)⁻¹ • a - b = (1 + η / m)⁻¹ • (a - b) - ((η / m) / (1 + η / m)) • b := by
    have hc : (1 + η / m)⁻¹ + (η / m) / (1 + η / m) = 1 := by
      field_simp
    rw [smul_sub, sub_sub, ← add_smul, hc, one_smul]
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_pos.2 hd).le,
    Real.norm_of_nonneg (by positivity)]
  have h1 : (1 + η / m)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [div_nonneg hη hm.le])
  have h2 : (η / m) / (1 + η / m) ≤ η / m :=
    div_le_self (by positivity) (by linarith [div_nonneg hη hm.le])
  calc (1 + η / m)⁻¹ * ‖a - b‖ + (η / m) / (1 + η / m) * ‖b‖ ≤ 1 * η + η / m * R := by
        gcongr
    _ = η * (1 + R / m) := by ring

/-- A `C¹` function supported in a compact set `K` and bounded in norm by a function `ρ` is
approximated by test functions obeying the same bound, uniformly together with its derivative, as
long as a closed thickening `cthickening δ K` lies in `Ω` and `ρ` is continuous and positive on
it: for every `ε > 0` there is a test function `φ` on `Ω`, supported in `cthickening δ K`, with
`‖φ x‖ ≤ ρ x` everywhere, within `ε` of `f` everywhere and whose derivative is within `ε` of
`fderiv ℝ f` everywhere. -/
theorem ContDiff.exists_testFunction_norm_le_and_dist_le_and_dist_fderiv_le {f : E → F}
    (hf : ContDiff ℝ 1 f) {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hKΩ : cthickening δ K ⊆ Ω) {ρ : E → ℝ}
    (hρ : ContinuousOn ρ (cthickening δ K)) (hρ0 : ∀ x ∈ cthickening δ K, 0 < ρ x)
    (hfρ : ∀ x, ‖f x‖ ≤ ρ x) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, F), tsupport φ ⊆ cthickening δ K ∧ (∀ x, ‖φ x‖ ≤ ρ x) ∧
      ∀ x, dist (φ x) (f x) ≤ ε ∧ dist (fderiv ℝ φ x) (fderiv ℝ f x) ≤ ε := by
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hfK
  -- A positive lower bound `m` for `ρ` on the thickening, and a bound `R` for `f` and `Df`.
  obtain ⟨m, hm, hmρ⟩ := hK.cthickening.exists_forall_le' hρ hρ0
  obtain ⟨R₀, hR₀⟩ := hf.continuous.bounded_above_of_compact_support hfc
  obtain ⟨R₁, hR₁⟩ :=
    (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (hfc.fderiv ℝ)
  set R := max (max R₀ R₁) 0
  -- Approximate `f` to within `η`, then shrink the approximation by `(1 + η / m)⁻¹`.
  set η := ε / (1 + R / m)
  have hη : 0 < η := by positivity
  have hηε : η * (1 + R / m) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨φ, hφK, hφ⟩ := hf.exists_testFunction_dist_le_and_dist_fderiv_le hK hfK hδ hKΩ hη
  refine ⟨(1 + η / m)⁻¹ • φ, (tsupport_smul_subset_right _ _).trans hφK, fun x => ?_,
    fun x => ⟨?_, ?_⟩⟩
  · by_cases hx : x ∈ cthickening δ K
    · have hρx := hmρ x hx
      have hφx : ‖φ x‖ ≤ ρ x + η := by
        have h := norm_sub_norm_le (φ x) (f x)
        rw [← dist_eq_norm] at h
        linarith [hfρ x, (hφ x).1]
      have hd : 0 < 1 + η / m := by positivity
      rw [smul_apply, norm_smul, Real.norm_of_nonneg (inv_pos.2 hd).le,
        inv_mul_le_iff₀ hd]
      calc ‖φ x‖ ≤ ρ x + η := hφx
        _ ≤ ρ x + η * (ρ x / m) := by
          gcongr
          exact le_mul_of_one_le_right hη.le ((one_le_div hm).2 hρx)
        _ = (1 + η / m) * ρ x := by ring
    · rw [smul_apply, image_eq_zero_of_notMem_tsupport fun h => hx (hφK h), smul_zero,
        norm_zero]
      exact (norm_nonneg _).trans (hfρ x)
  · rw [smul_apply, dist_eq_norm, ← hηε]
    exact norm_inv_one_add_div_smul_sub_le hη.le hm (by simpa [dist_eq_norm] using (hφ x).1)
      ((hR₀ x).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · rw [FunLike.coe_smul, fderiv_const_smul (φ.contDiff.differentiable (by simp) x), dist_eq_norm,
      ← hηε]
    exact norm_inv_one_add_div_smul_sub_le hη.le hm (by simpa [dist_eq_norm] using (hφ x).2)
      ((hR₁ x).trans ((le_max_right _ _).trans (le_max_left _ _)))

/-- A test function `φ` of class `C^n` on `Ω` is a uniform limit of smooth test functions supported
in a fixed compact subset of `Ω`: there is a compact `K ⊆ Ω` containing the support of `φ` such
that for every `ε > 0` some smooth test function supported in `K` is within `ε` of `φ`
everywhere. -/
theorem TestFunction.exists_isCompact_forall_exists_dist_le {n : ℕ∞} (φ : 𝓓^{n}(Ω, F)) :
    ∃ K : Set E, IsCompact K ∧ K ⊆ Ω ∧ tsupport φ ⊆ K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ ψ : 𝓓(Ω, F), tsupport ψ ⊆ K ∧ ∀ x, dist (ψ x) (φ x) ≤ ε := by
  have hK := φ.hasCompactSupport.isCompact
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen φ.tsupport_subset
  exact ⟨_, hK.cthickening, hδΩ, self_subset_cthickening _, fun ε hε =>
    φ.continuous.exists_testFunction_dist_le hK subset_rfl hδ hδΩ hε⟩
