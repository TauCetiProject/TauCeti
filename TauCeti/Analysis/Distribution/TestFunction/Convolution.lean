/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation
public import Mathlib.Analysis.Distribution.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.Convergence
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Mollification and cutoff convolutions in the test-function topology

A test function may be convolved with a normalized smooth bump whenever the enlarged support
stays inside its open domain. Every derivative commutes with this operation. For shrinking
bumps, the mollifications converge in the native LF topology, so every distribution can be
evaluated along this approximation.

More generally, convolving a test function on `Ω'` with any locally integrable scalar kernel `K₀`
and multiplying by a smooth cutoff test function `χ` on `Ω` defines a continuous linear map
`TestFunction.cutoffConvolutionCLM : 𝓓(Ω', F) →L[ℝ] 𝓓(Ω, F)` for the LF topologies. This packages
the transpose of a locally integrable convolution kernel (such as a fundamental solution) on a
bounded domain without requiring global decay.

The codomain is any real Banach space, including the finite-dimensional spaces of alternating
forms used to test currents in coordinates.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §1.3 and §4.2:
  regularization by convolution and the topology of test functions.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory Filter Metric Set TopologicalSpace
open scoped Convolution Topology Distributions ContDiff Pointwise

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E}

/-- Mollify a test function by a normalized bump whose support enlargement stays in `Ω`. -/
def mollify (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) : 𝓓(Ω, F) where
  toFun := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)
  contDiff' := φ.hasCompactSupport.contDiff_convolution_right _
    (ρ.continuous_normed.locallyIntegrable) φ.contDiff
  hasCompactSupport' := ρ.hasCompactSupport_normed.convolution _ φ.hasCompactSupport
  tsupport_subset' := (ρ.tsupport_normed_convolution_subset (g := (φ : E → F))).trans h

/-- A mollified test function is the usual normalized-bump convolution. -/
@[simp]
theorem coe_mollify (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) :
    ⇑(mollify φ μ ρ h) = ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (φ : E → F) := (rfl)

/-- Evaluation of a mollified test function is the usual normalized-bump convolution. -/
theorem mollify_apply (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) (x : E) :
    mollify φ μ ρ h x = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)) x := (rfl)

/-- Mollifying the zero test function gives zero. -/
@[simp]
theorem mollify_zero (ρ : ContDiffBump (0 : E)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (h : closedBall (0 : E) ρ.rOut + tsupport (0 : 𝓓(Ω, F)) ⊆ (Ω : Set E)) :
    mollify (0 : 𝓓(Ω, F)) μ ρ h = 0 := by
  ext x
  simp [mollify_apply]

/-- Mollification is additive whenever all three support enlargements stay in the domain. -/
theorem mollify_add (φ ψ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure] (ρ : ContDiffBump (0 : E))
    (hφ : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E))
    (hψ : closedBall (0 : E) ρ.rOut + tsupport ψ ⊆ (Ω : Set E))
    (h : closedBall (0 : E) ρ.rOut + tsupport (φ + ψ) ⊆ (Ω : Set E)) :
    mollify (φ + ψ) μ ρ h = mollify φ μ ρ hφ + mollify ψ μ ρ hψ := by
  ext x
  simp only [mollify_apply, FunLike.coe_add, add_apply]
  exact (φ.hasCompactSupport.convolutionExists_right _
    ρ.continuous_normed.locallyIntegrable φ.continuous x).distrib_add
    (ψ.hasCompactSupport.convolutionExists_right _
      ρ.continuous_normed.locallyIntegrable ψ.continuous x)

/-- Mollification commutes with real scalar multiplication. -/
theorem mollify_smul (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : ℝ) (ρ : ContDiffBump (0 : E))
    (hφ : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E))
    (h : closedBall (0 : E) ρ.rOut + tsupport (c • φ) ⊆ (Ω : Set E)) :
    mollify (c • φ) μ ρ h = c • mollify φ μ ρ hφ := by
  ext x
  simp only [mollify_apply, FunLike.coe_smul, smul_apply, convolution_smul, Pi.smul_apply]

/-- Every Fréchet derivative commutes with mollification of test functions. -/
theorem iteratedFDeriv_mollify (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) (n : ℕ) :
    iteratedFDeriv ℝ n (mollify φ μ ρ h : E → F) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ n (φ : E → F) := by
  rw [coe_mollify]
  exact φ.hasCompactSupport.iteratedFDeriv_normed_convolution φ.contDiff ρ (by simp)

variable [CompleteSpace F]

/-- On a common compact support, shrinking-bump mollifications converge in the LF topology.
The compact set is contained in the open domain, not merely in its closure. -/
private theorem tendsto_mollify_of_support_subset {ι : Type*} {l : Filter ι}
    (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure]
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω)
    (hK : ∀ i, closedBall (0 : E) (ρ i).rOut + tsupport φ ⊆ (K : Set E)) :
    Tendsto (fun i => mollify φ μ (ρ i) ((hK i).trans hKΩ)) l (𝓝 φ) := by
  refine tendsto_of_tendstoUniformly_iteratedFDeriv K.isCompact hKΩ (fun i ↦
    ((ρ i).tsupport_normed_convolution_subset (g := (φ : E → F))).trans (hK i))
    fun n _ ↦ ?_
  have hc := φ.contDiff.continuous_iteratedFDeriv (m := n) (by simp)
  have hu := (φ.hasCompactSupport.iteratedFDeriv n).uniformContinuous_of_continuous hc
  simpa only [iteratedFDeriv_mollify] using
    ContDiffBump.tendstoUniformly_normed_convolution (μ := μ) hρ hu

/-- Shrinking normalized bumps approximate a test function in its LF topology whenever
the closed `rOut`-enlargement of `tsupport φ` stays inside `Ω` for every index. -/
theorem tendsto_mollify {ι : Type*} {l : Filter ι} (φ : 𝓓(Ω, F))
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    (h : ∀ i, closedBall (0 : E) (ρ i).rOut + tsupport φ ⊆ (Ω : Set E)) :
    Tendsto (fun i => mollify φ μ (ρ i) (h i)) l (𝓝 φ) := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := φ.hasCompactSupport.isCompact.exists_cthickening_subset_open
    Ω.isOpen φ.tsupport_subset
  let K : Compacts E := ⟨closedBall (0 : E) δ + tsupport φ,
    (isCompact_closedBall _ _).add φ.hasCompactSupport.isCompact⟩
  have hKΩ : (K : Set E) ⊆ Ω := by
    simpa only [K, Compacts.coe_mk,
      φ.hasCompactSupport.isCompact.closedBall_add hδ.le, zero_vadd] using hδΩ
  -- Replace only the initial large bumps, obtaining a common compact support.
  let ρ₀ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let σ : ι → ContDiffBump (0 : E) := fun i => if (ρ i).rOut ≤ δ then ρ i else ρ₀
  have hσ : σ =ᶠ[l] ρ := by
    filter_upwards [hρ.eventually (gt_mem_nhds hδ)] with i hi
    simp [σ, hi.le]
  have hσδ (i : ι) : (σ i).rOut ≤ δ := by
    dsimp [σ]
    split_ifs with hi
    · exact hi
    · exact le_rfl
  have hσK (i : ι) : closedBall (0 : E) (σ i).rOut + tsupport φ ⊆ (K : Set E) :=
    add_subset_add (closedBall_subset_closedBall (hσδ i)) Subset.rfl
  have hσlim := hρ.congr' (hσ.symm.mono fun i hi => congrArg ContDiffBump.rOut hi)
  refine (tendsto_mollify_of_support_subset φ μ hσlim hKΩ hσK).congr' ?_
  filter_upwards [hσ] with i hi
  ext x
  simp only [mollify_apply, hi]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Convolving tests supported in `K` with an integrable kernel `κ` supported in a compact set `S`
gives a continuous linear map into tests supported in `S + K`. -/
private def integrableConvolutionSupportedIn (K : Compacts E) {S : Set E} (hS : IsCompact S)
    {κ : E → ℝ} {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant] (hκi : Integrable κ μ)
    (hκs : Function.support κ ⊆ S) :
    𝓓_{K}(E, F) →L[ℝ] 𝓓_{⟨S + K, hS.add K.isCompact⟩}(E, F) :=
  letI K' : Compacts E := ⟨S + K, hS.add K.isCompact⟩
  letI P : 𝓓_{K}(E, F) →ₗ[ℝ] 𝓓_{K'}(E, F) :=
    { toFun f := .of_support_subset
        (f.hasCompactSupport.contDiff_convolution_right (lsmul ℝ ℝ) hκi.locallyIntegrable
          f.contDiff)
        ((support_convolution_subset _).trans (add_subset_add hκs f.support_subset))
      map_add' f g := by
        ext x
        simp only [ContDiffMapSupportedIn.coe_of_support_subset, FunLike.coe_add, add_apply]
        exact (f.hasCompactSupport.convolutionExists_right (lsmul ℝ ℝ) hκi.locallyIntegrable
          f.continuous x).distrib_add (g.hasCompactSupport.convolutionExists_right (lsmul ℝ ℝ)
            hκi.locallyIntegrable g.continuous x)
      map_smul' c f := by
        ext x
        simp [ContDiffMapSupportedIn.coe_of_support_subset, convolution_smul] }
  { toLinearMap := P
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{i}, ∫ t, ‖κ t‖ ∂μ, fun f ↦ ((P f).seminorm_le_iff ℝ
        (mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (apply_nonneg _ f)) i).2
        fun hi x _ ↦ ?_⟩
      have hPf : ⇑(P f) = κ ⋆[lsmul ℝ ℝ, μ] (f : E → F) := by
        ext y
        simp [P]
      rw [Finset.sup_singleton, hPf,
        f.hasCompactSupport.iteratedFDeriv_convolution_right (lsmul ℝ ℝ) hκi.locallyIntegrable
          f.contDiff (mod_cast le_top), convolution_def, ← integral_mul_const]
      refine norm_integral_le_of_norm_le (hκi.norm.mul_const _) (ae_of_all _ fun t ↦ ?_)
      have heq : ((compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ E) F F).comp (lsmul ℝ ℝ))
          (κ t) (iteratedFDeriv ℝ i (f : E → F) (x - t)) =
          κ t • iteratedFDeriv ℝ i (f : E → F) (x - t) := by
        ext m
        simp
      rw [heq, norm_smul]
      exact mul_le_mul_of_nonneg_left
        (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm ℝ hi) (norm_nonneg _) }

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
private theorem integrableConvolutionSupportedIn_apply (K : Compacts E) {S : Set E}
    (hS : IsCompact S) {κ : E → ℝ} {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant]
    (hκi : Integrable κ μ) (hκs : Function.support κ ⊆ S) (f : 𝓓_{K}(E, F)) (x : E) :
    integrableConvolutionSupportedIn K hS hκi hκs f x = (κ ⋆[lsmul ℝ ℝ, μ] (f : E → F)) x :=
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Convolving a test function on `Ω'` with a locally integrable scalar kernel `K₀` and multiplying
by a smooth cutoff test function `χ` on `Ω`, as a continuous linear map `𝓓(Ω', F) →L[ℝ] 𝓓(Ω, F)`
for the LF topologies. -/
def cutoffConvolutionCLM {Ω' : Opens E} (χ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    𝓓(Ω', F) →L[ℝ] 𝓓(Ω, F) :=
  TestFunction.limitCLM ℝ
    (fun φ ↦ ⟨fun x ↦ χ x • (K₀ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)) x,
      χ.contDiff.smul (φ.hasCompactSupport.contDiff_convolution_right (lsmul ℝ ℝ) hK₀ φ.contDiff),
      χ.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left _ _).trans χ.tsupport_subset⟩)
    (fun K _ ↦
      -- On `tsupport χ`, convolving with `K₀` against tests in `K` only sees `K₀` on the compact
      -- difference set `tsupport χ - K`.
      letI S : Set E := tsupport χ - (K : Set E)
      haveI hS : IsCompact S := by
        simpa only [S, sub_eq_add_neg] using IsCompact.add χ.hasCompactSupport K.isCompact.neg
      haveI hκi : Integrable (S.indicator K₀) μ :=
        (integrable_indicator_iff hS.measurableSet).2 (hK₀.integrableOn_isCompact hS)
      cutoffCLM χ.contDiff (inter_subset_left.trans χ.tsupport_subset) ∘L
        (ofSupportedInCLM ℝ (subset_univ _) : _ →L[ℝ] 𝓓(⊤, F)) ∘L
        integrableConvolutionSupportedIn K hS hκi Set.support_indicator_subset)
    (fun K _ f ↦ TestFunction.ext fun x ↦ by
      simp only [comp_apply, cutoffCLM_apply, coe_ofSupportedInCLM, coe_ofSupportedIn,
        integrableConvolutionSupportedIn_apply, coe_mk]
      by_cases hx : x ∈ tsupport χ
      · congr 1
        rw [convolution_def, convolution_def]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        by_cases hxt : x - t ∈ (K : Set E)
        · have htS : t ∈ tsupport χ - (K : Set E) := ⟨x, hx, x - t, hxt, sub_sub_cancel x t⟩
          simp [Set.indicator_of_mem htS]
        · simp [f.zero_on_compl hxt]
      · simp [image_eq_zero_of_notMem_tsupport hx])

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
@[simp]
theorem cutoffConvolutionCLM_apply {Ω' : Opens E} (χ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) (φ : 𝓓(Ω', F)) (x : E) :
    cutoffConvolutionCLM χ hK₀ φ x = χ x • (K₀ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)) x := by
  -- Pointwise formula defining `cutoffConvolutionCLM`, whose body is not exported.
  exact rfl

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The support of `cutoffConvolutionCLM χ hK₀ φ` is contained in the support of the cutoff `χ`. -/
theorem tsupport_cutoffConvolutionCLM_subset {Ω' : Opens E} (χ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ}
    {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ)
    (φ : 𝓓(Ω', F)) :
    tsupport (cutoffConvolutionCLM χ hK₀ φ : E → F) ⊆ tsupport (χ : E → ℝ) := by
  rw [funext (cutoffConvolutionCLM_apply χ hK₀ φ)]
  exact tsupport_smul_subset_left _ _

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Cutoff convolution with the zero cutoff vanishes. -/
@[simp]
theorem cutoffConvolutionCLM_zero {Ω' : Opens E} {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (0 : 𝓓(Ω, ℝ)) hK₀ = 0 := by
  ext φ x
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Cutoff convolution is additive in the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_add {Ω' : Opens E} (χ₁ χ₂ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (χ₁ + χ₂) hK₀ =
      cutoffConvolutionCLM χ₁ hK₀ + cutoffConvolutionCLM χ₂ hK₀ := by
  ext φ x
  simp [add_smul]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Cutoff convolution commutes with negation of the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_neg {Ω' : Opens E} (χ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (-χ) hK₀ = -cutoffConvolutionCLM χ hK₀ := by
  ext φ x
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Cutoff convolution commutes with subtraction of cutoffs. -/
@[simp]
theorem cutoffConvolutionCLM_sub {Ω' : Opens E} (χ₁ χ₂ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ} {μ : Measure E}
    [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (χ₁ - χ₂) hK₀ =
      cutoffConvolutionCLM χ₁ hK₀ - cutoffConvolutionCLM χ₂ hK₀ := by
  ext φ x
  simp [sub_smul]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Cutoff convolution commutes with scalar multiplication of the cutoff. -/
@[simp]
theorem cutoffConvolutionCLM_smul {Ω' : Opens E} (c : ℝ) (χ : 𝓓(Ω, ℝ)) {K₀ : E → ℝ}
    {μ : Measure E} [SFinite μ] [μ.IsAddLeftInvariant] (hK₀ : LocallyIntegrable K₀ μ) :
    cutoffConvolutionCLM (Ω' := Ω') (F := F) (c • χ) hK₀ = c • cutoffConvolutionCLM χ hK₀ := by
  ext φ x
  simp [mul_smul]

end TestFunction
