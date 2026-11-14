/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.DerivativeApproximation
public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Analysis.Distribution.TestFunction.Convergence

/-!
# Mollification in the test-function topology

A test function may be convolved with a normalized smooth bump whenever the enlarged support
stays inside its open domain. Every derivative and the divergence of a test vector field commute
with this operation. For shrinking
bumps, the mollifications converge in the native LF topology, so every distribution can be
evaluated along this approximation.

The codomain is any real Banach space, including the finite-dimensional spaces of alternating
forms used to test currents in coordinates.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §1.3:
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

/-- The Fréchet derivative commutes with mollification of test functions. -/
theorem fderiv_mollify (φ : 𝓓(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) :
    fderiv ℝ (mollify φ μ ρ h : E → F) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ (φ : E → F) := by
  ext x : 1
  have hpre : (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR E = lsmul ℝ ℝ := by ext; rfl
  rw [coe_mollify, (φ.hasCompactSupport.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    (ρ.continuous_normed (μ := μ)).locallyIntegrable (φ.contDiff.of_le (by simp)) x).fderiv, hpre]

/-- As functions, the divergence of a mollified test vector field is the normalized-bump
convolution of its divergence. -/
theorem coe_divergenceCLM_mollify (φ : 𝓓(Ω, E)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) :
    (divergenceCLM (mollify φ μ ρ h) : E → ℝ) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (divergenceCLM φ : E → ℝ) := by
  ext x
  have hφ1 : ContDiff ℝ 1 (φ : E → E) := φ.contDiff.of_le (by simp)
  have hex := (ρ.hasCompactSupport_normed (μ := μ)).convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) (ρ.integrable_normed (μ := μ)).locallyIntegrable
    (hφ1.continuous_fderiv one_ne_zero) x
  have hdiv : (divergenceCLM φ : E → ℝ) =
      fun y => TauCeti.traceCLM ℝ E (fderiv ℝ (φ : E → E) y) := by
    ext y
    rw [divergenceCLM_apply, ← TauCeti.traceCLM_apply]
  rw [divergenceCLM_apply, ← TauCeti.traceCLM_apply, fderiv_mollify, hdiv]
  exact ((TauCeti.traceCLM ℝ E).convolution_lsmul_comp_comm hex).symm

/-- Divergence commutes with mollification of test vector fields. -/
theorem divergenceCLM_mollify (φ : 𝓓(Ω, E)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E))
    (hdiv : closedBall (0 : E) ρ.rOut + tsupport (divergenceCLM φ) ⊆ (Ω : Set E) := by
      exact (Set.add_subset_add_left (closure_minimal
        (Function.support_subset_iff'.2 fun x hx => by simp [fderiv_of_notMem_tsupport ℝ hx])
        (isClosed_tsupport _))).trans h) :
    divergenceCLM (mollify φ μ ρ h) = mollify (divergenceCLM φ) μ ρ hdiv := by
  ext x
  exact congrFun (coe_divergenceCLM_mollify φ μ ρ h) x

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

end TestFunction
