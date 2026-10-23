/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Mollification in the test-function topology

A test function may be convolved with a normalized smooth bump whenever the enlarged support
stays inside its open domain. Every derivative commutes with this operation. For shrinking
bumps, the mollifications converge in the native LF topology, so every distribution can be
evaluated along this approximation. The tail has a common compact support inside the domain.
The convergence proof uses the continuous inclusion of a fixed-compact test space, rather
than a final topology on topological spaces.

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
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

/-- Mollify a test function by a normalized bump whose support enlargement stays in `Ω`. -/
def mollify (φ : 𝓓(Ω, F)) (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) : 𝓓(Ω, F) where
  toFun := ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)
  contDiff' := φ.hasCompactSupport.contDiff_convolution_right _
    (ρ.continuous_normed.locallyIntegrable) φ.contDiff
  hasCompactSupport' := ρ.hasCompactSupport_normed.convolution _ φ.hasCompactSupport
  tsupport_subset' := (ρ.tsupport_normed_convolution_subset (g := (φ : E → F))).trans h

/-- Evaluation of a mollified test function is the usual normalized-bump convolution. -/
@[simp]
theorem mollify_apply (φ : 𝓓(Ω, F)) (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) (x : E) :
    mollify (μ := μ) φ ρ h x = (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (φ : E → F)) x := (rfl)

/-- Mollifying the zero test function gives zero. -/
@[simp]
theorem mollify_zero (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport (0 : 𝓓(Ω, F)) ⊆ (Ω : Set E)) :
    mollify (μ := μ) (0 : 𝓓(Ω, F)) ρ h = 0 := by
  ext x
  simp [mollify_apply]

/-- Mollification is additive whenever all three support enlargements stay in the domain. -/
theorem mollify_add (φ ψ : 𝓓(Ω, F)) (ρ : ContDiffBump (0 : E))
    (hφ : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E))
    (hψ : closedBall (0 : E) ρ.rOut + tsupport ψ ⊆ (Ω : Set E))
    (h : closedBall (0 : E) ρ.rOut + tsupport (φ + ψ) ⊆ (Ω : Set E)) :
    mollify (μ := μ) (φ + ψ) ρ h = mollify (μ := μ) φ ρ hφ + mollify (μ := μ) ψ ρ hψ := by
  ext x
  simp only [mollify_apply, FunLike.coe_add, add_apply]
  exact (φ.hasCompactSupport.convolutionExists_right _
    ρ.continuous_normed.locallyIntegrable φ.continuous x).distrib_add
    (ψ.hasCompactSupport.convolutionExists_right _
      ρ.continuous_normed.locallyIntegrable ψ.continuous x)

/-- Mollification commutes with real scalar multiplication. -/
theorem mollify_smul (φ : 𝓓(Ω, F)) (c : ℝ) (ρ : ContDiffBump (0 : E))
    (hφ : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E))
    (h : closedBall (0 : E) ρ.rOut + tsupport (c • φ) ⊆ (Ω : Set E)) :
    mollify (μ := μ) (c • φ) ρ h = c • mollify (μ := μ) φ ρ hφ := by
  ext x
  simp only [mollify_apply, FunLike.coe_smul, smul_apply, convolution_smul, Pi.smul_apply]

/-- Mollification enlarges support by at most the radius of the bump. -/
theorem tsupport_mollify_subset (φ : 𝓓(Ω, F)) (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) :
    tsupport (mollify (μ := μ) φ ρ h) ⊆ closedBall (0 : E) ρ.rOut + tsupport φ :=
  ρ.tsupport_normed_convolution_subset (g := (φ : E → F))

/-- Every Fréchet derivative commutes with mollification of test functions. -/
theorem iteratedFDeriv_mollify (φ : 𝓓(Ω, F)) (ρ : ContDiffBump (0 : E))
    (h : closedBall (0 : E) ρ.rOut + tsupport φ ⊆ (Ω : Set E)) (n : ℕ) :
    iteratedFDeriv ℝ n (mollify (μ := μ) φ ρ h : E → F) =
      ρ.normed μ ⋆[lsmul ℝ ℝ, μ] iteratedFDeriv ℝ n (φ : E → F) :=
  φ.hasCompactSupport.iteratedFDeriv_convolution_lsmul_right
    ρ.continuous_normed.locallyIntegrable φ.contDiff (by simp)

variable [CompleteSpace F]

/-- On a common compact support, shrinking-bump mollifications converge in the LF topology.
The compact set is contained in the open domain, not merely in its closure. -/
private theorem tendsto_mollify_of_support_subset {ι : Type*} {l : Filter ι} (φ : 𝓓(Ω, F))
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (hφK : tsupport φ ⊆ K)
    (hK : ∀ i, closedBall (0 : E) (ρ i).rOut + tsupport φ ⊆ (K : Set E)) :
    Tendsto (fun i => mollify (μ := μ) φ (ρ i) ((hK i).trans hKΩ)) l (𝓝 φ) := by
  let φK : 𝓓_{K}(E, F) := .of_support_subset φ.contDiff ((subset_tsupport _).trans hφK)
  let ψ : ι → 𝓓_{K}(E, F) := fun i => .of_support_subset
    (mollify (μ := μ) φ (ρ i) ((hK i).trans hKΩ)).contDiff
    ((subset_tsupport _).trans ((tsupport_mollify_subset φ (ρ i) _).trans (hK i)))
  have hlim : Tendsto ψ l (𝓝 φK) := by
    rw [(ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
      ℝ).isEmbedding.tendsto_nhds_iff]
    apply tendsto_pi_nhds.2
    intro n
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.2
    have hc := φ.contDiff.continuous_iteratedFDeriv (m := n) (by simp)
    have hu := (φ.hasCompactSupport.iteratedFDeriv n).uniformContinuous_of_continuous hc
    have ht := ContDiffBump.tendstoUniformly_normed_convolution (μ := μ) hρ hu
    convert ht using 1
    · funext i x
      simp only [Function.comp_apply, ContinuousLinearMap.pi_apply,
        ContDiffMapSupportedIn.structureMapCLM_top_apply]
      exact congrFun (iteratedFDeriv_mollify φ (ρ i) ((hK i).trans hKΩ) n) x
    · rfl
  have ht := (continuous_ofSupportedIn hKΩ).tendsto φK |>.comp hlim
  -- The fixed-compact bundles and their inclusion retain the same underlying functions.
  convert ht using 1
  · funext i
    ext x
    rfl
  · congr 1

/-- Shrinking normalized bumps approximate a test function in its LF topology whenever
each mollification has support inside the domain. A common compact support for the tail
is automatic. -/
theorem tendsto_mollify {ι : Type*} {l : Filter ι} (φ : 𝓓(Ω, F))
    {ρ : ι → ContDiffBump (0 : E)} (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0))
    (h : ∀ i, closedBall (0 : E) (ρ i).rOut + tsupport φ ⊆ (Ω : Set E)) :
    Tendsto (fun i => mollify (μ := μ) φ (ρ i) (h i)) l (𝓝 φ) := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := φ.hasCompactSupport.isCompact.exists_cthickening_subset_open
    Ω.isOpen φ.tsupport_subset
  let K : Compacts E := ⟨closedBall (0 : E) δ + tsupport φ,
    (isCompact_closedBall _ _).add φ.hasCompactSupport.isCompact⟩
  have hKΩ : (K : Set E) ⊆ Ω := by
    simpa only [K, Compacts.coe_mk,
      φ.hasCompactSupport.isCompact.closedBall_add hδ.le, zero_vadd] using hδΩ
  have hφK : tsupport φ ⊆ K := by
    intro x hx
    exact ⟨0, mem_closedBall_self hδ.le, x, hx, zero_add x⟩
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
  refine (tendsto_mollify_of_support_subset (μ := μ) φ hσlim hKΩ hφK hσK).congr' ?_
  filter_upwards [hσ] with i hi
  ext x
  simp only [mollify_apply, hi]

end TestFunction
