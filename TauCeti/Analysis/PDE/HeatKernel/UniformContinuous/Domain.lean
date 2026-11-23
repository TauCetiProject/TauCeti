/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous.Core
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Integral.BoundedContinuousFunction
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore
import TauCeti.Topology.ContinuousMap.Bounded.Mollification

/-!
# The domain of the heat generator on bounded uniformly continuous functions

On the Banach space `BUC(E, F)` of bounded uniformly continuous functions on a finite-dimensional
real inner product space `E`, with the supremum norm, the heat semigroup `e^{tΔ}`
(`TauCeti.heatSemigroupBUC`) has as generator the distributional Laplacian on its maximal domain
in `BUC`: `f` lies in the domain with `A f = g` exactly when `Δf = g` in the sense of
distributions,

`∫ Δφ • f = ∫ φ • g` for every smooth compactly supported `φ : E → ℝ`

(`TauCeti.mem_graph_generator_heatSemigroupBUC_iff`). So the domain is the set of `f ∈ BUC` whose
distributional Laplacian has a bounded uniformly continuous representative
(`TauCeti.mem_domain_heatSemigroupBUC_iff`). Unlike `TauCeti.generator_heatSemigroupBUC`, which
identifies the generator on bounded `C²` functions with bounded first and second derivatives, no
differentiability of `f` is assumed.

## The argument

The pairs `(f, g)` with `Δf = g` in the sense of distributions form a closed subspace of
`BUC × BUC`: against a fixed test function both sides are continuous in the supremum norm. It
contains the generator graph on the smooth functions with bounded derivatives, where the generator
is the classical Laplacian and Green's identity holds, and these functions form a core
(`TauCeti.generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule`). Hence it contains
the whole generator graph.

Conversely, let `Δf = g` in the sense of distributions and mollify: `fₙ = ρₙ ⋆ f` with normalized
bumps `ρₙ` of radii tending to zero (`ContDiffBump.normedConvolutionBUC`). Each `fₙ` is smooth with
bounded derivatives of every order, so it lies in the domain with `A fₙ = Δfₙ`, and
`Δfₙ = ρₙ ⋆ g` because the Laplacian of `ρₙ ⋆ f` at `y` is the pairing of `f` with the Laplacian
of the test function `t ↦ ρₙ (y - t)`. By uniform continuity, `fₙ → f` and `ρₙ ⋆ g → g`
uniformly, and the generator is closed.

## Main declarations

* `TauCeti.integral_laplacian_smul_eq_integral_smul_generator_heatSemigroupBUC`: on its domain the
  generator is the distributional Laplacian.
* `TauCeti.mem_graph_generator_heatSemigroupBUC_iff`: `(f, g)` lies on the generator graph exactly
  when `Δf = g` in the sense of distributions.
* `TauCeti.mem_domain_heatSemigroupBUC_iff`: the domain is the set of `f ∈ BUC` whose distributional
  Laplacian lies in `BUC`.
* `TauCeti.generator_heatSemigroupBUC_eq_of_integral_laplacian_smul_eq`: the generator sends `f` to
  its distributional Laplacian.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction Filter Laplacian MeasureTheory Semigroups Set
  Topology ContinuousLinearMap
open scoped ContDiff Convolution Distributions

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace F]

/-- **On its domain, the heat generator is the distributional Laplacian.** For `f` in the domain
of the heat generator `A` on bounded uniformly continuous functions, `∫ Δφ • f = ∫ φ • A f` for
every smooth compactly supported `φ`. -/
theorem integral_laplacian_smul_eq_integral_smul_generator_heatSemigroupBUC
    (f : (heatSemigroupBUC (E := E) (F := F)).generator.domain) (φ : 𝓓(⊤, ℝ)) :
    ∫ x, Δ (φ : E → ℝ) x • ((f : uniformContinuousSubmodule ℝ E F).val : E → F) x =
      ∫ x, (φ : E → ℝ) x • ((heatSemigroupBUC (E := E) (F := F)).generator f).val x := by
  let S := (heatSemigroupBUC (E := E) (F := F)).toStronglyContinuousSemigroup
  let s : Set (uniformContinuousSubmodule ℝ E F × uniformContinuousSubmodule ℝ E F) :=
    (fun p ↦ (p.1.val, p.2.val)) ⁻¹' {p : (E →ᵇ F) × (E →ᵇ F) |
      ∀ φ : 𝓓(⊤, ℝ), ∫ x, Δ (φ : E → ℝ) x • p.1 x = ∫ x, (φ : E → ℝ) x • p.2 x}
  -- Against a fixed test function, both sides are continuous in the supremum norm.
  have hs : IsClosed s := by
    refine IsClosed.preimage ((continuous_subtypeVal.comp continuous_fst).prodMk
      (continuous_subtypeVal.comp continuous_snd)) ?_
    simp only [ofPred_forall]
    refine isClosed_iInter fun φ ↦ isClosed_eq ?_ ?_
    · exact (((φ.contDiff.of_le (by simp)).continuous_laplacian).integrable_of_hasCompactSupport
        φ.hasCompactSupport.laplacian).continuous_integral_smul.comp continuous_fst
    · exact (φ.contDiff.continuous.integrable_of_hasCompactSupport
        φ.hasCompactSupport).continuous_integral_smul.comp continuous_snd
  -- On the smooth core the generator is the classical Laplacian, and Green's identity holds.
  have hcore : ((S.generator.domRestrict (smoothBoundedDerivativesSubmodule ℝ E F)).graph :
      Set _) ⊆ s := by
    intro p hp φ
    obtain ⟨h, rfl⟩ := (LinearPMap.mem_graph_iff' _).1 hp
    obtain ⟨_, hΔ⟩ := exists_generator_heatSemigroupBUC_eq_laplacian h.property.1
    have hval : ((S.generator.domRestrict (smoothBoundedDerivativesSubmodule ℝ E F)) h).val =
        Δ (h.val.val : E → F) := by
      have hres : (S.generator.domRestrict (smoothBoundedDerivativesSubmodule ℝ E F)) h =
          S.generator ⟨h.val, h.property.2⟩ := LinearPMap.domRestrict_apply rfl
      rw [hres]
      exact hΔ
    simp only [hval]
    have hsmooth := ((mem_smoothBoundedDerivativesSubmodule ℝ E F _).1 h.property.1).1
    exact (hsmooth.of_le (by simp)).contDiffOn.integral_laplacian_smul_eq_integral_smul_laplacian
      (Ω := ⊤) φ
  have hgraph := generator_heatSemigroupBUC_hasCore_smoothBoundedDerivativesSubmodule
    |>.graph_subset_of_isClosed hs hcore
  exact hgraph (S.generator.mem_graph f) φ

/-- **The graph of the heat generator on bounded uniformly continuous functions.** The pair
`(f, g)` lies on the graph of the heat generator exactly when `Δf = g` in the sense of
distributions: `∫ Δφ • f = ∫ φ • g` for every smooth compactly supported `φ`. -/
theorem mem_graph_generator_heatSemigroupBUC_iff {f g : uniformContinuousSubmodule ℝ E F} :
    (f, g) ∈ (heatSemigroupBUC (E := E) (F := F)).generator.graph ↔
      ∀ φ : 𝓓(⊤, ℝ),
        ∫ x, Δ (φ : E → ℝ) x • (f.val : E → F) x = ∫ x, (φ : E → ℝ) x • (g.val : E → F) x := by
  let S := (heatSemigroupBUC (E := E) (F := F)).toStronglyContinuousSemigroup
  refine ⟨fun h φ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨u, rfl, rfl⟩ := (LinearPMap.mem_graph_iff _).1 h
    exact integral_laplacian_smul_eq_integral_smul_generator_heatSemigroupBUC u φ
  -- Mollify: `ρₙ ⋆ f` lies in the domain, with generator value `Δ (ρₙ ⋆ f) = ρₙ ⋆ g`.
  let ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking one_pos
  have hgraph : ∀ n, ((ρ n).normedConvolutionBUC volume f, (ρ n).normedConvolutionBUC volume g) ∈
      S.generator.graph := fun n ↦ by
    obtain ⟨hdom, hΔ⟩ := exists_generator_heatSemigroupBUC_eq_laplacian
      ((ρ n).normedConvolutionBUC_mem_smoothBoundedDerivativesSubmodule volume f)
    refine (LinearPMap.mem_graph_iff _).2 ⟨⟨_, ?_⟩, rfl, Subtype.ext (BoundedContinuousFunction.ext
      fun y ↦ ?_)⟩
    · rwa [StronglyContinuousSemigroup.generator_domain]
    · refine (congrFun hΔ y).trans ?_
      rw [ContDiffBump.coe_normedConvolutionBUC, ContDiffBump.coe_normedConvolutionBUC]
      exact laplacian_convolution_apply_eq_of_integral_laplacian_smul_eq (Ω := ⊤)
        f.val.continuous.locallyIntegrable h (ρ n).contDiff_normed
        (ρ n).hasCompactSupport_normed fun _ _ ↦ trivial
  have hρ := ContDiffBump.tendsto_rOut_shrinking (c := (0 : E)) one_pos
  exact S.isClosed_generator.mem_of_tendsto
    ((ContDiffBump.tendsto_normedConvolutionBUC hρ volume f).prodMk_nhds
      (ContDiffBump.tendsto_normedConvolutionBUC hρ volume g))
    (Eventually.of_forall hgraph)

/-- **The domain of the heat generator on bounded uniformly continuous functions** is the set of
`f ∈ BUC` whose distributional Laplacian has a bounded uniformly continuous representative. -/
theorem mem_domain_heatSemigroupBUC_iff {f : uniformContinuousSubmodule ℝ E F} :
    f ∈ (heatSemigroupBUC (E := E) (F := F)).domain ↔
      ∃ g : uniformContinuousSubmodule ℝ E F, ∀ φ : 𝓓(⊤, ℝ),
        ∫ x, Δ (φ : E → ℝ) x • (f.val : E → F) x = ∫ x, (φ : E → ℝ) x • (g.val : E → F) x := by
  simp only [← StronglyContinuousSemigroup.generator_domain, LinearPMap.mem_domain_iff,
    mem_graph_generator_heatSemigroupBUC_iff]

/-- The heat generator sends `f` in its domain to `g` when `Δf = g` in the sense of
distributions. -/
theorem generator_heatSemigroupBUC_eq_of_integral_laplacian_smul_eq
    {f : (heatSemigroupBUC (E := E) (F := F)).generator.domain}
    {g : uniformContinuousSubmodule ℝ E F}
    (h : ∀ φ : 𝓓(⊤, ℝ),
      ∫ x, Δ (φ : E → ℝ) x • ((f : uniformContinuousSubmodule ℝ E F).val : E → F) x =
        ∫ x, (φ : E → ℝ) x • (g.val : E → F) x) :
    (heatSemigroupBUC (E := E) (F := F)).generator f = g :=
  ((LinearPMap.image_iff f.property).2 (mem_graph_generator_heatSemigroupBUC_iff.2 h)).symm

end TauCeti
