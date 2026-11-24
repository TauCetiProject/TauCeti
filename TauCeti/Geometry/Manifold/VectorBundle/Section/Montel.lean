/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Montel
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Smooth sections of a vector bundle form a Montel space

Let `V` be a smooth vector bundle with finite-dimensional real model fibre over a boundaryless
manifold modelled on a finite-dimensional real normed space. Its smooth sections carry the
compact derivative topology `ContMDiffSection.frameTopology` of uniform convergence on compact
coordinate sets of every derivative of the frame coefficients, for a covering family of smooth
frames. This file proves that with this topology the smooth sections form a Montel space: every
closed von Neumann bounded set of sections is compact
(`ContMDiffSection.montelSpace_frameTopology`). When `V` is also a complex vector bundle, or more
generally a vector bundle over a normed field extension of `ℝ` acting compatibly, the sections form
a Montel space over that field as well
(`ContMDiffSection.montelSpace_frameTopology_of_isScalarTower`).

By Mathlib's `ContinuousLinearEquiv.toCompactConvergenceCLM`, the strong topology on the space of
continuous linear maps out of the smooth sections, in particular on their continuous dual, is
therefore the topology of uniform convergence on compact sets of sections.

The frame coefficients of a section are smooth maps on the frame domains, and the coefficient map
is a closed linear embedding of the sections into the product of these weak Whitney coefficient
spaces (`ContMDiffSection.isClosedEmbedding_sectionFrameCoordinates`), whose image is cut out by
the transition equations of the bundle. Each coefficient space is a Montel space
(`ContMDiffMap.montelSpace_manifoldWeakWhitney`), hence so is their product, and so is the closed
subspace of sections (`MontelSpace.of_isClosedEmbedding`).

## References

* F. Trèves, *Topological Vector Spaces, Distributions and Kernels*, Chapter 34.
* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for compact derivative topologies.
-/

public section

open Bundle TopologicalSpace
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For a covering family of smooth frames, the smooth sections of a vector bundle with
finite-dimensional real fibre over a boundaryless manifold modelled on a finite-dimensional real
space form a Montel space in the compact derivative topology of the frames. -/
theorem montelSpace_frameTopology (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := ∞) e U hU
    MontelSpace ℝ Cₛ^∞⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := ∞) e U hU
  have hJ := isClosedEmbedding_sectionFrameCoordinates (I := I) (n := ∞) e U hU hcover
  exact MontelSpace.of_isClosedEmbedding
    ⟨TauCeti.Manifold.sectionFrameCoordinates (I := I) (n := ∞) e U hU, hJ.continuous⟩ hJ

/-- For a covering family of smooth frames, the smooth sections of a vector bundle over a normed
field extension `𝕜'` of `ℝ`, such as a complex vector bundle, with finite-dimensional real fibre
over a boundaryless manifold modelled on a finite-dimensional real space, form a Montel space
over `𝕜'` in the compact derivative topology of the frames. -/
theorem montelSpace_frameTopology_of_isScalarTower (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedAlgebra ℝ 𝕜'] [NormedSpace 𝕜' F] [∀ x, Module 𝕜' (V x)]
    [∀ x, IsScalarTower ℝ 𝕜' (V x)] [VectorBundle 𝕜' F V] (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameTopology (I := I) (n := ∞) e U hU
    MontelSpace 𝕜' Cₛ^∞⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := ∞) e U hU
  have := montelSpace_frameTopology (I := I) e U hU hcover
  exact MontelSpace.of_isScalarTower (𝕜 := ℝ) 𝕜'

end ContMDiffSection
