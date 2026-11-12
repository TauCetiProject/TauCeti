/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Complete
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# The weak Whitney topology on a sigma-compact manifold is completely metrizable

Let `M` be a sigma-compact boundaryless manifold modelled on a locally compact, second-countable
normed space over `ℝ` or `ℂ`, and let `F` be a Banach space. The vector-valued `C^n` maps on `M`,
for finite or smooth regularity `n`, form a completely metrizable space in the weak Whitney
topology (`ContMDiffMap.isCompletelyMetrizableSpace_manifoldWeakWhitney`): the topology is
metrizable (`ContMDiffMap.metrizableSpace_manifoldWeakWhitney_of_sigmaCompact`) and complete for
the uniform structure of this topological vector space
(`ContMDiffMap.completeSpace_manifoldWeakWhitney`), and a metrizable topological additive group
has a countably generated uniformity, so it carries a complete compatible metric.

By the Baire category theorem (`BaireSpace.of_completelyPseudoMetrizable`) this space is then a
Baire space: a countable intersection of open dense sets of `C^n` maps is dense. This is the
setting of the genericity theorems for functions on a manifold, which describe a property as
holding on a residual set of functions. On a noncompact manifold the space is not normable, so
the Baire property cannot come from a Banach space structure.

The result is registered as a scoped instance in `TauCeti.ManifoldWeakWhitney`, together with the
weak Whitney topology itself.

## Main results

* `ContMDiffMap.isCompletelyMetrizableSpace_manifoldWeakWhitney`: the weak Whitney space of
  vector-valued `C^n` maps on a sigma-compact boundaryless manifold is completely metrizable.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §4, where the spaces of
  `C^r` maps are shown to be Baire spaces.
-/

public section

open TopologicalSpace
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  [SecondCountableTopology E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {n : ℕ∞ω} [IsManifold I n M] [ENat.LEInfty n]

/-- **The weak Whitney topology is completely metrizable.** On a sigma-compact boundaryless
manifold modelled on a locally compact, second-countable space over `ℝ` or `ℂ`, the
vector-valued `C^n` maps with values in a Banach space, for finite or smooth regularity `n`, form
a completely metrizable space. In particular they form a Baire space. -/
theorem isCompletelyMetrizableSpace_manifoldWeakWhitney :
    IsCompletelyMetrizableSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  let _ : UniformSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup C^n⟮I, M; 𝓘(𝕜, F), F⟯ := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace C^n⟮I, M; 𝓘(𝕜, F), F⟯ := completeSpace_manifoldWeakWhitney
  have := metrizableSpace_manifoldWeakWhitney_of_sigmaCompact (I := I) (M := M) (F := F) (n := n)
  have : (uniformity C^n⟮I, M; 𝓘(𝕜, F), F⟯).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  infer_instance

end ContMDiffMap

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.isCompletelyMetrizableSpace_manifoldWeakWhitney
