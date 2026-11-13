/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.SecondCountable

/-!
# Second countability of spaces of `C^n` bundle sections

The compact derivative topology `ContMDiffSection.frameTopology` on the `C^n` sections of a
vector bundle is induced by the tuple of weak Whitney frame coefficients
(`ContMDiffSection.isInducing_sectionFrameCoordinates`). When there are countably many frame
domains, each sigma-compact, the base field is complete, the model space is locally compact, and
the model fibre is second countable, each coefficient space is second countable
(`ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`), and so is the
section space. In particular it is separable. No covering condition is needed.

This covers the spaces of `C^k` symmetric tensor fields, such as Riemannian metrics, on which
genericity arguments vary the metric.

## Main results

* `ContMDiffSection.secondCountableTopology_frameTopology`: the frame topology is second
  countable.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1.
-/

public section

noncomputable section

open Bundle Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- For countably many sigma-compact frame domains, on a manifold with locally compact model over a
complete field and with second-countable model fibre, the compact derivative topology on `C^n`
sections is second countable, hence separable. -/
theorem secondCountableTopology_frameTopology [Countable ι] [CompleteSpace 𝕜]
    [LocallyCompactSpace E] [SecondCountableTopology F] [∀ i, SigmaCompactSpace (U i)] :
    let _ := frameTopology (I := I) (n := n) e U hU
    SecondCountableTopology Cₛ^n⟮I; F, V⟯ := by
  let _ := frameTopology (I := I) (n := n) e U hU
  exact (isInducing_sectionFrameCoordinates e U hU).secondCountableTopology

end ContMDiffSection
