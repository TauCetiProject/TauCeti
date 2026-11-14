/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Multilinear.SecondCountable
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.CountableSeminorms
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Second countability of spaces of `C^n` maps

Let `M` be a manifold modelled on a finite-dimensional space `E` over a complete field `𝕜`, and `F`
a second-countable normed space. Choose countably many charts of `M` whose sources cover `M`, and a
compact exhaustion of each chart target. Restricting the coordinate derivatives of order at most `n`
to the compact pieces of these exhaustions gives a linear map `ContMDiffMap.chartExhaustionJet` from
the vector-valued `C^n` maps into a countable product of supremum-norm spaces of continuous maps on
compact sets. The supremum norms of its components are the compact chart derivative seminorms, which
are equivalent to the compact chart `C^k` seminorms generating the weak Whitney topology
(`ContMDiffMap.withSeminorms_chartExhaustion`), so this map induces the weak Whitney topology
(`ContMDiffMap.isInducing_chartExhaustionJet`). Each factor is second countable: the compact pieces
are compact metrizable, and the derivatives take values in a second-countable space of continuous
multilinear maps (`ContinuousMultilinearMap.secondCountableTopology`). So the space of `C^n` maps is
second countable, and in particular separable.

This holds on every sigma-compact manifold with locally compact model over a complete field, for
every regularity `n`, including manifolds with boundary or corners, because such a model is
finite-dimensional. The finite-atlas norm of `ContMDiffMap.finiteAtlasNormedAddCommGroup` carries
the weak Whitney topology by construction, so on a compact manifold the Banach space of `C^k` maps
is separable. These are the separability hypotheses of the Sard–Smale theorem and of parametric
transversality when the parameter space is a space of functions: the product of the parameter space
with a second-countable manifold, and hence every subset of it, such as the zero set of a universal
section, is again second countable.

## Main results

* `ContMDiffMap.secondCountableTopology_chartExhaustion`: the weak Whitney topology is second
  countable, given countably many covering charts with compact exhaustions.
* `ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact`: the weak Whitney
  topology is second countable on a sigma-compact manifold with locally compact model; it is a
  scoped instance in `TauCeti.ManifoldWeakWhitney`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2 (the weak topology on `C^r` maps and
  its countability properties).
-/

public section

open Set Topology
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Exhaustion

variable {n : WithTop ℕ∞} [IsManifold I n M] {ι : Type*} (c : ι → M)
  (hcover : ∀ x : M, ∃ i, x ∈ (extChartAt I (c i)).source)

include hcover in
/-- Countably many charts whose sources cover the manifold, with compact exhaustions of their
targets, make the weak Whitney topology on vector-valued `C^n` maps second countable when the
model space is finite-dimensional over a complete field and the target is second countable. -/
theorem secondCountableTopology_chartExhaustion [Countable ι] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] [SecondCountableTopology F]
    (A : ∀ i, CompactExhaustion (extChartAt I (c i)).target) :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ :=
  (isInducing_chartExhaustionJet (F := F) (n := n) c hcover A).secondCountableTopology

end Exhaustion

/-- On a sigma-compact manifold with locally compact model over a complete field, the weak Whitney
topology on `C^n` maps into a second-countable normed space is second countable, hence separable.
This holds for every regularity `n` and also on manifolds with boundary or corners. -/
theorem secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact {n : WithTop ℕ∞}
    [IsManifold I n M] [CompleteSpace 𝕜] [LocallyCompactSpace E] [SecondCountableTopology F]
    [SigmaCompactSpace M] :
    SecondCountableTopology C^n⟮I, M; 𝓘(𝕜, F), F⟯ := by
  have := FiniteDimensional.of_locallyCompactSpace 𝕜 (E := E)
  obtain ⟨s, hs, hc, ⟨A⟩⟩ := TauCeti.exists_countable_chartExhaustion (I := I) (M := M)
  have := hs.to_subtype
  exact secondCountableTopology_chartExhaustion (F := F) (n := n) (fun i : s ↦ (i : M)) hc A

scoped[TauCeti.ManifoldWeakWhitney] attribute [instance]
  ContMDiffMap.secondCountableTopology_manifoldWeakWhitney_of_sigmaCompact

end ContMDiffMap
