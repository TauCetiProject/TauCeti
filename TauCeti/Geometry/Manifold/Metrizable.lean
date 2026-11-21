/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Metrizable
public import Mathlib.Topology.Sets.Opens

/-!
# Open subsets of σ-compact manifolds

An open subset of a σ-compact charted space modelled on a finite-dimensional space is again
σ-compact: the ambient space is locally compact and second countable, and both properties pass to
open subsets. When the ambient space is also Hausdorff, Mathlib's `Manifold.metrizableSpace` then
makes the open subset metrizable, hence normal. These are the hypotheses of Mathlib's smooth
Urysohn lemma `exists_contMDiffMap_zero_one_nhds_of_isClosed` for the open subset, which is how
smooth cut-off functions on open subsets are produced.

## Main results

* `TauCeti.Manifold.sigmaCompactSpace_opens`: an open subset is σ-compact.
* `TauCeti.Manifold.normalSpace_opens`: an open subset of a Hausdorff such space is normal.
-/

public section

open TopologicalSpace

namespace TauCeti.Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M]

/-- An open subset of a σ-compact charted space modelled on a finite-dimensional space is
σ-compact. -/
theorem sigmaCompactSpace_opens (I : ModelWithCorners ℝ E H) [ChartedSpace H M] (W : Opens M) :
    SigmaCompactSpace W := by
  have := I.locallyCompactSpace
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  have : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace H W
  infer_instance

/-- An open subset of a Hausdorff σ-compact charted space modelled on a finite-dimensional space
is normal. -/
theorem normalSpace_opens (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    (W : Opens M) : NormalSpace W :=
  have := sigmaCompactSpace_opens I W
  have := Manifold.metrizableSpace I W
  inferInstance

end TauCeti.Manifold
