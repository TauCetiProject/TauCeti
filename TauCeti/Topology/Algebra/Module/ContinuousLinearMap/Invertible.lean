/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Persistence of invertibility from convergence of inverses

The totalized inverse of a continuous linear map is zero when the map is not invertible.
Consequently, convergence of inverse maps to the inverse of an invertible map forces eventual
invertibility. This applies to inverse families without completeness or continuity of the
original family, and is useful when differentiating such families.
-/

public section

open Filter
open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousSMul 𝕜 F]

/-- If the inverses of a family converge to the inverse of an invertible map, then the family
is eventually invertible. Convergence uses the topology of bounded convergence; neither
completeness nor convergence of the original family is required. -/
theorem IsInvertible.eventually_of_tendsto_inverse {A : ι → E →L[𝕜] F} {B : E →L[𝕜] F}
    (hB : B.IsInvertible) {l : Filter ι}
    (h : Tendsto (fun i => (A i).inverse) l (𝓝 B.inverse)) :
    ∀ᶠ i in l, (A i).IsInvertible := by
  by_cases hE : Subsingleton E
  · obtain ⟨e, _⟩ := hB
    let : Subsingleton E := hE
    let : Subsingleton F := e.toEquiv.symm.subsingleton
    exact Eventually.of_forall fun i => by
      simpa only [Subsingleton.elim (A i) 0, isInvertible_zero_iff] using
        And.intro (inferInstance : Subsingleton E) (inferInstance : Subsingleton F)
  · have hne : B.inverse ≠ 0 := by
      intro hzero
      exact hE (isInvertible_zero_iff.mp (hzero ▸ hB.inverse)).2
    filter_upwards [h.eventually_ne hne] with i hi
    by_contra hA
    exact hi (inverse_of_not_isInvertible hA)

end ContinuousLinearMap
