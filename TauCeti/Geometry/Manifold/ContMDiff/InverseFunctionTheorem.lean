/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# Charts from coordinate maps with identity derivative

Let `χ` be a `C^n` partial homeomorphism from a manifold `M` to a Banach space `E`, with `C^n`
inverse, and let `A` be a `C^n` self-map of `E` on an open set of coordinates whose derivative at
`χ x` is the identity, `1 ≤ n`. The inverse function theorem makes `A` a partial homeomorphism
`Θ` near `χ x`, and `χ.trans Θ` is again a `C^n` chart with `C^n` inverse
(`TauCeti.exists_contMDiffOn_trans_of_hasFDerivAt`). Bochner linearization applies this to an
averaged coordinate map.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 E H M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- **Charts from a map with identity derivative.** Let `χ` be a `C^n` partial homeomorphism
from `M` to `E` with `C^n` inverse, and let `A` be `C^n` on an open set `V` of coordinates, with
derivative the identity at `χ x ∈ V`, `1 ≤ n`. Then `A` is a partial homeomorphism `Θ` near `χ x`
with source in `V`, and `χ.trans Θ` is `C^n` with `C^n` inverse. -/
theorem exists_contMDiffOn_trans_of_hasFDerivAt {χ : OpenPartialHomeomorph M E}
    (hχ : ContMDiffOn I 𝓘(𝕜, E) n χ χ.source) (hχs : ContMDiffOn 𝓘(𝕜, E) I n χ.symm χ.target)
    {A : E → E} {V : Set E} (hA : ContDiffOn 𝕜 n A V) (hV : IsOpen V) {x : M} (hxV : χ x ∈ V)
    (hn : 1 ≤ n) (hAx : HasFDerivAt A (ContinuousLinearMap.id 𝕜 E) (χ x)) :
    ∃ Θ : OpenPartialHomeomorph E E, (Θ : E → E) = A ∧ χ x ∈ Θ.source ∧ Θ.source ⊆ V ∧
      ContMDiffOn I 𝓘(𝕜, E) n (χ.trans Θ) (χ.trans Θ).source ∧
      ContMDiffOn 𝓘(𝕜, E) I n (χ.trans Θ).symm (χ.trans Θ).target := by
  obtain ⟨Θ, hΘ, hxΘ, hΘV, hΘsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph hA hV hxV hn
      (e := ContinuousLinearEquiv.refl 𝕜 E) hAx.fderiv.symm
  exact ⟨Θ, hΘ, hxΘ, hΘV,
    ((hΘ ▸ hA.mono hΘV).contMDiffOn).comp (hχ.mono inter_subset_left) inter_subset_right,
    hχs.comp (hΘsymm.contMDiffOn.mono inter_subset_left) inter_subset_right⟩

end TauCeti
