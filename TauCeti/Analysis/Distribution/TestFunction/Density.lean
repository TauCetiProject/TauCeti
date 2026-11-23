/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import TauCeti.Analysis.Distribution.TestFunction.Banach

/-!
# Smooth functions are dense in `𝓓^{n}_{K}(E, F)` for convex `K`

For a compact set `K` in a real normed space `E`, a real Banach space `F` and `n ≤ ∞`, the space
`𝓓^{n}_{K}(E, F)` of `Cⁿ` functions from `E` to `F` supported in `K` carries the topology of
uniform convergence of all derivatives of order at most `n`. When `K` is convex, the inclusion
`𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has dense range for all `n₂ ≤ n₁`
(`ContDiffMapSupportedIn.denseRange_monoCLM`). The approximants keep their support in `K` itself,
not merely in a neighbourhood of `K`. Density lets a property that is open in this `Cⁿ` topology,
and holds for some `Cⁿ` perturbation, hold for a smooth perturbation with the same support.

For finite `n` this is the density of smooth maps in the normed synonym
`TauCeti.NormedContDiffMapSupportedIn` (`TauCeti.NormedContDiffMapSupportedIn.dense_setOf_contDiff`,
proved by contracting towards an interior point of `K` and mollifying), transported along the
identity `TauCeti.NormedContDiffMapSupportedIn.continuousLinearEquiv`; every smooth map supported
in `K` lies in the range of the inclusion. For `n₂ = ∞` the hypothesis forces `n₁ = ∞`, and every
element of `𝓓_{K}(E, F)` is already smooth.

## Main results

* `ContDiffMapSupportedIn.denseRange_monoCLM`: for convex `K`, a Banach space `F` and `n₂ ≤ n₁`,
  the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)` has dense range; for `n₁ = ∞` this says
  that smooth functions supported in `K` are dense in `𝓓^{n₂}_{K}(E, F)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §1.3 (regularization by convolution).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition, AMS
  Colloquium Publications 52, 2012, §3.2 (Banach spaces of perturbations and smooth regular
  choices in transversality arguments).
-/

public section

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {K : Compacts E}

/-- **Smooth functions supported in a convex compact set are dense.** For convex `K`, a Banach
space `F` (`[CompleteSpace F]`) and `n₂ ≤ n₁`, the inclusion `𝓓^{n₁}_{K}(E, F) → 𝓓^{n₂}_{K}(E, F)`
has dense range. For `n₁ = ∞` this says that every `C^{n₂}` function supported in `K` is a limit,
in every derivative of order at most `n₂` uniformly, of smooth functions supported in `K`. -/
theorem denseRange_monoCLM [CompleteSpace F] (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] {n₁ n₂ : ℕ∞} (hn : n₂ ≤ n₁)
    (hK : Convex ℝ (K : Set E)) :
    DenseRange (monoCLM 𝕜 : 𝓓^{n₁}_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)) := by
  -- Every smooth function supported in `K` lies in the range of the inclusion.
  have hrange {g : 𝓓^{n₂}_{K}(E, F)} (hg : ContDiff ℝ ∞ g) :
      g ∈ range (monoCLM 𝕜 : 𝓓^{n₁}_{K}(E, F) →L[𝕜] 𝓓^{n₂}_{K}(E, F)) :=
    ⟨.of_support_subset (hg.of_le (by exact_mod_cast le_top)) g.support_subset,
      ext fun x ↦ by simp [hn]⟩
  induction n₂ using ENat.recTopCoe with
  | top => exact fun g ↦ subset_closure (hrange g.contDiff)
  | coe ℓ =>
    exact ((TauCeti.NormedContDiffMapSupportedIn.continuousLinearEquiv ℝ E F ℓ
      K).surjective.denseRange.dense_image (ContinuousLinearEquiv.continuous _)
        (TauCeti.NormedContDiffMapSupportedIn.dense_setOf_contDiff hK)).mono
      (by rintro _ ⟨g, hg, rfl⟩; exact hrange (by simpa using hg))

end ContDiffMapSupportedIn
