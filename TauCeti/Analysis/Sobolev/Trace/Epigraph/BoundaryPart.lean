/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Epigraph.Basic
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables

/-!
# Flattening boundary parts of the region above a Lipschitz graph

Let `φ : E → ℝ` be `K`-Lipschitz. Precomposition with inverse graph flattening
`(t, y) ↦ (t + φ y, y)` identifies `W^{1,p}` of the region above the graph of `φ`
(`TauCeti.normalEpigraph φ`) with `W^{1,p}` of the half-space `{0 < t}`
(`TauCeti.W1p.normalEpigraphEquivL`). This file shows that for `1 ≤ p < ∞` the identification
respects vanishing on a part of the boundary: `u` lies in `W^{1,p}_Γ` of the region, in the sense
of `TauCeti.w1pVanishingOnSubmodule`, exactly when its flattening lies in `W^{1,p}_{Γ'}` of the
half-space, where `Γ'` is the image of `Γ` under graph flattening `(t, y) ↦ (t - φ y, y)`. A part
`{(φ y, y) | y ∈ B}` of the graph goes to the part `{0} × B` of the boundary hyperplane.

Graph flattening is only Lipschitz, not smooth, so this rests on the Lipschitz transport
`TauCeti.W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule_iff`. It reduces
statements about functions vanishing on a part of a Lipschitz graph to the half-space with a part
of its boundary hyperplane, for instance the description of `W^{1,p}_Γ` by the trace.

## Main declarations

* `TauCeti.W1p.normalEpigraphEquivL_mem_w1pVanishingOnSubmodule_iff`: flattening preserves and
  reflects vanishing on a boundary part.

## References

* S. Bauer, D. Pauly, M. Schomburg, *The Maxwell compactness property in bounded weak Lipschitz
  domains with mixed boundary conditions*, SIAM J. Math. Anal. 48 (2016), Lemma 3.1 and
  Appendix A (boundary parts are flattened by bi-Lipschitz charts).
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : C(E, ℝ)} {K : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Flattening preserves and reflects vanishing on a boundary part.** For `1 ≤ p < ∞` and any
set `Γ`, the flattening of `u ∈ W^{1,p}` of the region above the graph of a Lipschitz `φ` lies in
`W^{1,p}_{Γ'}` of the half-space `{0 < t}`, for the image `Γ'` of `Γ` under graph flattening,
exactly when `u` lies in `W^{1,p}_Γ` of the region. -/
theorem W1p.normalEpigraphEquivL_mem_w1pVanishingOnSubmodule_iff (hp : p ≠ ∞)
    (hφ : LipschitzWith K φ) (Γ : Set (WithLp 2 (ℝ × E))) (u : W1p volume (normalEpigraph φ) p) :
    W1p.normalEpigraphEquivL hφ u ∈ w1pVanishingOnSubmodule volume (normalHalfSpace 0) p
        (graphFlattening φ φ.continuous '' Γ) ↔
      u ∈ w1pVanishingOnSubmodule volume (normalEpigraph φ) p Γ := by
  have hL := lipschitzWith_graphFlattening_symm hφ
  rw [W1p.normalEpigraphEquivL_apply hφ hL.locallyLipschitz.locallyLipschitzOn
    (fun x _ => norm_fderiv_le_of_lipschitz ℝ hL), ← Homeomorph.preimage_symm]
  exact W1p.compMeasurePreservingL_mem_w1pVanishingOnSubmodule_iff hp _ hL.locallyLipschitz
    (lipschitzWith_graphFlattening hφ).locallyLipschitz _ _ _ _
    (fun _ _ => norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_graphFlattening hφ))

end TauCeti
