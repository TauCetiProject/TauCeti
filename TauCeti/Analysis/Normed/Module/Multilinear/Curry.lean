/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Reindexing and currying continuous multilinear maps

Mathlib's `ContinuousMultilinearMap.domDomCongrₗᵢ` packages the reindexing of the arguments of a
continuous multilinear map along an equivalence of index types as a linear isometric equivalence.
This file records its evaluation lemma.

Separating the last variable of a continuous multilinear map with
`ContinuousMultilinearMap.curryRight` preserves distances, so it is `1`-Lipschitz; it also
sends `0` to `0`.

## Main declarations

* `ContinuousMultilinearMap.domDomCongrₗᵢ_apply`: `domDomCongrₗᵢ` applied to a map is
  `ContinuousMultilinearMap.domDomCongr`.
* `ContinuousMultilinearMap.edist_curryRight` and
  `ContinuousMultilinearMap.lipschitzWith_curryRight`: separating the last variable preserves
  distances.
* `ContinuousMultilinearMap.curryRight_zero`: separating the last variable of `0` gives `0`.
-/

public section

namespace ContinuousMultilinearMap

section domDomCongr

variable {𝕜 ι ι' E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [Fintype ι']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Evaluation of the isometric reindexing of continuous multilinear maps. -/
@[simp]
theorem domDomCongrₗᵢ_apply (σ : ι ≃ ι') (g : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    domDomCongrₗᵢ 𝕜 E F σ g = g.domDomCongr σ :=
  rfl

end domDomCongr

section curryRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {G : Type*} [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {n : ℕ} {Ei : Fin (n + 1) → Type*} [∀ i, NormedAddCommGroup (Ei i)]
  [∀ i, NormedSpace 𝕜 (Ei i)]

/-- Separating the last variable of the zero multilinear map gives the zero map. -/
@[simp]
theorem curryRight_zero : (0 : ContinuousMultilinearMap 𝕜 Ei G).curryRight = 0 :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).map_zero

/-- Separating the last variable of a continuous multilinear map preserves distances. -/
@[simp]
theorem edist_curryRight (f g : ContinuousMultilinearMap 𝕜 Ei G) :
    edist f.curryRight g.curryRight = edist f g :=
  (continuousMultilinearCurryRightEquiv 𝕜 Ei G).edist_map f g

/-- Separating the last variable of a continuous multilinear map is `1`-Lipschitz. -/
theorem lipschitzWith_curryRight :
    LipschitzWith 1 fun f : ContinuousMultilinearMap 𝕜 Ei G ↦ f.curryRight :=
  LipschitzWith.of_edist_le fun f g ↦ (edist_curryRight f g).le

end curryRight

end ContinuousMultilinearMap
