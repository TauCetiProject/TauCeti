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
continuous multilinear map along an equivalence of index types as a linear isometric equivalence,
and `continuousMultilinearCurryLeftEquiv` packages `ContinuousMultilinearMap.curryLeft` the same
way. This file records the evaluation lemmas identifying the equivalences with the underlying
operations.

## Main declarations

* `ContinuousMultilinearMap.domDomCongrₗᵢ_apply`: `domDomCongrₗᵢ` applied to a map is
  `ContinuousMultilinearMap.domDomCongr`.
* `continuousMultilinearCurryLeftEquiv_eq_curryLeft`: `continuousMultilinearCurryLeftEquiv`
  applied to a map is `ContinuousMultilinearMap.curryLeft`.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 ι ι' E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [Fintype ι']
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Evaluation of the isometric reindexing of continuous multilinear maps. -/
@[simp]
theorem domDomCongrₗᵢ_apply (σ : ι ≃ ι') (g : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    domDomCongrₗᵢ 𝕜 E F σ g = g.domDomCongr σ :=
  rfl

end ContinuousMultilinearMap

section CurryLeft

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ} {Ei : Fin (n + 1) → Type*}
  [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Left currying of an `(n + 1)`-multilinear map by the currying equivalence is
`ContinuousMultilinearMap.curryLeft`. -/
theorem continuousMultilinearCurryLeftEquiv_eq_curryLeft (f : ContinuousMultilinearMap 𝕜 Ei G) :
    continuousMultilinearCurryLeftEquiv 𝕜 Ei G f = f.curryLeft := by
  ext x v
  rw [continuousMultilinearCurryLeftEquiv_apply, ContinuousMultilinearMap.curryLeft_apply]

end CurryLeft
