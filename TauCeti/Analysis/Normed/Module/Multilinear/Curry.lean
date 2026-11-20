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
This file records its evaluation lemma, and how joining the last variable with Mathlib's
`continuousMultilinearCurryRightEquiv'` interacts with separating the first one.

## Main declarations

* `ContinuousMultilinearMap.domDomCongrₗᵢ_apply`: `domDomCongrₗᵢ` applied to a map is
  `ContinuousMultilinearMap.domDomCongr`.
* `ContinuousMultilinearMap.curryLeft_continuousMultilinearCurryRightEquiv'_symm`: separating the
  first variable commutes with joining the last one.
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

section CurryRight

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Separating the first variable commutes with joining the last one: for an `(n + 1)`-multilinear
map `M` with values in `E →L[𝕜] F`, the first variable of the `(n + 2)`-multilinear map obtained by
joining the last variable of `M` may be separated before the join. -/
theorem ContinuousMultilinearMap.curryLeft_continuousMultilinearCurryRightEquiv'_symm {n : ℕ}
    (M : E [×(n + 1)]→L[𝕜] (E →L[𝕜] F)) (v : E) :
    ((continuousMultilinearCurryRightEquiv' 𝕜 (n + 1) E F).symm M).curryLeft v =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm (M.curryLeft v) :=
  ContinuousMultilinearMap.ext fun w ↦ by
    have hw : Fin.init (Fin.cons v w : Fin (n + 2) → E) = Fin.cons v (Fin.init w) := by
      ext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rfl
      · simp only [Fin.init, Fin.cons_succ, ← Fin.succ_castSucc]
    simp [hw]

end CurryRight
