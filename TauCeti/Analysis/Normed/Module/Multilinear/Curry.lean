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
way. This file records the evaluation lemmas identifying these equivalences with the underlying
operations, and how joining the last variable with Mathlib's
`continuousMultilinearCurryRightEquiv'` interacts with separating the first one.

Separating the last variable of a continuous multilinear map with
`ContinuousMultilinearMap.curryRight` preserves distances, so it is `1`-Lipschitz; it also
sends `0` to `0`. Conversely, zeroth-order currying and right-currying of continuous
`𝕜`-multilinear maps are `𝕜'`-linear isometry equivalences whenever `𝕜` and `𝕜'` commute on the
target (`ContinuousMultilinearMap.curryFin0Mixedₗᵢ`, `ContinuousMultilinearMap.curryRightMixedₗᵢ`,
`ContinuousMultilinearMap.curryRightMixedₗᵢ'`).

## Main declarations

* `ContinuousMultilinearMap.domDomCongrₗᵢ_apply`: `domDomCongrₗᵢ` applied to a map is
  `ContinuousMultilinearMap.domDomCongr`.
* `ContinuousMultilinearMap.edist_curryRight` and
  `ContinuousMultilinearMap.lipschitzWith_curryRight`: separating the last variable preserves
  distances.
* `ContinuousMultilinearMap.curryRight_zero`: separating the last variable of `0` gives `0`.
* `ContinuousMultilinearMap.curryFin0Mixedₗᵢ`: zeroth-order currying as a `𝕜'`-linear isometry
  equivalence.
* `ContinuousMultilinearMap.curryRightMixedₗᵢ` and `ContinuousMultilinearMap.curryRightMixedₗᵢ'`:
  right currying as a `𝕜'`-linear isometry equivalence.
* `ContinuousMultilinearMap.curryLeft_continuousMultilinearCurryRightEquiv'_symm`: separating the
  first variable commutes with joining the last one.
* `continuousMultilinearCurryLeftEquiv_eq_curryLeft`: `continuousMultilinearCurryLeftEquiv`
  applied to a map is `ContinuousMultilinearMap.curryLeft`.
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

section MixedScalar

variable (𝕜 𝕜' : Type*) [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']

/-- The zeroth-order currying `(E [×0]→L[𝕜] G) ≃ₗᵢ[𝕜'] G`, bundled as a `𝕜'`-linear isometry
equivalence when `𝕜` and `𝕜'` commute on `G`. -/
noncomputable def curryFin0Mixedₗᵢ (E G : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    (E [×0]→L[𝕜] G) ≃ₗᵢ[𝕜'] G where
  toLinearEquiv :=
    { toFun := continuousMultilinearCurryFin0 𝕜 E G
      invFun := (continuousMultilinearCurryFin0 𝕜 E G).symm
      left_inv := (continuousMultilinearCurryFin0 𝕜 E G).left_inv
      right_inv := (continuousMultilinearCurryFin0 𝕜 E G).right_inv
      map_add' := map_add _
      map_smul' := fun c f ↦ by simp [continuousMultilinearCurryFin0_apply] }
  norm_map' := (continuousMultilinearCurryFin0 𝕜 E G).norm_map

/-- Forward evaluation of `ContinuousMultilinearMap.curryFin0Mixedₗᵢ`. -/
@[simp]
theorem curryFin0Mixedₗᵢ_apply {𝕜 𝕜' E G : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (f : E [×0]→L[𝕜] G) :
    curryFin0Mixedₗᵢ 𝕜 𝕜' E G f = f 0 := by
  rfl

/-- Inverse evaluation of `ContinuousMultilinearMap.curryFin0Mixedₗᵢ`. -/
@[simp]
theorem curryFin0Mixedₗᵢ_symm_apply {𝕜 𝕜' E G : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (g : G) :
    (curryFin0Mixedₗᵢ 𝕜 𝕜' E G).symm g = ContinuousMultilinearMap.uncurry0 𝕜 E g := by
  rfl

/-- Right currying of continuous `𝕜`-multilinear maps, bundled as a `𝕜'`-linear isometry
equivalence when `𝕜` and `𝕜'` commute on `G`. -/
noncomputable def curryRightMixedₗᵢ {n : ℕ} (Ei : Fin (n + 1) → Type*)
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] (G : Type*)
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    ContinuousMultilinearMap 𝕜 Ei G ≃ₗᵢ[𝕜']
      ContinuousMultilinearMap 𝕜 (fun i : Fin n ↦ Ei i.castSucc) (Ei (Fin.last n) →L[𝕜] G) where
  toLinearEquiv :=
    { toFun := continuousMultilinearCurryRightEquiv 𝕜 Ei G
      invFun := (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm
      left_inv := (continuousMultilinearCurryRightEquiv 𝕜 Ei G).left_inv
      right_inv := (continuousMultilinearCurryRightEquiv 𝕜 Ei G).right_inv
      map_add' := map_add _
      map_smul' := fun c f ↦ by ext v x; simp }
  norm_map' := (continuousMultilinearCurryRightEquiv 𝕜 Ei G).norm_map

/-- Forward evaluation of `ContinuousMultilinearMap.curryRightMixedₗᵢ`. -/
@[simp]
theorem curryRightMixedₗᵢ_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {Ei : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (f : ContinuousMultilinearMap 𝕜 Ei G) :
    curryRightMixedₗᵢ 𝕜 𝕜' Ei G f = f.curryRight := by
  rfl

/-- Inverse evaluation of `ContinuousMultilinearMap.curryRightMixedₗᵢ`. -/
@[simp]
theorem curryRightMixedₗᵢ_symm_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {Ei : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (Φ : ContinuousMultilinearMap 𝕜 (fun i : Fin n ↦ Ei i.castSucc)
      (Ei (Fin.last n) →L[𝕜] G)) :
    (curryRightMixedₗᵢ 𝕜 𝕜' Ei G).symm Φ =
      (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm Φ := by
  rfl

/-- Non-dependent specialization of `ContinuousMultilinearMap.curryRightMixedₗᵢ` on
`Fin (n + 1)`. -/
noncomputable def curryRightMixedₗᵢ' (n : ℕ) (E G : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    (E [×n + 1]→L[𝕜] G) ≃ₗᵢ[𝕜'] (E [×n]→L[𝕜] (E →L[𝕜] G)) :=
  curryRightMixedₗᵢ 𝕜 𝕜' (fun _ ↦ E) G

/-- Forward evaluation of `ContinuousMultilinearMap.curryRightMixedₗᵢ'`. -/
@[simp]
theorem curryRightMixedₗᵢ'_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {E G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (f : E [×n + 1]→L[𝕜] G) :
    curryRightMixedₗᵢ' 𝕜 𝕜' n E G f = continuousMultilinearCurryRightEquiv' 𝕜 n E G f := by
  rfl

/-- Inverse evaluation of `ContinuousMultilinearMap.curryRightMixedₗᵢ'`. -/
@[simp]
theorem curryRightMixedₗᵢ'_symm_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {E G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (Φ : E [×n]→L[𝕜] (E →L[𝕜] G)) :
    (curryRightMixedₗᵢ' 𝕜 𝕜' n E G).symm Φ =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E G).symm Φ := by
  rfl

end MixedScalar

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
