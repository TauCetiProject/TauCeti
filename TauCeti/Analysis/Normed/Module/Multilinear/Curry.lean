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

Separating the last variable of a continuous multilinear map with
`ContinuousMultilinearMap.curryRight` preserves distances, so it is `1`-Lipschitz; it also
sends `0` to `0`. Conversely, uncurrying `0`-multilinear maps and right-uncurrying continuous
multilinear maps are continuous `𝕜'`-linear maps whenever `𝕜` and `𝕜'` commute on the target
(`ContinuousMultilinearMap.uncurry0L`, `ContinuousMultilinearMap.uncurryRightL`,
`ContinuousMultilinearMap.uncurryRightL'`).

## Main declarations

* `ContinuousMultilinearMap.domDomCongrₗᵢ_apply`: `domDomCongrₗᵢ` applied to a map is
  `ContinuousMultilinearMap.domDomCongr`.
* `ContinuousMultilinearMap.edist_curryRight` and
  `ContinuousMultilinearMap.lipschitzWith_curryRight`: separating the last variable preserves
  distances.
* `ContinuousMultilinearMap.curryRight_zero`: separating the last variable of `0` gives `0`.
* `ContinuousMultilinearMap.uncurry0L`: zeroth-order uncurrying as a continuous `𝕜'`-linear map.
* `ContinuousMultilinearMap.uncurryRightL` and `ContinuousMultilinearMap.uncurryRightL'`:
  right uncurrying as a continuous `𝕜'`-linear map.
* `ContinuousMultilinearMap.curryLeft_continuousMultilinearCurryRightEquiv'_symm`: separating the
  first variable commutes with joining the last one.
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

/-- The zeroth-order uncurrying `G → (E [×0]→L[𝕜] G)`, bundled as a continuous `𝕜'`-linear map
when `𝕜` and `𝕜'` commute on `G`. -/
noncomputable def uncurry0L (E G : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    G →L[𝕜'] (E [×0]→L[𝕜] G) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMultilinearMap.uncurry0 𝕜 E
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
    1 fun g ↦ by simp

/-- Evaluation of `ContinuousMultilinearMap.uncurry0L`. -/
@[simp]
theorem uncurry0L_apply {𝕜 𝕜' E G : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (g : G) :
    uncurry0L 𝕜 𝕜' E G g = ContinuousMultilinearMap.uncurry0 𝕜 E g :=
  (rfl)

/-- Right uncurrying of continuous `𝕜`-multilinear maps, bundled as a continuous `𝕜'`-linear map
when `𝕜` and `𝕜'` commute on `G`. -/
noncomputable def uncurryRightL {n : ℕ} (Ei : Fin (n + 1) → Type*)
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] (G : Type*)
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    ContinuousMultilinearMap 𝕜 (fun i : Fin n ↦ Ei i.castSucc) (Ei (Fin.last n) →L[𝕜] G) →L[𝕜']
      ContinuousMultilinearMap 𝕜 Ei G :=
  LinearMap.mkContinuous
    { toFun := (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
    1 fun Φ ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact ((continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm.norm_map Φ).le

/-- Evaluation of `ContinuousMultilinearMap.uncurryRightL`. -/
@[simp]
theorem uncurryRightL_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {Ei : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (Φ : ContinuousMultilinearMap 𝕜 (fun i : Fin n ↦ Ei i.castSucc)
      (Ei (Fin.last n) →L[𝕜] G)) :
    uncurryRightL 𝕜 𝕜' Ei G Φ = (continuousMultilinearCurryRightEquiv 𝕜 Ei G).symm Φ :=
  (rfl)

/-- Non-dependent specialization of `ContinuousMultilinearMap.uncurryRightL` on `Fin (n + 1)`. -/
noncomputable def uncurryRightL' (n : ℕ) (E G : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G] :
    (E [×n]→L[𝕜] (E →L[𝕜] G)) →L[𝕜'] (E [×n + 1]→L[𝕜] G) :=
  uncurryRightL 𝕜 𝕜' (fun _ ↦ E) G

/-- Evaluation of `ContinuousMultilinearMap.uncurryRightL'`. -/
@[simp]
theorem uncurryRightL'_apply {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] {n : ℕ} {E G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]
    (Φ : E [×n]→L[𝕜] (E →L[𝕜] G)) :
    uncurryRightL' 𝕜 𝕜' n E G Φ = (continuousMultilinearCurryRightEquiv' 𝕜 n E G).symm Φ :=
  (rfl)

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
