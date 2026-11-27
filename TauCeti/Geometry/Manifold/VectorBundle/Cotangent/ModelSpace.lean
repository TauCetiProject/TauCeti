/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens

/-!
# The cotangent bundle of a normed space

The cotangent bundle of a normed space `E`, regarded as a manifold modelled on itself, is the
product of `E` with its dual:

`T*E ≃ E × (E →L[𝕜] 𝕜)`, `p ∈ T*_q E ↦ (q, p)`

(`TauCeti.CotangentBundle.modelSpaceDiffeomorph`). A tangent space of `E` is `E` itself, so a
covector at `q` is an element of the dual `E →L[𝕜] 𝕜`; the content of the statement is that this
identification is a smooth diffeomorphism for the manifold structure of the cotangent bundle,
whose canonical trivializations over the model space read a covector as itself.

This is the cotangent analogue of Mathlib's `tangentBundleModelSpaceDiffeomorph`. It gives global
coordinates `(q, p)` on `T*E`; it is the preferred chart of `T*E` at every covector
(`TauCeti.CotangentBundle.coe_modelSpaceDiffeomorph_eq_extChartAt`), so its differential is the
identity (`TauCeti.CotangentBundle.mfderiv_modelSpaceDiffeomorph`). For the line, reading a
covector `p` through its value `p 1` gives the global coordinates `T*𝕜 ≃ 𝕜 × 𝕜`,
`(q, p) ↦ (q, p 1)` (`TauCeti.CotangentBundle.lineDiffeomorph`). In these coordinates the canonical
symplectic form of the cotangent bundle is a constant linear form
(`TauCeti.Geometry.Symplectic.Cotangent.Bundle.ModelSpace`).

Over an open subset `U` of `E`, a covector is likewise an element of the dual of `E`, and a map
into `T*U` is continuous as soon as its base point and its covector depend continuously on the
parameter (`TauCeti.CotangentBundle.continuous_totalSpaceMk_opens`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- Over the model space, the canonical trivialization at any point reads a covector as itself. -/
private theorem trivializationAt_snd_modelSpace (q : E) (z : CotangentBundle 𝓘(𝕜, E) E) :
    (trivializationAt (E →L[𝕜] 𝕜) (fun x : E ↦ TangentSpace 𝓘(𝕜, E) x →L[𝕜] 𝕜) q z).2 = z.snd := by
  rw [trivializationAt_mk_snd, TangentBundle.symmL_model_space]
  -- The covector `z.2` precomposed with the identity of `E`.
  exact ContinuousLinearMap.comp_id _

/-- **The cotangent bundle of a normed space is the product with its dual.** The smooth
diffeomorphism `T*E ≃ E × (E →L[𝕜] 𝕜)` sending a covector `p` at `q` to `(q, p)`. -/
def modelSpaceDiffeomorph :
    CotangentBundle 𝓘(𝕜, E) E ≃ₘ⟮𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] 𝕜), 𝓘(𝕜, E × (E →L[𝕜] 𝕜))⟯
      E × (E →L[𝕜] 𝕜) where
  toFun z := (z.proj, z.snd)
  invFun w := TotalSpace.mk' (E →L[𝕜] 𝕜) w.1 w.2
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun z := by
    -- The two components are the projection and the fibre coordinate of the trivialization.
    refine ContMDiffAt.prodMk_space
      ((contMDiff_proj (IB := 𝓘(𝕜, E)) (fun x : E ↦ TangentSpace 𝓘(𝕜, E) x →L[𝕜] 𝕜)) z) ?_
    have h := (contMDiffAt_totalSpace_iff (IM := 𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (IB := 𝓘(𝕜, E))
      (n := ∞) (f := id) (x₀ := z)).1 contMDiffAt_id
    simpa only [id, trivializationAt_snd_modelSpace] using h.2
  contMDiff_invFun w := by
    refine contMDiffAt_totalSpace_iff.2 ⟨contDiff_fst.contMDiff.contMDiffAt, ?_⟩
    simp only [trivializationAt_snd_modelSpace]
    exact contDiff_snd.contMDiff.contMDiffAt

/-- `modelSpaceDiffeomorph` sends a covector to its base point and its value in the dual. -/
@[simp]
theorem modelSpaceDiffeomorph_apply (z : CotangentBundle 𝓘(𝕜, E) E) :
    modelSpaceDiffeomorph E z = (z.proj, z.snd) :=
  (rfl)

/-- The inverse of `modelSpaceDiffeomorph` reads `(q, p)` as the covector `p` at `q`. -/
@[simp]
theorem modelSpaceDiffeomorph_symm_apply (w : E × (E →L[𝕜] 𝕜)) :
    (modelSpaceDiffeomorph E).symm w = TotalSpace.mk' (E →L[𝕜] 𝕜) w.1 w.2 :=
  (rfl)

/-- `modelSpaceDiffeomorph` is the preferred chart of the cotangent bundle at every covector: over
the model space all these charts are the same global chart. -/
theorem coe_modelSpaceDiffeomorph_eq_extChartAt (z₀ : CotangentBundle 𝓘(𝕜, E) E) :
    ⇑(modelSpaceDiffeomorph E) = extChartAt (𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] 𝕜)) z₀ := by
  funext z
  rw [extChartAt_apply, TangentBundle.symmL_model_space, modelSpaceDiffeomorph_apply]
  -- The base chart of the model space is the identity, and so is the tangent trivialization.
  exact Prod.ext rfl (ContinuousLinearMap.comp_id _).symm

/-- The differential of `modelSpaceDiffeomorph` is the identity: a tangent vector of `T*E` at a
covector is its own coordinate vector `(δq, δp)`. -/
@[simp]
theorem mfderiv_modelSpaceDiffeomorph (z : CotangentBundle 𝓘(𝕜, E) E) :
    mfderiv (𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] 𝕜)) 𝓘(𝕜, E × (E →L[𝕜] 𝕜)) (modelSpaceDiffeomorph E) z =
      ContinuousLinearMap.id 𝕜 (E × (E →L[𝕜] 𝕜)) := by
  rw [coe_modelSpaceDiffeomorph_eq_extChartAt E z]
  exact mfderiv_extChartAt_self

variable (𝕜) in
/-- The linear coordinates `(q, p) ↦ (q, p 1)` of `𝕜 × (𝕜 →L[𝕜] 𝕜)`. -/
private def lineEquiv : (𝕜 × (𝕜 →L[𝕜] 𝕜)) ≃L[𝕜] 𝕜 × 𝕜 :=
  (ContinuousLinearEquiv.refl 𝕜 𝕜).prodCongr
    (ContinuousLinearMap.toSpanSingletonLIE 𝕜 𝕜).toContinuousLinearEquiv.symm

variable (𝕜) in
/-- `lineEquiv` reads a covector `p` as its value `p 1`. -/
private theorem lineEquiv_apply (v : 𝕜 × (𝕜 →L[𝕜] 𝕜)) : lineEquiv 𝕜 v = (v.1, v.2 1) := by
  simp [lineEquiv]

variable (𝕜) in
/-- **The cotangent bundle of the line is the plane.** The smooth diffeomorphism
`T*𝕜 ≃ 𝕜 × 𝕜` sending a covector `p` at `q` to `(q, p 1)`: the covector `p` is multiplication by
its value `p 1` on the unit tangent vector. -/
def lineDiffeomorph :
    CotangentBundle 𝓘(𝕜) 𝕜 ≃ₘ⟮𝓘(𝕜).prod 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜), 𝓘(𝕜, 𝕜 × 𝕜)⟯ 𝕜 × 𝕜 :=
  (modelSpaceDiffeomorph 𝕜).trans (lineEquiv 𝕜).toDiffeomorph

variable (𝕜) in
/-- `lineDiffeomorph` sends a covector `p` at `q` to `(q, p 1)`. -/
@[simp]
theorem lineDiffeomorph_apply (z : CotangentBundle 𝓘(𝕜) 𝕜) :
    lineDiffeomorph 𝕜 z = (z.proj, z.snd (1 : 𝕜)) :=
  (rfl)

variable (𝕜) in
/-- The inverse of `lineDiffeomorph` reads `(q, a)` as the covector `v ↦ v a` at `q`. -/
@[simp]
theorem lineDiffeomorph_symm_apply (w : 𝕜 × 𝕜) :
    (lineDiffeomorph 𝕜).symm w =
      TotalSpace.mk' (𝕜 →L[𝕜] 𝕜) w.1 (ContinuousLinearMap.toSpanSingleton 𝕜 w.2) :=
  (rfl)

variable (𝕜) in
/-- The differential of `lineDiffeomorph` reads a tangent vector `(δq, δp)` of `T*𝕜` as
`(δq, δp 1)`. -/
@[simp]
theorem mfderiv_lineDiffeomorph_apply (z : CotangentBundle 𝓘(𝕜) 𝕜) (v : 𝕜 × (𝕜 →L[𝕜] 𝕜)) :
    mfderiv (𝓘(𝕜).prod 𝓘(𝕜, 𝕜 →L[𝕜] 𝕜)) 𝓘(𝕜, 𝕜 × 𝕜) (lineDiffeomorph 𝕜) z v = (v.1, v.2 1) := by
  have he : mfderiv 𝓘(𝕜, 𝕜 × (𝕜 →L[𝕜] 𝕜)) 𝓘(𝕜, 𝕜 × 𝕜) (lineEquiv 𝕜) (modelSpaceDiffeomorph 𝕜 z) =
      (lineEquiv 𝕜 : 𝕜 × (𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜 × 𝕜) :=
    (mfderiv_eq_fderiv).trans (lineEquiv 𝕜).fderiv
  have hcomp := mfderiv_comp_apply (I' := 𝓘(𝕜, 𝕜 × (𝕜 →L[𝕜] 𝕜))) z
    ((lineEquiv 𝕜).toDiffeomorph.mdifferentiable (by simp) _)
    ((modelSpaceDiffeomorph 𝕜).mdifferentiable (by simp) z) v
  rw [mfderiv_modelSpaceDiffeomorph] at hcomp
  -- The identity of the tangent space followed by `lineEquiv`, which reads `p` as `p 1`.
  rw [lineDiffeomorph, Diffeomorph.coe_trans, hcomp, ContinuousLinearEquiv.coe_toDiffeomorph, he]
  exact lineEquiv_apply 𝕜 v

variable {E} in
/-- **Continuous covector fields over an open subset of a normed space.** Let `U` be an open subset
of a normed space `E`. A map into the cotangent bundle of `U`, sending `x` to the covector `φ x` of
`E` at the point `β x` of `U`, is continuous when `β` and `φ` are. -/
theorem continuous_totalSpaceMk_opens {U : TopologicalSpace.Opens E} {X : Type*}
    [TopologicalSpace X] {β : X → U} (hβ : Continuous β) {φ : X → E →L[𝕜] 𝕜}
    (hφ : Continuous φ) :
    Continuous fun x ↦ (TotalSpace.mk' (E →L[𝕜] 𝕜) (β x) (φ x) : CotangentBundle 𝓘(𝕜, E) U) := by
  -- Through the open embedding `T*U → T*E`, this is the map `x ↦ (β x, φ x)` into `E × E*`.
  refine (isOpenEmbedding_openInclusion U).isInducing.continuous_iff.2 ?_
  have h : (openInclusion U ∘ fun x ↦
      (TotalSpace.mk' (E →L[𝕜] 𝕜) (β x) (φ x) : CotangentBundle 𝓘(𝕜, E) U)) =
      (modelSpaceDiffeomorph E).symm ∘ fun x ↦ ((β x : E), φ x) := by
    funext x
    rw [Function.comp_apply, openInclusion_def, Function.comp_apply,
      modelSpaceDiffeomorph_symm_apply]
    congr 1
    ext v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      Manifold.tangentSpaceOpenEquiv_symm_apply]
    -- Both sides evaluate `φ x` at `v`, read in the tangent spaces of `U` and of `E`.
    rfl
  rw [h]
  exact (modelSpaceDiffeomorph E).symm.continuous.comp
    ((continuous_subtypeVal.comp hβ).prodMk hφ)

end TauCeti.CotangentBundle
