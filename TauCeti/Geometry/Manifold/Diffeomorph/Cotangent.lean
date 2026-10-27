/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent

/-!
# Cotangent lifts of diffeomorphisms

A diffeomorphism `h : M → N` lifts to a diffeomorphism of cotangent bundles,

`T*M → T*N, (x, p) ↦ (h x, p ∘ (dh_x)⁻¹)`,

where the inverse of the differential `dh_x` is the differential of `h⁻¹` at `h x`
(`Diffeomorph.cotangent`). It is characterized by covering `h`
(`Diffeomorph.proj_cotangent`) and by preserving the pairing of covectors with tangent vectors:
the lifted covector, evaluated on `dh_x v`, is `p v` (`Diffeomorph.cotangent_snd_apply_mfderiv`).
Smoothness of the lift is the smoothness of pulling covectors back along a map,
`TauCeti.CotangentBundle.contMDiff_mk_comp_mfderiv`.

The construction is functorial: cotangent lifts preserve identity maps, inverses and composition
(`Diffeomorph.cotangent_refl`, `Diffeomorph.cotangent_symm`, `Diffeomorph.cotangent_trans`).
It is the cotangent counterpart of the tangent lift `Diffeomorph.tangent`. The cotangent lift of
a diffeomorphism preserves the Liouville form and the canonical symplectic form of the cotangent
bundle; see `TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners 𝕜 G H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

namespace Diffeomorph

open TauCeti

/-- The underlying map of the cotangent lift: a covector `p` at `x` goes to the covector
`p ∘ (dh_x)⁻¹` at `h x`, the inverse differential being the differential of `h.symm` at `h x`. -/
private def cotangentMap (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) : CotangentBundle J N :=
  TotalSpace.mk' (F →L[𝕜] 𝕜) (h z.proj) (z.2 ∘L mfderiv J I h.symm (h z.proj))

/-- The covector `cotangentMap h z` evaluates a tangent vector `w` at `h x` as `z` evaluates
`dh⁻¹ w`. -/
private theorem cotangentMap_snd_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (w : TangentSpace J (h z.proj)) :
    (h.cotangentMap z).2 w = z.2 (mfderiv J I h.symm (h z.proj) w) :=
  (rfl)

/-- Applying the cotangent lift of `h` and then that of `h.symm` returns the original covector. -/
private theorem cotangentMap_symm_cotangentMap (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    h.symm.cotangentMap (h.cotangentMap z) = z := by
  refine CotangentBundle.ext (h.symm_apply_apply z.proj) fun v ↦ ?_
  -- Evaluating both lifts in turn gives `z` applied to `dh⁻¹ (d(h⁻¹)⁻¹ v)`, and `d(h⁻¹)⁻¹ = dh`.
  have hv := h.symm.mfderiv_apply_mfderiv_symm_apply (by simp) (h z.proj) v
  exact ((cotangentMap_snd_apply _ _ v).trans (cotangentMap_snd_apply h z _)).trans
    (congrArg z.2 hv)

variable [IsManifold I 2 M] [IsManifold J 2 N] [IsManifold K 2 P]

/-- The underlying map of the cotangent lift of `h` is smooth. -/
private theorem contMDiff_cotangentMap (h : M ≃ₘ⟮I, J⟯ N) :
    ContMDiff (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)) ∞ h.cotangentMap :=
  CotangentBundle.contMDiff_mk_comp_mfderiv (Ψ := fun z : CotangentBundle I M ↦ z)
    (fun z ↦ (h.symm_apply_apply z.proj).symm) contMDiff_id
    (h.contMDiff.comp (contMDiff_proj _)) h.symm.contMDiff (by simp)

/-- The **cotangent lift** of a smooth diffeomorphism `h : M → N`: the smooth diffeomorphism
`T*M → T*N` sending a covector `p` at `x` to the covector `p ∘ (dh_x)⁻¹` at `h x`. Its inverse is
the cotangent lift of `h.symm`. -/
protected def cotangent (h : M ≃ₘ⟮I, J⟯ N) :
    CotangentBundle I M ≃ₘ⟮I.prod 𝓘(𝕜, E →L[𝕜] 𝕜), J.prod 𝓘(𝕜, F →L[𝕜] 𝕜)⟯
      CotangentBundle J N where
  toFun := h.cotangentMap
  invFun := h.symm.cotangentMap
  left_inv := h.cotangentMap_symm_cotangentMap
  -- `h.symm.symm` is `h` up to structure eta, so this is the left inverse law for `h.symm`.
  right_inv := h.symm.cotangentMap_symm_cotangentMap
  contMDiff_toFun := h.contMDiff_cotangentMap
  contMDiff_invFun := h.symm.contMDiff_cotangentMap

/-- The cotangent lift sends a covector `p` at `x` to `p ∘ (dh_x)⁻¹` at `h x`, where
`(dh_x)⁻¹` is the differential of `h.symm` at `h x`. -/
theorem cotangent_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    h.cotangent z =
      TotalSpace.mk' (F →L[𝕜] 𝕜) (h z.proj) (z.2 ∘L mfderiv J I h.symm (h z.proj)) :=
  (rfl)

/-- The cotangent lift of `h` covers `h`. -/
@[simp]
theorem proj_cotangent (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M) :
    (h.cotangent z).proj = h z.proj :=
  (rfl)

/-- The lifted covector evaluates a tangent vector `w` at `h x` as the original covector
evaluates `(dh_x)⁻¹ w`. -/
theorem cotangent_snd_apply (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (w : TangentSpace J (h z.proj)) :
    (h.cotangent z).2 w = z.2 (mfderiv J I h.symm (h z.proj) w) :=
  (rfl)

/-- **The cotangent lift preserves the pairing of covectors with tangent vectors:** the lifted
covector evaluated on `dh_x v` is the original covector evaluated on `v`. -/
@[simp]
theorem cotangent_snd_apply_mfderiv (h : M ≃ₘ⟮I, J⟯ N) (z : CotangentBundle I M)
    (v : TangentSpace I z.proj) :
    (h.cotangent z).2 (mfderiv I J h z.proj v) = z.2 v :=
  (cotangent_snd_apply h z _).trans
    (congrArg z.2 (h.mfderiv_symm_apply_mfderiv_apply (by simp) z.proj v))

/-- The inverse of a cotangent lift is the cotangent lift of the inverse diffeomorphism. -/
@[simp]
theorem cotangent_symm (h : M ≃ₘ⟮I, J⟯ N) :
    h.cotangent.symm = h.symm.cotangent :=
  Diffeomorph.ext fun _ ↦ rfl

/-- The cotangent lift of the identity diffeomorphism is the identity diffeomorphism of the
cotangent bundle. -/
@[simp]
theorem cotangent_refl :
    (Diffeomorph.refl I M ∞).cotangent =
      Diffeomorph.refl (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) (CotangentBundle I M) ∞ := by
  refine Diffeomorph.ext fun z ↦ CotangentBundle.ext rfl fun v ↦ ?_
  -- The inverse of the identity diffeomorphism is the identity map, with identity differential.
  exact (cotangent_snd_apply _ z v).trans (congrArg z.2 (DFunLike.congr_fun mfderiv_id v))

/-- Cotangent lift commutes with composition of smooth diffeomorphisms. -/
@[simp]
theorem cotangent_trans (h : M ≃ₘ⟮I, J⟯ N) (g : N ≃ₘ⟮J, K⟯ P) :
    (h.trans g).cotangent = h.cotangent.trans g.cotangent := by
  refine Diffeomorph.ext fun z ↦ CotangentBundle.ext rfl fun v ↦ ?_
  -- The differential of `(g ∘ h)⁻¹ = h⁻¹ ∘ g⁻¹` at `g (h x)` is the composite of differentials.
  have hcomp := mfderiv_comp_apply (g (h z.proj))
    (h.symm.mdifferentiable (by simp) (g.symm (g (h z.proj))))
    (g.symm.mdifferentiable (by simp) (g (h z.proj))) v
  rw [g.symm_apply_apply] at hcomp
  exact ((cotangent_snd_apply _ z v).trans (congrArg z.2 hcomp)).trans
    ((cotangent_snd_apply h z _).symm.trans (cotangent_snd_apply g _ v).symm)

end Diffeomorph
