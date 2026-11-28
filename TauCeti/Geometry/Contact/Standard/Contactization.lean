/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Geometry.Manifold.Diffeomorph.Prod
public import TauCeti.Geometry.Symplectic.Liouville.Standard
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Contactization presentation of the standard contact form

Reassociating `(V × V) × ℝ ≃ V × V × ℝ` identifies the standard contact form
`TauCeti.innerProductContactForm V` (`dz - ⟪p, dq⟫`) on `V × V × ℝ` with the contactization of the
canonical Liouville one-form `TauCeti.innerProductLiouvilleForm V` on `V × V`
(`TauCeti.mpullback_prodAssocSymmSelf_symm_innerProductContactForm`).
-/

public section

noncomputable section

open scoped Manifold InnerProductSpace ContDiff

namespace TauCeti

/-- Reassociating `((q, p), t) ↦ (q, p, t)` pulls `innerProductContactForm V` back to the
contactization form `dz - ⟪p, dq⟫` of `innerProductLiouvilleForm V`. -/
theorem mpullback_prodAssocSymmSelf_symm_innerProductContactForm (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    SmoothForm.mpullback (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm
        (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm.contMDiff (innerProductContactForm V) =
      (innerProductLiouvilleForm V).contactization := by
  apply Subtype.ext; funext p; refine ContinuousAlternatingMap.ext_fin_one fun u ↦ ?_
  let g₁ : (V × V) →L[ℝ] V × V × ℝ :=
    (ContinuousLinearMap.fst ℝ V V).prod ((ContinuousLinearMap.snd ℝ V V).prod 0)
  let g₂ : ℝ →L[ℝ] V × V × ℝ :=
    (0 : ℝ →L[ℝ] V).prod ((0 : ℝ →L[ℝ] V).prod (ContinuousLinearMap.id ℝ ℝ))
  have h_eq : ⇑(Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm =
      ⇑g₁ ∘ Prod.fst + ⇑g₂ ∘ Prod.snd := by
    funext ⟨⟨q, r⟩, t⟩
    simp [Diffeomorph.prodAssocSymmSelf_symm_apply, g₁, g₂]
  have h1 (v : TangentSpace 𝓘(ℝ, V × V) p.fst) :
      mvfderiv 𝓘(ℝ, V × V) g₁ p.fst v = g₁ v := by
    rw [mvfderiv_eq_fderiv_apply, g₁.hasFDerivAt.fderiv]
  have h2 (v : TangentSpace 𝓘(ℝ) p.snd) : mvfderiv 𝓘(ℝ) g₂ p.snd v = g₂ v := by
    rw [mvfderiv_eq_fderiv_apply, g₂.hasFDerivAt.fderiv]
  have hassoc_d :
      mvfderiv (𝓘(ℝ, V × V).prod 𝓘(ℝ)) (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm p u =
        g₁ u.fst + g₂ u.snd := by
    have h := mvfderiv_comp_fst_add_comp_snd_apply
      (g₁.differentiable.mdifferentiable p.fst) (g₂.differentiable.mdifferentiable p.snd) u
    rw [← h_eq] at h
    exact h.trans (congrArg₂ (· + ·) (h1 u.fst) (h2 u.snd))
  rw [SmoothForm.mpullback_apply_one, innerProductContactForm_apply,
    ← mvfderiv_apply_eq_mfderiv_apply, hassoc_d]
  simp [g₁, g₂, NormedSpace.fromTangentSpace_apply]

end TauCeti
