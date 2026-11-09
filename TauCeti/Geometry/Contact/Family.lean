/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Moser
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Smooth families of contact forms

A smooth family of one-forms on a manifold `M`, parametrized by a manifold `N`, is represented by
a single smooth one-form `α` on `N × M`, whose *slice* at `t ∈ N` is the form `α_t = ι_t^* α` on
`M`, pulled back along the inclusion `ι_t : y ↦ (t, y)`. This file shows that when every slice is a
contact form, the vector fields which the contact forms determine pointwise depend smoothly on the
parameter as well as on the point:

* the Reeb vector fields `R_(α_t)`
  (`TauCeti.SmoothForm.contMDiff_reebVectorField_mpullback_prodMk`);
* for a second smooth one-form `β` on `N × M`, the horizontal contact-Moser vector fields `Y_t` of
  `(α_t, β_t)`, the solutions of `α_t(Y_t) = 0` and `(ι_(Y_t) dα_t + β_t)|ker α_t = 0`
  (`TauCeti.SmoothForm.contMDiff_contactMoserVectorField_mpullback_prodMk`).

Both are smooth maps `(t, y) ↦ (y, X_t(y))` from `N × M` to the tangent bundle of `M`. For `N = ℝ`
this is the form in which time-dependent vector fields enter the time-dependent flow
`TauCeti.timeDependentFlowOf`. In Gray's stability theorem, `β_t` is the time derivative
`∂_t α_t`, the slice of the Lie derivative of `α` along the time coordinate field, and the flow of
`Y_t` pulls each `α_t` back to a positive multiple of `α_0`.

The proofs read the slices as families of forms along the projection `N × M → M`. The slices of a
smooth form are jointly smooth (`TauCeti.contMDiff_mpullback_prodMk_form`), and so are the slices
of its exterior derivative, which are the exterior derivatives of the slices. The pointwise
constructions then depend smoothly on the parameter
(`TauCeti.SmoothForm.contMDiffAt_sectionAlong_reebVectorField`,
`TauCeti.SmoothForm.contMDiffAt_sectionAlong_contactMoserVectorField`).

## Main results

* `TauCeti.SmoothForm.contMDiff_reebVectorField_mpullback_prodMk`: the Reeb vector fields of the
  slices depend smoothly on the parameter.
* `TauCeti.SmoothForm.contMDiff_contactMoserVectorField_mpullback_prodMk`: the contact-Moser vector
  fields of the slices depend smoothly on the parameter.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M EN HN N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] in
/-- The slices `ι_t^* α` of a smooth one-form on `N × M` are jointly smooth along the projection
`(t, y) ↦ y`, and so are their exterior derivatives. -/
private theorem contMDiff_mpullback_prodMk_and_mextDeriv
    (α : SmoothForm (J.prod I) (N × M) ℝ 1) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
        (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin 1]→L[ℝ] Trivial M ℝ x) p.2
          ((mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).1 p.2)) ∧
      ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x [⋀^Fin 2]→L[ℝ] Trivial M ℝ x) p.2
          (mextDeriv (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).1 p.2)) := by
  refine ⟨by simpa only [coe_mpullback] using contMDiff_mpullback_prodMk_form α.contMDiff, ?_⟩
  have h := contMDiff_mpullback_prodMk_form (mextDerivₗ (J.prod I) 1 α).contMDiff
  simp only [mextDerivₗ_apply] at h
  convert h using 3 with p
  rw [← mextDerivₗ_apply, mextDerivₗ_mpullback, coe_mpullback, mextDerivₗ_apply]

/-- **Reeb vector fields of a smooth family of contact forms.** If every slice `α_t = ι_t^* α` of
a smooth one-form `α` on `N × M` is a contact form, then the Reeb vector fields `R_(α_t)` depend
smoothly on `t`: the map `(t, y) ↦ (y, R_(α_t)(y))` is smooth. -/
theorem contMDiff_reebVectorField_mpullback_prodMk (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ContMDiff (J.prod I) I.tangent ∞ (fun p : N × M ↦
      (⟨p.2, (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
        p.2⟩ : TangentBundle I M)) := fun p ↦
  contMDiffAt_sectionAlong_reebVectorField (b := Prod.snd)
    (α := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (fun q ↦ hc q.1) ((contMDiff_mpullback_prodMk_and_mextDeriv α).1 p)
    ((contMDiff_mpullback_prodMk_and_mextDeriv α).2 p)

/-- **Contact-Moser vector fields of a smooth family of contact forms.** If every slice
`α_t = ι_t^* α` of a smooth one-form `α` on `N × M` is a contact form, and `β` is a second smooth
one-form on `N × M` with slices `β_t`, then the horizontal contact-Moser vector fields `Y_t` of
`(α_t, β_t)` depend smoothly on `t`: the map `(t, y) ↦ (y, Y_t(y))` is smooth. -/
theorem contMDiff_contactMoserVectorField_mpullback_prodMk
    (α β : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ContMDiff (J.prod I) I.tangent ∞ (fun p : N × M ↦
      (⟨p.2, (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
        α).contactMoserVectorField
          (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) β) p.2⟩ :
        TangentBundle I M)) := fun p ↦
  contMDiffAt_sectionAlong_contactMoserVectorField (b := Prod.snd)
    (α := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (β := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) β)
    (fun q ↦ hc q.1) ((contMDiff_mpullback_prodMk_and_mextDeriv α).1 p)
    ((contMDiff_mpullback_prodMk_and_mextDeriv α).2 p)
    ((contMDiff_mpullback_prodMk_and_mextDeriv β).1 p)

end TauCeti.SmoothForm
