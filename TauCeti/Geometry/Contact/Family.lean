/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Moser
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Smooth families of contact forms

A smooth family of one-forms on a manifold `M`, parametrized by a manifold `N`, is represented by
a single smooth one-form `α` on `N × M`, whose *slice* at `t ∈ N` is the form `α_t = ι_t^* α` on
`M`, pulled back along the inclusion `ι_t : y ↦ (t, y)`. This file shows that when the slices are
contact forms for all parameters in an open set `U ⊆ N`, the vector fields which the contact forms
determine pointwise depend smoothly on the parameter in `U` as well as on the point:

* the Reeb vector fields `R_(α_t)`
  (`TauCeti.SmoothForm.contMDiffOn_reebVectorField_mpullback_prodMk`);
* for a second smooth one-form `β` on `N × M`, the horizontal contact-Moser vector fields `Y_t` of
  `(α_t, β_t)`, the solutions of `α_t(Y_t) = 0` and `(ι_(Y_t) dα_t + β_t)|ker α_t = 0`
  (`TauCeti.SmoothForm.contMDiffOn_contactMoserVectorField_mpullback_prodMk`).

Both are maps `(t, y) ↦ (y, X_t(y))` from `N × M` to the tangent bundle of `M`, smooth on `U × M`.
For `N = ℝ` this is the form in which time-dependent vector fields enter the time-dependent flow
`TauCeti.timeDependentFlowOf`. In Gray's stability theorem, `β_t` is the time derivative
`∂_t α_t`, the slice of the Lie derivative of `α` along the time coordinate field, and the flow of
`Y_t` pulls each `α_t` back to a positive multiple of `α_0`.

The proofs read the slices as families of forms along the projection `N × M → M`. The slices of a
smooth form are jointly smooth (`TauCeti.SmoothForm.contMDiff_mpullback_prodMk`), and so are their
exterior derivatives (`TauCeti.SmoothForm.contMDiff_mextDeriv_mpullback_prodMk`). The pointwise
constructions then depend smoothly on the parameter
(`TauCeti.SmoothForm.contMDiffAt_sectionAlong_reebVectorField`,
`TauCeti.SmoothForm.contMDiffAt_sectionAlong_contactMoserVectorField`).

## Main results

* `TauCeti.SmoothForm.contMDiffOn_reebVectorField_mpullback_prodMk`: the Reeb vector fields of the
  slices depend smoothly on the parameter in an open set where the slices are contact.
* `TauCeti.SmoothForm.contMDiffOn_contactMoserVectorField_mpullback_prodMk`: the contact-Moser
  vector fields of the slices depend smoothly on the parameter in an open set where the slices are
  contact.
* `TauCeti.SmoothForm.contMDiff_reebVectorField_mpullback_prodMk` and
  `TauCeti.SmoothForm.contMDiff_contactMoserVectorField_mpullback_prodMk`: the global versions, when
  every slice is contact.

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

/-- **Reeb vector fields of a smooth family of contact forms.** If the slices `α_t = ι_t^* α` of a
smooth one-form `α` on `N × M` are contact forms for all `t` in an open set `U ⊆ N`, then the Reeb
vector fields `R_(α_t)` depend smoothly on `t ∈ U`: the map `(t, y) ↦ (y, R_(α_t)(y))` is smooth on
`U × M`. -/
theorem contMDiffOn_reebVectorField_mpullback_prodMk (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    {U : Set N} (hU : IsOpen U)
    (hc : ∀ t ∈ U, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ContMDiffOn (J.prod I) I.tangent ∞ (fun p : N × M ↦
      (⟨p.2, (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
        p.2⟩ : TangentBundle I M)) (U ×ˢ Set.univ) := fun p hp ↦
  (contMDiffAt_sectionAlong_reebVectorField (b := Prod.snd)
    (α := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (Filter.mem_of_superset ((hU.preimage continuous_fst).mem_nhds hp.1) fun q hq ↦ hc q.1 hq)
    (contMDiff_mpullback_prodMk α p)
    (contMDiff_mextDeriv_mpullback_prodMk α p)).contMDiffWithinAt

/-- **Reeb vector fields of a smooth family of contact forms.** If every slice `α_t = ι_t^* α` of
a smooth one-form `α` on `N × M` is a contact form, then the Reeb vector fields `R_(α_t)` depend
smoothly on `t`: the map `(t, y) ↦ (y, R_(α_t)(y))` is smooth. -/
theorem contMDiff_reebVectorField_mpullback_prodMk (α : SmoothForm (J.prod I) (N × M) ℝ 1)
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ContMDiff (J.prod I) I.tangent ∞ (fun p : N × M ↦
      (⟨p.2, (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
        p.2⟩ : TangentBundle I M)) := by
  rw [← contMDiffOn_univ, ← Set.univ_prod_univ]
  exact contMDiffOn_reebVectorField_mpullback_prodMk α isOpen_univ fun t _ ↦ hc t

/-- **Contact-Moser vector fields of a smooth family of contact forms.** If the slices
`α_t = ι_t^* α` of a smooth one-form `α` on `N × M` are contact forms for all `t` in an open set
`U ⊆ N`, and `β` is a second smooth one-form on `N × M` with slices `β_t`, then the horizontal
contact-Moser vector fields `Y_t` of `(α_t, β_t)` depend smoothly on `t ∈ U`: the map
`(t, y) ↦ (y, Y_t(y))` is smooth on `U × M`. -/
theorem contMDiffOn_contactMoserVectorField_mpullback_prodMk
    (α β : SmoothForm (J.prod I) (N × M) ℝ 1) {U : Set N} (hU : IsOpen U)
    (hc : ∀ t ∈ U, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    ContMDiffOn (J.prod I) I.tangent ∞ (fun p : N × M ↦
      (⟨p.2, (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id)
        α).contactMoserVectorField
          (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) β) p.2⟩ :
        TangentBundle I M)) (U ×ˢ Set.univ) := fun p hp ↦
  (contMDiffAt_sectionAlong_contactMoserVectorField (b := Prod.snd)
    (α := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)
    (β := fun q : N × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) β)
    (Filter.mem_of_superset ((hU.preimage continuous_fst).mem_nhds hp.1) fun q hq ↦ hc q.1 hq)
    (contMDiff_mpullback_prodMk α p)
    (contMDiff_mextDeriv_mpullback_prodMk α p) (contMDiff_mpullback_prodMk β p)).contMDiffWithinAt

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
        TangentBundle I M)) := by
  rw [← contMDiffOn_univ, ← Set.univ_prod_univ]
  exact contMDiffOn_contactMoserVectorField_mpullback_prodMk α β isOpen_univ fun t _ ↦ hc t

end TauCeti.SmoothForm
