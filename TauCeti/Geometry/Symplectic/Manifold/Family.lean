/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Symplectic.Manifold.Flat
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Smooth families of nondegenerate two-forms

A smooth family of two-forms on a manifold `M`, parametrized by a manifold `N`, is represented by
a single smooth two-form `σ` on `N × M`, whose *slice* at `t ∈ N` is the form `σ_t = ι_t^* σ` on
`M`, pulled back along the inclusion `ι_t : x ↦ (t, x)`. This file shows that when every slice is
nondegenerate, the inverse flat maps of the slices depend smoothly on the parameter: for a second
smooth one-form `α` on `N × M`, the vector fields `(σ_t♭)⁻¹ α_t`, the solutions of
`ι_X σ_t = α_t`, form a smooth map `(t, x) ↦ (x, (σ_t♭)⁻¹ α_t (x))` from `N × M` to the tangent
bundle of `M` (`TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`).

For `N = ℝ` this is the form in which time-dependent vector fields enter the time-dependent flow
`TauCeti.timeDependentFlowOf`; with `α_t` a primitive of the velocity of `σ_t`, these are the Moser
vector fields of Moser's stability theorem.

The proof reads the slices as families of forms along the projection `N × M → M`. The slices of a
smooth form are jointly smooth (`TauCeti.SmoothForm.contMDiff_mpullback_prodMk`), hence so are
their flat maps (`TauCeti.SmoothTwoForm.contMDiffAt_sectionAlong_flat`) and, by
`ContMDiffAt.clm_bundle_inverse`, the inverses of these.

## Main results

* `TauCeti.SmoothTwoForm.contMDiff_interiorEquiv_symm_mpullback_prodMk`: the vector fields
  `(σ_t♭)⁻¹ α_t` of a smooth family of nondegenerate two-forms and a smooth family of one-forms
  depend smoothly on the parameter.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Inverse flat maps of a smooth family of nondegenerate two-forms.** Let `σ` be a smooth
two-form on `N × M` whose slices `σ_t = ι_t^* σ` are all nondegenerate, and let `α` be a smooth
one-form on `N × M` with slices `α_t`. Then the vector fields `(σ_t♭)⁻¹ α_t`, the solutions of
`ι_X σ_t = α_t`, depend smoothly on `t`: the map `(t, x) ↦ (x, (σ_t♭)⁻¹ α_t (x))` is smooth. -/
theorem contMDiff_interiorEquiv_symm_mpullback_prodMk {EN HN N : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] [TopologicalSpace HN] {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N]
    [ChartedSpace HN N] [IsManifold J ∞ N] [FiniteDimensional ℝ E]
    (σ : SmoothForm (J.prod I) (N × M) ℝ 2)
    (hσ : ∀ t, IsNondegenerate
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (α : SmoothForm (J.prod I) (N × M) ℝ 1) :
    ContMDiff (J.prod I) I.tangent ∞ (fun p : N × M ↦ (⟨p.2, (hσ p.1).interiorEquiv.symm
      (SmoothForm.mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α) p.2⟩ :
        TangentBundle I M)) := by
  intro p
  simp only [IsNondegenerate.interiorEquiv_symm_apply]
  have hflat := contMDiffAt_sectionAlong_flat (b := Prod.snd) (σ := fun q : N × M ↦
    SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ)
    (SmoothForm.contMDiff_mpullback_prodMk σ p)
  have hα := (SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
    (α := fun q : N × M ↦
      SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α)).2
    (SmoothForm.contMDiff_mpullback_prodMk α p)
  have hinv := ContMDiffAt.clm_bundle_inverse (x := p) (b := Prod.snd)
    (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ϕ := fun q : N × M ↦
    flat (SmoothForm.mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) σ) q.2) hflat
    ((hσ p.1).isInvertible_flat p.2)
  exact hinv.clm_bundle_apply hα

end SmoothTwoForm

end TauCeti
