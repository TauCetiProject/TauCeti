/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Incidence.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Invariance of incidence regularity under coordinate changes

Regularity of an incidence parameter (`TauCeti.IsRegularIncidenceParameterOn`) transfers along
nonlinear coordinate changes of the source, target-map domain, parameter space, and target whose
derivatives are surjective, and is invariant under continuous linear equivalences, with no
differentiability hypotheses on the family or the map.

## Main declarations

* `TauCeti.IsRegularIncidenceParameterOn.comp`: nonlinear chart transfer.
* `TauCeti.isRegularIncidenceParameterOn_comp_equiv_iff` and
  `TauCeti.isRegularIncidenceParameter_comp_equiv_iff`: unconditional continuous linear
  equivalence invariance.
-/

public section

open Function Set

namespace TauCeti

variable {E W V P E' W' V' P' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup W'] [NormedSpace ℝ W']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup P'] [NormedSpace ℝ P']

/-- **Nonlinear coordinate-change transfer for `IsRegularIncidenceParameterOn`.** Suppose
`φ : E' → E`, `ψ : W' → W`, `τ : P' → P`, and `χ : V → V'` satisfy, at each incidence point
`((x', y'), p') ∈ U'` with `χ (F (φ x', τ p')) = χ (j (ψ y'))`:
* `((φ x', ψ y'), τ p') ∈ U` and `F (φ x', τ p') = j (ψ y')` (`χ` reflects incidence equalities),
* `φ`, `ψ`, and `χ` have surjective derivatives at `x'`, `y'`, and `j (ψ y')` (which automatically
  makes them differentiable there), and `τ` is differentiable at `p'`.

Then regularity of `τ p'` on `U` transfers to regularity of `p'` on `U'` for the composed system
`z ↦ χ (F (φ z.1, τ z.2))` against `χ ∘ j ∘ ψ`, with no extra differentiability hypotheses on `F`
or `j`. This is the local chart-transfer step for manifold incidence transversality. -/
theorem IsRegularIncidenceParameterOn.comp {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {U' : Set ((E' × W') × P')}
    {φ : E' → E} {ψ : W' → W} {τ : P' → P} {χ : V → V'} {p' : P'}
    (h : IsRegularIncidenceParameterOn F j U (τ p'))
    (hmaps : ∀ x' y', ((x', y'), p') ∈ U' → χ (F (φ x', τ p')) = χ (j (ψ y')) →
      ((φ x', ψ y'), τ p') ∈ U ∧ F (φ x', τ p') = j (ψ y'))
    (hφ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ φ x'))
    (hψ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ ψ y'))
    (hτ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      DifferentiableAt ℝ τ p')
    (hχ : ∀ x' y', ((x', y'), p') ∈ U' → F (φ x', τ p') = j (ψ y') →
      Surjective (fderiv ℝ χ (j (ψ y')))) :
    IsRegularIncidenceParameterOn
      (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (fun y' ↦ χ (j (ψ y'))) U' p' := by
  rw [isRegularIncidenceParameterOn_iff, isRegularParameterOn_iff]
  rintro ⟨x', y'⟩ hU' hEq'
  -- Phase 1: reflect the incidence point into `U` and collect differentiability of all maps once.
  obtain ⟨hU, hEq⟩ := hmaps x' y' hU' (incidenceEquation_eq_zero.1 hEq')
  obtain ⟨hFxy, hjxy⟩ := h.differentiableAt hU hEq
  have hφs := hφ x' y' hU' hEq
  have hψs := hψ x' y' hU' hEq
  have hχs := hχ x' y' hU' hEq
  have hφd := differentiableAt_of_fderiv_surjective hφs
  have hψd := differentiableAt_of_fderiv_surjective hψs
  have hχd := differentiableAt_of_fderiv_surjective hχs
  -- Phase 2: differentiate the composed family, its `x'`-slice, and the composed target map.
  have hpair : DifferentiableAt ℝ (fun z : E' × P' ↦ (φ z.1, τ z.2)) (x', p') :=
    (hφd.comp (x', p') differentiableAt_fst).prodMk
      ((hτ x' y' hU' hEq).comp (x', p') differentiableAt_snd)
  have hF' : DifferentiableAt ℝ (fun z : E' × P' ↦ χ (F (φ z.1, τ z.2))) (x', p') :=
    (hEq.symm ▸ hχd).comp (x', p') (hFxy.comp (x', p') hpair)
  have hFx : HasFDerivAt (fun x'' ↦ χ (F (φ x'', τ p')))
      ((fderiv ℝ χ (j (ψ y'))).comp
        (((fderiv ℝ F (φ x', τ p')).comp (.inl ℝ E P)).comp (fderiv ℝ φ x'))) x' := by
    have hχ' : HasFDerivAt χ (fderiv ℝ χ (j (ψ y'))) (F (φ x', τ p')) := by
      rw [hEq]; exact hχd.hasFDerivAt
    exact hχ'.comp x' (hFxy.hasFDerivAt_slice_fst.comp x' hφd.hasFDerivAt)
  have hjy : HasFDerivAt (fun w ↦ χ (j (ψ w)))
      ((fderiv ℝ χ (j (ψ y'))).comp ((fderiv ℝ j (ψ y')).comp (fderiv ℝ ψ y'))) y' :=
    hχd.hasFDerivAt.comp y' (hjxy.hasFDerivAt.comp y' hψd.hasFDerivAt)
  -- Phase 3: reduce to the coproduct of slice derivatives and lift any tangent vector `w' : V'`.
  rw [fderiv_incidenceEquation_comp_inl hF' hjy.differentiableAt, ← fderiv_slice_left hF',
    hFx.fderiv, hjy.fderiv]
  intro w'
  obtain ⟨w, rfl⟩ := hχs w'
  obtain ⟨⟨u, v⟩, huv⟩ := h.surjective hU hEq w
  obtain ⟨u', rfl⟩ := hφs u
  obtain ⟨v', rfl⟩ := hψs v
  refine ⟨(u', v'), ?_⟩
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ← map_neg, ← map_add] at huv ⊢
  exact congrArg (fderiv ℝ χ (j (ψ y'))) huv

/-- **Subset-localized invariance under continuous linear equivalences** on `E`, `W`, `P`, and `V`
(requiring no differentiability hypotheses on `F` or `j`). -/
theorem isRegularIncidenceParameterOn_comp_equiv_iff (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V}
    {U : Set ((E × W) × P)} {p' : P'} :
    IsRegularIncidenceParameterOn
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y')))
        (((eE.prodCongr eW).prodCongr eP) ⁻¹' U) p' ↔
      IsRegularIncidenceParameterOn F j U (eP p') := by
  constructor
  · intro h
    have h₀ : IsRegularIncidenceParameterOn
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y')))
        (((eE.prodCongr eW).prodCongr eP) ⁻¹' U) (eP.symm (eP p')) := by
      rwa [eP.symm_apply_apply]
    have hcomp := IsRegularIncidenceParameterOn.comp h₀ (U' := U)
      (φ := eE.symm) (ψ := eW.symm) (τ := eP.symm) (χ := eV.symm)
      (fun _ _ hU hEq ↦ ⟨by
        simpa only [mem_preimage, ContinuousLinearEquiv.prodCongr_apply, Prod.map_apply,
          ContinuousLinearEquiv.apply_symm_apply] using hU, eV.symm.injective hEq⟩)
      (fun _ _ _ _ ↦ by rw [eE.symm.fderiv]; exact eE.symm.surjective)
      (fun _ _ _ _ ↦ by rw [eW.symm.fderiv]; exact eW.symm.surjective)
      (fun _ _ _ _ ↦ eP.symm.differentiableAt)
      (fun _ _ _ _ ↦ by rw [eV.symm.fderiv]; exact eV.symm.surjective)
    simpa only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      using hcomp
  · intro h
    exact IsRegularIncidenceParameterOn.comp h
      (φ := eE) (ψ := eW) (τ := eP) (χ := eV)
      (fun _ _ hU hEq ↦ ⟨by
        simpa only [mem_preimage, ContinuousLinearEquiv.prodCongr_apply, Prod.map_apply] using hU,
        eV.injective hEq⟩)
      (fun _ _ _ _ ↦ by rw [eE.fderiv]; exact eE.surjective)
      (fun _ _ _ _ ↦ by rw [eW.fderiv]; exact eW.surjective)
      (fun _ _ _ _ ↦ eP.differentiableAt)
      (fun _ _ _ _ ↦ by rw [eV.fderiv]; exact eV.surjective)

/-- **Invariance under continuous linear equivalences** on `E`, `W`, `P`, and `V` (requiring no
differentiability hypotheses on `F` or `j`). -/
theorem isRegularIncidenceParameter_comp_equiv_iff (eE : E' ≃L[ℝ] E) (eW : W' ≃L[ℝ] W)
    (eP : P' ≃L[ℝ] P) (eV : V ≃L[ℝ] V') {F : E × P → V} {j : W → V} {p' : P'} :
    IsRegularIncidenceParameter
        (fun z : E' × P' ↦ eV (F (eE z.1, eP z.2))) (fun y' ↦ eV (j (eW y'))) p' ↔
      IsRegularIncidenceParameter F j (eP p') := by
  simpa only [preimage_univ, isRegularIncidenceParameterOn_univ] using
    isRegularIncidenceParameterOn_comp_equiv_iff (F := F) (j := j) (U := univ) (p' := p')
      eE eW eP eV

end TauCeti
