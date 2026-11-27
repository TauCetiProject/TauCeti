/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Contact.Standard
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.Diffeomorph.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Symplectic.Manifold.Darboux

/-!
# The strict contact Darboux theorem

Let `M` be a smooth manifold with finite-dimensional real model space `E`, and let `α` be a
one-form, smooth on an open set `U`, which is a contact form at an interior point `x₀ ∈ U`
(`TauCeti.IsContactFormAt`). Whereas the contact Darboux theorem of
`TauCeti/Geometry/Contact/Darboux/Basic.lean` pulls the standard contact form
`α_std = dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to a positive multiple `g α`,
**the strict contact Darboux theorem**
(`TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`) eliminates the conformal
factor `g`: there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `chart` from
`M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0` such that for every
`x ∈ chart.source` and `v : T_x M`,

`α_std (chart x) (d chart_x v) = α x v`.

The proof follows the geometric Reeb-slice construction rather than the contact Moser deformation
of `TauCeti/Geometry/Contact/Darboux/Basic.lean`:

1. Read `α` in the preferred extended chart at `x₀`, where openness of the pointwise contact
   condition (`TauCeti.IsContactFormAt.eventually_modelSpace`) gives an open neighbourhood `W₀` on
   which the coordinate one-form `α₀` is a smooth contact form.
2. Choose the affine slice through `y₀` along the contact hyperplane `K = ker α₀(y₀)`, which has
   codimension one and is transverse to the Reeb vector field `R_{α₀}(y₀)`. The local Reeb flow map
   out of this slice is a local diffeomorphism at `(0, 0)`
   (`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`) and pulls
   `α₀` back to the contactization form `dt + β` (`(-β).contactization`), where `β` is the
   restriction of `α₀` to the slice (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`).
3. Because `dβ` is closed and nondegenerate at the origin of the slice, the symplectic Darboux
   theorem (`TauCeti.SmoothTwoForm.exists_standardDarbouxChart_of_nondegenerate_of_isInteriorPoint`)
   provides slice coordinates `ψ` into `ℝⁿ × ℝⁿ` pulling the standard symplectic form
   `Σᵢ dqᵢ ∧ dpᵢ` back to `dβ`.
4. On the open submanifold `ψ.target` of `ℝⁿ × ℝⁿ`, the pushed-forward one-form `β_t = (ψ⁻¹)^* β`
   and the standard momentum form `⟪p, dq⟫` (`TauCeti.innerProductMomentumForm`) have opposite
   exterior derivatives, so `β_t + ⟪p, dq⟫` is closed. The Poincaré lemma
   (`TauCeti.exists_contMDiff_isPrimitiveOn`) supplies a smooth primitive on an open neighbourhood
   `B ⊆ ψ.target` of `0` vanishing at `0`. Absorbing this primitive into the Reeb-time coordinate
   via `TauCeti.contactizationShift` (`TauCeti.mpullback_contactizationShift_contactization`) and
   reassociating `(ℝⁿ × ℝⁿ) × ℝ ≃ ℝⁿ × ℝⁿ × ℝ`
   (`TauCeti.mpullback_prodAssocSymmSelf_symm_innerProductContactForm`) pulls `dz - Σᵢ pᵢ dqᵢ` back
   to `dt + β`, completing the chart.

## Main results

* `TauCeti.IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq`,
  `TauCeti.IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq_of_finrank_eq`:
  strict Darboux partial diffeomorphisms on finite-dimensional real normed spaces.
* `TauCeti.IsContactFormAt.exists_inChartAt_pullback`: coordinate reduction and chart lifting for
  local contact forms at an interior point.
* `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`: strict
  Darboux charts for a locally defined one-form which is contact at an interior point.
* `TauCeti.IsContactFormAt.exists_strictDarbouxChart`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq`: the same on boundaryless
  manifolds.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`: global counterparts
  for smooth contact forms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 3.5.14.
-/

public section

noncomputable section

open Set Filter Bundle Module TopologicalSpace
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti

/-! ### Strict Contact Darboux on finite-dimensional normed spaces -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Shrink an open set `W` around `y₀` to an open subset `W₀ : Opens E` on which a smooth flat
one-form `η` restricts to a smooth contact form `α₀`. -/
private theorem exists_opens_isContactForm {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) (hW : IsOpen W) (hy₀W : y₀ ∈ W)
    (hη : ContDiffOn ℝ ∞ η W) :
    ∃ (W₀ : Opens E) (p₀ : W₀) (α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1),
      (p₀ : E) = y₀ ∧ (W₀ : Set E) ⊆ W ∧ α₀.IsContactForm ∧
      ∀ (p : W₀) (v : TangentSpace 𝓘(ℝ, E) p),
        α₀.val p ![v] =
          η p.val ![NormedSpace.fromTangentSpace p.val
            (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) p v)] := by
  let ηR : RoughForm 𝓘(ℝ, E) E ℝ 1 := η
  obtain ⟨W₁', hW₁'_sub, hW₁'_open, hy₀W₁'⟩ :=
    eventually_nhds_iff.1
      (hc.eventually_modelSpace ((hη.contDiffAt (hW.mem_nhds hy₀W)).of_le (by simp)))
  let W₀ : Opens E := ⟨W₁' ∩ W, hW₁'_open.inter hW⟩
  let p₀ : W₀ := ⟨y₀, hy₀W₁', hy₀W⟩
  have hη_md (x : W₀) : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (ηR y)) (x : E) :=
    contMDiffAt_form_modelSpace_iff (φ := ηR).2 (hη.contDiffAt (hW.mem_nhds x.property.right))
  have hsmooth :
      IsSmoothForm 𝓘(ℝ, E) ∞ (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : W₀ → E) ηR) :=
    (isSmoothForm_def (I := 𝓘(ℝ, E)) ∞ _).2 fun x ↦
      (hη_md x).mpullback_form (contMDiff_subtypeVal (I := 𝓘(ℝ, E)) (n := ∞) (x := x)) (by simp)
  let α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1 := ⟨_, hsmooth.mem_smoothBundleForms⟩
  have hα₀ : α₀.IsContactForm :=
    SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun x ↦
      (isContactFormAt_mpullback_iff
        ((contMDiff_subtypeVal (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffAt.of_le (by simp))
        ((hη_md x).of_le (by simp)) (bijective_mfderiv_subtype_val x)).2
        (hW₁'_sub x.val x.property.left)
  refine ⟨W₀, p₀, α₀, rfl, inter_subset_right, hα₀, fun p v ↦ ?_⟩
  dsimp only [α₀]
  rw [mpullback_apply_one, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    NormedSpace.fromTangentSpace_apply]
  -- `ηR` is `let`-bound to `η`, so both sides coincide.
  rfl

/-- Given a smooth contact form `α₀` on an open subset `W₀ : Opens E` and a point `p₀ : W₀`, there
exist a codimension-one subspace `K` of `E`, an open subset `S_K : Opens K`, a point `s₀ : S_K`,
and a smooth map `ι_K : S_K → W₀` sending `s₀` to `p₀` whose differential at `s₀` is injective and
does not contain `α₀.reebVectorField (ι_K s₀)` in its range. -/
private theorem exists_contactHyperplaneSlice_opens {W₀ : Opens E} (p₀ : W₀)
    {α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1} (hα₀ : α₀.IsContactForm) :
    ∃ (K : Submodule ℝ E) (S_K : Opens K) (s₀ : S_K) (ι_K : S_K → W₀),
      finrank ℝ K + 1 = finrank ℝ E ∧
      ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, E) ∞ ι_K ∧
      ι_K s₀ = p₀ ∧
      Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀) ∧
      α₀.reebVectorField (ι_K s₀) ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀).range := by
  let e_at (x : W₀) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x).trans (NormedSpace.fromTangentSpace x.val)
  let L_at (x : W₀) : E →ₗ[ℝ] ℝ :=
    ((SmoothForm.degreeOneEquiv α₀ x).comp (e_at x).symm.toContinuousLinearMap).toLinearMap
  have hL_apply (x : W₀) (u : TangentSpace 𝓘(ℝ, E) x) : L_at x (e_at x u) = α₀.val x ![u] := by
    simp [L_at]
  -- Define the codimension-one subspace `K = ker α₀(p₀)` and the affine slice `ι_K : S_K → W₀`.
  let K : Submodule ℝ E := LinearMap.ker (L_at p₀)
  have hL_ne : L_at p₀ ≠ 0 := fun h0 ↦
    (SmoothForm.isContactForm_iff_forall_isContactFormAt.1 hα₀ p₀).ne_zero <|
      ContinuousAlternatingMap.ext_fin_one fun u ↦ by simp [← hL_apply p₀ u, h0]
  have hdimK : finrank ℝ K + 1 = finrank ℝ E := Module.Dual.finrank_ker_add_one_of_ne_zero hL_ne
  let S_K : Opens K := ⟨{w : K | (p₀ : E) + K.subtypeL w ∈ W₀},
    (continuous_const.add K.subtypeL.continuous).isOpen_preimage _ W₀.isOpen⟩
  let s₀ : S_K := ⟨0, by simp [S_K, p₀.property]⟩
  let ι_K : S_K → W₀ := fun w ↦ ⟨(p₀ : E) + K.subtypeL w.val, w.property⟩
  have hι_K : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, E) ∞ ι_K := (ContMDiff.subtypeVal_comp_iff W₀ _).1 <|
    contMDiff_const.add (K.subtypeL.contDiff.contMDiff.comp contMDiff_subtypeVal)
  have hι_s₀ : ι_K s₀ = p₀ := Subtype.ext (by simp [ι_K, s₀])
  -- Compute `d ι_K` at `s₀` to verify injectivity and transversality to the Reeb vector field.
  let e_s₀ : TangentSpace 𝓘(ℝ, K) s₀ ≃L[ℝ] K :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, K)) s₀).trans (NormedSpace.fromTangentSpace s₀.val)
  have hdι (v : TangentSpace 𝓘(ℝ, K) s₀) :
      e_at (ι_K s₀) (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v) = K.subtypeL (e_s₀ v) := by
    let A : K → E := fun w ↦ (p₀ : E) + K.subtypeL w
    have hA : HasFDerivAt A K.subtypeL s₀.val := K.subtypeL.hasFDerivAt.const_add (p₀ : E)
    let v0 : TangentSpace 𝓘(ℝ, K) s₀.val := (NormedSpace.fromTangentSpace s₀.val).symm (e_s₀ v)
    have hv0 : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v = mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) A s₀.val v0 := by
      have h1 : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v = mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) A s₀.val v :=
        Manifold.mfderiv_apply_of_subtype_val_comp_eq (I := 𝓘(ℝ, K)) (I' := 𝓘(ℝ, E))
          (f := ι_K) (A := A) rfl v
      have h2 : v0 = v := by
        simp only [v0, e_s₀, ContinuousLinearEquiv.trans_apply,
          Manifold.tangentSpaceOpenEquiv_apply]
        exact (NormedSpace.fromTangentSpace (s₀.val : K)).symm_apply_apply _
      exact h1.trans (congrArg (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) A s₀.val) h2.symm)
    dsimp only [e_at, ContinuousLinearEquiv.trans_apply]
    rw [Manifold.tangentSpaceOpenEquiv_apply, hv0, NormedSpace.fromTangentSpace_apply,
      ← mvfderiv_apply_eq_mfderiv_apply, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, hA.fderiv]
  have hι_inj : Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀) := fun v w hvw ↦ by
    have h1 := congrArg (e_at (ι_K s₀)) hvw
    rw [hdι, hdι] at h1
    exact e_s₀.injective (Subtype.ext h1)
  have hR : α₀.reebVectorField (ι_K s₀) ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀).range := by
    rintro ⟨v, hv⟩
    have h1 : α₀.val (ι_K s₀) ![α₀.reebVectorField (ι_K s₀)] = 1 := hα₀.apply_reebVectorField _
    have h0 : α₀.val (ι_K s₀) ![mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v] = 0 := by
      rw [← hL_apply (ι_K s₀), hdι v, hι_s₀]
      exact LinearMap.mem_ker.1 (e_s₀ v).property
    exact zero_ne_one (h0.symm.trans (hv ▸ h1))
  exact ⟨K, S_K, s₀, ι_K, hdimK, hι_K, hι_s₀, hι_inj, hR⟩

/-- Given a smooth contact form `α₀` on an open subset `W₀ : Opens E` and a point `p₀ : W₀`, there
exist a codimension-one subspace `K` of `E`, an open subset `S_K : Opens K`, a point `s₀ : S_K`,
a smooth one-form `β` on `S_K` whose exterior derivative is nondegenerate at `s₀`, and a smooth
partial diffeomorphism `Ψ : W₀ → S_K × ℝ` sending `p₀` to `(s₀, 0)` that pulls
`(-β).contactization` back to `α₀` on `Ψ.source`. -/
private theorem exists_reebSliceChart_opens {W₀ : Opens E} (p₀ : W₀)
    {α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1} (hα₀ : α₀.IsContactForm) :
    ∃ (K : Submodule ℝ E) (S_K : Opens K) (s₀ : S_K) (β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1)
      (Ψ : PartialDiffeomorph 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) W₀ (S_K × ℝ) ∞),
      finrank ℝ K + 1 = finrank ℝ E ∧
      ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate ∧
      p₀ ∈ Ψ.source ∧ Ψ p₀ = (s₀, 0) ∧
      ∀ p ∈ Ψ.source, ∀ v : TangentSpace 𝓘(ℝ, E) p,
        (-β).contactization.val (Ψ p) ![mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p v] =
          α₀.val p ![v] := by
  obtain ⟨K, S_K, s₀, ι_K, hdimK, hι_K, hι_s₀, hι_inj, hR⟩ :=
    exists_contactHyperplaneSlice_opens p₀ hα₀
  let β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1 := SmoothForm.mpullback ι_K hι_K α₀
  have hnd₀ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate :=
    hα₀.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι_K hdimK hι_inj hR
  have h0_dom : ((0 : ℝ), ι_K s₀) ∈ flowDomain α₀.reebVectorField :=
    mem_flowDomain_zero (hα₀.contMDiff_reebVectorField.of_le (by simp)) _
  let F : S_K × ℝ → W₀ := fun q ↦ flowOf α₀.reebVectorField q.snd (ι_K q.fst)
  have hloc : IsLocalDiffeomorphAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ F (s₀, 0) :=
    hα₀.isLocalDiffeomorphAt_flowOf_reebVectorField_comp hι_K hdimK (p := (s₀, 0)) hι_inj hR h0_dom
  let D : Set (S_K × ℝ) := {q | (q.snd, ι_K q.fst) ∈ flowDomain α₀.reebVectorField}
  have hD : IsOpen D := isOpen_setOf_mem_flowDomain
    (hα₀.contMDiff_reebVectorField.of_le (by simp)) continuous_snd
    (hι_K.continuous.comp continuous_fst)
  have hfω : ∀ᶠ q in 𝓝 (s₀, (0 : ℝ)),
      mpullback (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, E) F α₀.val q = (-β).contactization.val q := by
    filter_upwards [hD.mem_nhds h0_dom] with q hq
    exact mpullback_flowOf_comp_apply_eq_contactization hα₀.contMDiff_reebVectorField hι_K
      hα₀.apply_reebVectorField hα₀.interior_mextDeriv_reebVectorField hq
  obtain ⟨Ψ, hsrc, hΨ, hpull⟩ := hloc.exists_partialDiffeomorph_mpullback_eq (by simp) hfω
  have hF0 : F (s₀, 0) = p₀ := by dsimp [F]; rw [flowOf_zero, hι_s₀]
  refine ⟨K, S_K, s₀, β, Ψ, hdimK, hnd₀, hF0 ▸ hsrc, hF0 ▸ hΨ, fun p hp v ↦ ?_⟩
  rw [← mpullback_apply_one, hpull p hp]

/-- Construct standard Euclidean symplectic Darboux coordinates `ψ : S_K → ℝⁿ × ℝⁿ` around a point
`s₀` of an open subset `S_K : Opens K` where `dβ` is nondegenerate. -/
private theorem exists_symplecticSliceDarboux_opens {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [FiniteDimensional ℝ K] {S_K : Opens K} {s₀ : S_K}
    {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1}
    (hnd₀ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (n : ℕ) (ψ : PartialDiffeomorph 𝓘(ℝ, K)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) S_K
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞),
      finrank ℝ K = 2 * n ∧ s₀ ∈ ψ.source ∧ ψ s₀ = 0 ∧
      ∀ z ∈ ψ.target,
        ∀ u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) z,
          (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z w) =
            stdSymplecticForm (NormedSpace.fromTangentSpace z u)
              (NormedSpace.fromTangentSpace z w) := by
  obtain ⟨n, ψ, hs₀, h0, hchart⟩ :=
    SmoothTwoForm.exists_standardDarbouxChart_of_nondegenerate_of_isInteriorPoint
      (SmoothForm.isClosed_mextDerivₗ β) hnd₀ BoundarylessManifold.isInteriorPoint
  have hdim : finrank ℝ K = 2 * n := by
    have hL := (ψ.isLocalDiffeomorphAt _ _ _ hs₀).finrank_eq (by simp)
    rw [finrank_prod, finrank_euclideanSpace_fin] at hL
    omega
  refine ⟨n, ψ, hdim, hs₀, h0, fun z hz u w ↦ ?_⟩
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
  have hinv_d (a : TangentSpace J z) :
      mvfderiv 𝓘(ℝ, K) ψ (ψ.symm z) (mfderiv J 𝓘(ℝ, K) ψ.symm z a) =
        NormedSpace.fromTangentSpace z a := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hz,
      NormedSpace.fromTangentSpace_apply]
  have key := hchart (ψ.symm z) (ψ.map_target hz) (mfderiv J 𝓘(ℝ, K) ψ.symm z u)
    (mfderiv J 𝓘(ℝ, K) ψ.symm z w)
  rwa [hinv_d u, hinv_d w] at key

/-- Pullback of `dβ` through `ψ.toDiffeomorphSourceTarget.symm` and `Subtype.val` evaluates via
`ψ.symm`. -/
private theorem mextDeriv_mpullback_symm_subtypeVal {K F : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup F] [NormedSpace ℝ F] {S_K : Opens K}
    (β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1) (ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, F) S_K F ∞)
    (x : (⟨ψ.target, ψ.open_target⟩ : Opens F)) (u w : TangentSpace 𝓘(ℝ, F) x) :
    mextDeriv (SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
        ψ.toDiffeomorphSourceTarget.symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β)).val x ![u, w] =
      (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm x.val)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm x.val
          (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x u))
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm x.val
          (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x w)) := by
  have hcomp : (Subtype.val : (⟨ψ.source, ψ.open_source⟩ : Opens S_K) → S_K) ∘
      ψ.toDiffeomorphSourceTarget.symm =
      ψ.symm ∘ (Subtype.val : (⟨ψ.target, ψ.open_target⟩ : Opens F) → F) :=
    funext fun y ↦ ψ.toDiffeomorphSourceTarget_symm_apply_coe y
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback,
    ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, SmoothForm.coe_mpullback, hcomp,
    mpullback_comp_at ((contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp) x)
      (ψ.symm.mdifferentiableAt (n := ∞) (by simp) x.property),
    mpullback_apply_pair, mpullback_apply_pair, Manifold.mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, ← SmoothBundleForm.eval₂_apply]

/-- On `ψ.target`, the sum of the pushed-forward slice one-form `β` and a smooth primitive `θ` of
`-ω₀` is closed. -/
private theorem mextDeriv_pullback_add_eq_zero {K F : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup F] [NormedSpace ℝ F] {S_K : Opens K}
    {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1} {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, F) S_K F ∞}
    {ω₀ : F → F → ℝ}
    (hψ_symp : ∀ z ∈ ψ.target, ∀ u w : TangentSpace 𝓘(ℝ, F) z,
      (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm z u) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm z w) =
        ω₀ (NormedSpace.fromTangentSpace z u) (NormedSpace.fromTangentSpace z w))
    (θ : SmoothForm 𝓘(ℝ, F) F ℝ 1)
    (hdθ : ∀ y (u w : TangentSpace 𝓘(ℝ, F) y),
      mextDeriv θ.val y ![u, w] =
        -ω₀ (NormedSpace.fromTangentSpace y u) (NormedSpace.fromTangentSpace y w)) :
    mextDeriv (SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
        ψ.toDiffeomorphSourceTarget.symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β) +
      SmoothForm.mpullback (Subtype.val : (⟨ψ.target, ψ.open_target⟩ : Opens F) → F)
        contMDiff_subtypeVal θ).val = 0 := by
  funext x
  refine ContinuousAlternatingMap.ext_fin_two fun u w ↦ ?_
  have hdβ : mextDeriv (SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
        ψ.toDiffeomorphSourceTarget.symm.contMDiff
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β)).val x ![u, w] =
      ω₀ (NormedSpace.fromTangentSpace x.val (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x u))
        (NormedSpace.fromTangentSpace x.val
          (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x w)) :=
    (mextDeriv_mpullback_symm_subtypeVal β ψ x u w).trans (hψ_symp x.val x.property _ _)
  have hdθ' : mextDeriv
        (SmoothForm.mpullback (Subtype.val : (⟨ψ.target, ψ.open_target⟩ : Opens F) → F)
          contMDiff_subtypeVal θ).val x ![u, w] =
      -ω₀ (NormedSpace.fromTangentSpace x.val (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x u))
        (NormedSpace.fromTangentSpace x.val
          (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, F)) x w)) := by
    rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback,
      mpullback_apply_pair, mextDerivₗ_apply, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
    exact hdθ x.val _ _
  rw [← mextDerivₗ_apply, map_add]
  simp [-SmoothForm.coe_mpullback, mextDerivₗ_apply, hdβ, hdθ']

/-- On an open neighbourhood `B ⊆ ψ.target` of `0`, construct a smooth function `g : B → ℝ`
vanishing at `0` such that the pushed-forward form `-β_B` differs from the restriction of a smooth
primitive `θ` of `-ω₀` by `dg`. -/
private theorem exists_primitive_on_symplecticSlice {K F : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {S_K : Opens K} {s₀ : S_K}
    {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1} {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, F) S_K F ∞}
    (hs₀ψ : s₀ ∈ ψ.source) (hψs₀ : ψ s₀ = 0) {ω₀ : F → F → ℝ}
    (hψ_symp : ∀ z ∈ ψ.target, ∀ u w : TangentSpace 𝓘(ℝ, F) z,
      (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm z u) (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm z w) =
        ω₀ (NormedSpace.fromTangentSpace z u) (NormedSpace.fromTangentSpace z w))
    (θ : SmoothForm 𝓘(ℝ, F) F ℝ 1)
    (hdθ : ∀ y (u w : TangentSpace 𝓘(ℝ, F) y),
      mextDeriv θ.val y ![u, w] =
        -ω₀ (NormedSpace.fromTangentSpace y u) (NormedSpace.fromTangentSpace y w)) :
    ∃ (B : Opens F) (hBU : B ≤ ⟨ψ.target, ψ.open_target⟩) (h0B : (0 : F) ∈ B) (g : B → ℝ),
      ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ g ∧ g ⟨0, h0B⟩ = 0 ∧
      (-SmoothForm.mpullback (Opens.inclusion hBU) (contMDiff_inclusion hBU)
        (SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
          ψ.toDiffeomorphSourceTarget.symm.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β))).val =
        (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ).val +
          mextDeriv (RoughForm.ofFunction 𝓘(ℝ, F) g) := by
  let U_t : Opens F := ⟨ψ.target, ψ.open_target⟩
  let β_t : SmoothForm 𝓘(ℝ, F) U_t ℝ 1 :=
    SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
      ψ.toDiffeomorphSourceTarget.symm.contMDiff
      (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β)
  let θ_t : SmoothForm 𝓘(ℝ, F) U_t ℝ 1 :=
    SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ
  have hclosed : mextDeriv (β_t + θ_t).val = 0 := mextDeriv_pullback_add_eq_zero hψ_symp θ hdθ
  let x₀ : U_t := ⟨0, hψs₀ ▸ ψ.map_source hs₀ψ⟩
  obtain ⟨g, hg, W, hx₀W, hprim⟩ :=
    exists_contMDiff_isPrimitiveOn (I := 𝓘(ℝ, F)) (r := ⊤) (by simp)
      (β_t + θ_t).isSmoothForm hclosed x₀
  -- Shift the local primitive to vanish at `0` and shrink to an open neighbourhood `B ⊆ ψ.target`.
  let g₀ : U_t → ℝ := fun z ↦ g z + (-g x₀)
  have hg₀ : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ g₀ := hg.add contMDiff_const
  have hprim₀ : IsPrimitiveOn (β_t + θ_t).val g₀ W := hprim.add_const (-g x₀)
  let B : Opens F :=
    ⟨Subtype.val '' W, U_t.isOpen.isOpenEmbedding_subtypeVal.isOpenMap W hprim₀.isOpen⟩
  have hBU : B ≤ U_t := by rintro _ ⟨z, -, rfl⟩; exact z.property
  have h0B : (0 : F) ∈ B := ⟨x₀, hx₀W, rfl⟩
  have hinc_mem (z : B) : Opens.inclusion hBU z ∈ W := by
    obtain ⟨w, hwW, hwz⟩ := z.property
    have : Opens.inclusion hBU z = w := Subtype.ext hwz.symm
    exact this ▸ hwW
  let g_B : B → ℝ := fun z ↦ -(g₀ (Opens.inclusion hBU z))
  have hg_B : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ) ∞ g_B := (hg₀.comp (contMDiff_inclusion hBU)).neg
  refine ⟨B, hBU, h0B, g_B, hg_B, by simp [g_B, g₀, Opens.inclusion, x₀], ?_⟩
  -- Compare `d g_B` with the pullback of `β_t + θ_t` to `B`.
  have hinc_diff : MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, F) (Opens.inclusion hBU) :=
    (contMDiff_inclusion hBU).mdifferentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hneg : RoughForm.ofFunction 𝓘(ℝ, F) g_B =
      -RoughForm.ofFunction 𝓘(ℝ, F) (g₀ ∘ Opens.inclusion hBU) := by
    funext y; ext v; simp [g_B, RoughForm.ofFunction_apply]
  have hθ_eq : mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (Opens.inclusion hBU) θ_t.val =
      mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) Subtype.val θ.val := by
    rw [SmoothForm.coe_mpullback, ← mpullback_comp hinc_diff
      ((contMDiff_subtypeVal (n := ∞)).mdifferentiable (by simp))]
    -- `Subtype.val ∘ Opens.inclusion hBU` is definitionally `Subtype.val : B → F`.
    exact congrArg (fun f ↦ mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) f θ.val) rfl
  funext z
  have hdg : mextDeriv (RoughForm.ofFunction 𝓘(ℝ, F) g_B) z =
      -mpullback 𝓘(ℝ, F) 𝓘(ℝ, F) (Opens.inclusion hBU) (β_t + θ_t).val z := by
    rw [hneg, mextDeriv_neg, Pi.neg_apply, (hprim₀.mpullback hinc_diff).mextDeriv_eq z (hinc_mem z)]
  simp only [SmoothForm.neg_toRoughForm, SmoothForm.coe_mpullback, SmoothForm.add_toRoughForm,
    Pi.neg_apply, Pi.add_apply, hdg, mpullback_add, hθ_eq, β_t]
  abel

/-- Pulling back a one-form along the four-step composition
`assoc ∘ Prod.map inc id ∘ contactizationShift g ∘ Prod.map e id` reduces to the contactization of
`e^* β` whenever `assoc^* α = θ.contactization` and `β = inc^* θ + dg`. -/
private theorem mpullback_contactization_comp
    {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ M₃ E₄ H₄ M₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]
    [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [TopologicalSpace H₄]
    {I₄ : ModelWithCorners ℝ E₄ H₄} [TopologicalSpace M₄] [ChartedSpace H₄ M₄] [IsManifold I₄ ∞ M₄]
    {e : M₁ → M₂} (he : ContMDiff I₁ I₂ ∞ e)
    {g : M₂ → ℝ} (hg : ContMDiff I₂ 𝓘(ℝ) ∞ g)
    {inc : M₂ → M₃} (hinc : ContMDiff I₂ I₃ ∞ inc)
    {assoc : M₃ × ℝ → M₄} (hassoc : ContMDiff (I₃.prod 𝓘(ℝ)) I₄ ∞ assoc)
    {α : SmoothForm I₄ M₄ ℝ 1} {θ : SmoothForm I₃ M₃ ℝ 1} {β : SmoothForm I₂ M₂ ℝ 1}
    (hassoc_pull : SmoothForm.mpullback assoc hassoc α = θ.contactization)
    (hshift_eq : β.val =
      (SmoothForm.mpullback inc hinc θ).val + mextDeriv (RoughForm.ofFunction I₂ g)) :
    SmoothForm.mpullback
      (assoc ∘ Prod.map inc id ∘ contactizationShift I₂ hg ∘ Prod.map e id)
      (hassoc.comp ((hinc.prodMap contMDiff_id).comp
        ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id)))) α =
      (SmoothForm.mpullback e he β).contactization := by
  rw [SmoothForm.mpullback_comp _ _
      ((hinc.prodMap contMDiff_id).comp
        ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id))) hassoc,
    LinearMap.comp_apply, hassoc_pull,
    SmoothForm.mpullback_comp _ _
      ((contactizationShift I₂ hg).contMDiff.comp (he.prodMap contMDiff_id))
      (hinc.prodMap contMDiff_id),
    LinearMap.comp_apply, SmoothForm.mpullback_prodMap_id_contactization θ hinc,
    SmoothForm.mpullback_comp _ _ (he.prodMap contMDiff_id) (contactizationShift I₂ hg).contMDiff,
    LinearMap.comp_apply, mpullback_contactizationShift_contactization hg hshift_eq,
    SmoothForm.mpullback_prodMap_id_contactization β he]

/-- Pulling `-β_t` on `ψ.target` back through `e_B : W_ψ → B` recovers `-β` restricted to
`W_ψ`. -/
private theorem mpullback_symplecticSlice_neg {K V : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S_K : Opens K} {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1}
    {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, V × V) S_K (V × V) ∞}
    {B : Opens (V × V)} (hBU : B ≤ ⟨ψ.target, ψ.open_target⟩)
    {W_ψ : Opens S_K} {e_B : W_ψ → B} (he_B : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V × V) ∞ e_B)
    (hx_src : ∀ x : W_ψ, x.val ∈ ψ.source) (hx_coe : ∀ x : W_ψ, (e_B x : V × V) = ψ x.val) :
    SmoothForm.mpullback e_B he_B
      (-SmoothForm.mpullback (Opens.inclusion hBU) (contMDiff_inclusion hBU)
        (SmoothForm.mpullback ψ.toDiffeomorphSourceTarget.symm
          ψ.toDiffeomorphSourceTarget.symm.contMDiff
          (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal β))) =
      SmoothForm.mpullback (Subtype.val : W_ψ → S_K) contMDiff_subtypeVal (-β) := by
  have he_inv : (Subtype.val : (⟨ψ.source, ψ.open_source⟩ : Opens S_K) → S_K) ∘
      ψ.toDiffeomorphSourceTarget.symm ∘ Opens.inclusion hBU ∘ e_B =
      (Subtype.val : W_ψ → S_K) := funext fun x ↦ by
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
      ψ.toDiffeomorphSourceTarget_symm_apply_coe,
      Set.coe_inclusion (SetLike.coe_subset_coe.2 hBU), hx_coe x]
    exact ψ.left_inv (hx_src x)
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have he := he_B.mdifferentiable hne
  have hinc : MDifferentiable 𝓘(ℝ, V × V) 𝓘(ℝ, V × V) (Opens.inclusion hBU) :=
    (contMDiff_inclusion hBU).mdifferentiable hne
  have hsym := ψ.toDiffeomorphSourceTarget.symm.contMDiff.mdifferentiable hne
  rw [map_neg, map_neg]; congr 1; apply Subtype.ext
  simp only [SmoothForm.coe_mpullback]
  rw [← mpullback_comp he hinc, ← mpullback_comp (hinc.comp he) hsym,
    ← mpullback_comp (hsym.comp (hinc.comp he))
      ((contMDiff_subtypeVal (n := ∞)).mdifferentiable hne), he_inv]

/-- Compose slice coordinates `ψ : S_K → V × V` with `contactizationShift` for `g : B → ℝ` and
reassociation `(V × V) × ℝ ≃ V × V × ℝ` to obtain a partial diffeomorphism
`Ω : S_K × ℝ → V × V × ℝ` sending `(s₀, 0)` to `0` together with the restricted slice map
`e_B : W_ψ → B`. -/
private theorem exists_contactizationChart {K V : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {S_K : Opens K} {s₀ : S_K} {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, V × V) S_K (V × V) ∞}
    (hs₀ψ : s₀ ∈ ψ.source) (hψs₀ : ψ s₀ = 0)
    {B : Opens (V × V)} (h0B : (0 : V × V) ∈ B)
    {g : B → ℝ} (hg : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ g) (hg0 : g ⟨0, h0B⟩ = 0) :
    ∃ (W_ψ : Opens S_K) (e_B : W_ψ → B)
      (Ω : PartialDiffeomorph (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) (S_K × ℝ) (V × V × ℝ) ∞),
      ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V × V) ∞ e_B ∧
      (∀ x : W_ψ, x.val ∈ ψ.source) ∧
      (∀ x : W_ψ, (e_B x : V × V) = ψ x.val) ∧
      (∀ q : S_K × ℝ, q ∈ Ω.source → q.1 ∈ (W_ψ : Set S_K)) ∧
      (s₀, (0 : ℝ)) ∈ Ω.source ∧ Ω (s₀, 0) = 0 ∧
      ⇑Ω ∘ (Prod.map (Subtype.val : W_ψ → S_K) (id : ℝ → ℝ)) =
        (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm ∘ Prod.map Subtype.val id ∘
          contactizationShift 𝓘(ℝ, V × V) hg ∘ Prod.map e_B id := by
  let sv_B := PartialDiffeomorph.subtypeVal 𝓘(ℝ, V × V) ∞ B ⟨⟨0, h0B⟩⟩
  let ψ_B := ψ.trans sv_B.symm
  let id_ℝ := (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph
  let shift := (contactizationShift 𝓘(ℝ, V × V) hg).toPartialDiffeomorph
  let inc_B := sv_B.prod id_ℝ
  let assoc := (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm.toPartialDiffeomorph
  let Ω := (ψ_B.prod id_ℝ).trans (shift.trans (inc_B.trans assoc))
  have hψB_src : ψ_B.source = ψ.source ∩ ψ ⁻¹' (B : Set (V × V)) := by
    simp [ψ_B, sv_B]
  have hψB_coe (x : S_K) : ψ_B x = sv_B.symm (ψ x) := by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply]
  have hψB_val (x : S_K) (hx : ψ x ∈ (B : Set (V × V))) : (ψ_B x : V × V) = ψ x := by
    rw [hψB_coe, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal_symm_apply B ⟨⟨0, h0B⟩⟩ hx]
  have hsrc (q : S_K × ℝ) : q ∈ Ω.source ↔ q.1 ∈ ψ_B.source := by
    simp [Ω, sv_B, id_ℝ, shift, inc_B, assoc, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  have hψB₀ : ψ_B s₀ = ⟨0, h0B⟩ := by
    rw [hψB_coe, hψs₀, PartialDiffeomorph.symm_toPartialEquiv,
      PartialDiffeomorph.subtypeVal_symm_apply B ⟨⟨0, h0B⟩⟩ h0B]
  have hΩ₀ : Ω (s₀, 0) = 0 := by
    simp [Ω, sv_B, id_ℝ, shift, inc_B, assoc, hψB₀, hg0,
      Diffeomorph.toPartialDiffeomorph_toPartialEquiv]
  let W_ψ : Opens S_K := ⟨ψ_B.source, ψ_B.open_source⟩
  let e_B : W_ψ → B := fun x ↦ ψ_B x.val
  have he_B : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V × V) ∞ e_B :=
    ψ_B.contMDiffOn.comp_contMDiff contMDiff_subtypeVal fun x ↦ x.property
  have hx_mem (x : W_ψ) : x.val ∈ ψ.source ∩ ψ ⁻¹' (B : Set (V × V)) := by
    rw [← hψB_src]
    simp [W_ψ]
  refine ⟨W_ψ, e_B, Ω, he_B, fun x ↦ (hx_mem x).1, fun x ↦ hψB_val x.val (hx_mem x).2,
    fun q hq ↦ (hsrc q).1 hq,
    (hsrc _).2 (by rw [hψB_src]; exact ⟨hs₀ψ, by simpa [hψs₀] using h0B⟩), hΩ₀, funext fun z ↦ ?_⟩
  simp [Ω, sv_B, e_B, id_ℝ, shift, inc_B, assoc, Diffeomorph.toPartialDiffeomorph_toPartialEquiv]

/-- Given slice Darboux coordinates `ψ : S_K → ℝⁿ × ℝⁿ` around `s₀` whose inverse `ψ.symm` pulls
`dβ` back to `stdSymplecticForm`, there exists a smooth partial diffeomorphism
`Ω : S_K × ℝ → ℝⁿ × ℝⁿ × ℝ` sending `(s₀, 0)` to `0` that pulls `innerProductContactForm` back to
`(-β).contactization` on `Ω.source`. -/
private theorem exists_contactizationToInnerProductChart {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {S_K : Opens K} {s₀ : S_K} {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1} {n : ℕ}
    {ψ : PartialDiffeomorph 𝓘(ℝ, K)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) S_K
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}
    (hs₀ψ : s₀ ∈ ψ.source) (hψs₀ : ψ s₀ = 0)
    (hψ_symp : ∀ z ∈ ψ.target,
      ∀ u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) z,
        (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z w) =
          stdSymplecticForm (NormedSpace.fromTangentSpace z u)
            (NormedSpace.fromTangentSpace z w)) :
    ∃ Ω : PartialDiffeomorph (𝓘(ℝ, K).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (S_K × ℝ)
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      (s₀, (0 : ℝ)) ∈ Ω.source ∧ Ω (s₀, 0) = 0 ∧
      ∀ q ∈ Ω.source, ∀ u : TangentSpace (𝓘(ℝ, K).prod 𝓘(ℝ)) q,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (Ω q)
          ![mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ω q u] = (-β).contactization.val q ![u] := by
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨B, hBU, h0B, g, hg, hg0, hshift_eq⟩ :=
    exists_primitive_on_symplecticSlice (ω₀ := fun v w ↦ stdSymplecticForm v w) hs₀ψ hψs₀ hψ_symp
      (innerProductMomentumForm V) mextDeriv_innerProductMomentumForm_apply
  obtain ⟨W_ψ, e_B, Ω, he_B, hx_src, hxB, hmemW, hs₀Ω, hΩ₀, hΩ_comp⟩ :=
    exists_contactizationChart hs₀ψ hψs₀ h0B hg hg0
  have hF_pull := mpullback_contactization_comp he_B hg contMDiff_subtypeVal
    (Diffeomorph.prodAssocSymmSelf ℝ V V ℝ ∞).symm.contMDiff
    (mpullback_prodAssocSymmSelf_symm_innerProductContactForm V) hshift_eq
  rw [mpullback_symplecticSlice_neg hBU he_B hx_src hxB,
    ← SmoothForm.mpullback_prodMap_id_contactization (-β) contMDiff_subtypeVal] at hF_pull
  refine ⟨Ω, hs₀Ω, hΩ₀, fun q hq u ↦ ?_⟩
  let inc_W : W_ψ × ℝ → S_K × ℝ := Prod.map Subtype.val id
  let q_W : W_ψ × ℝ := (⟨q.1, hmemW q hq⟩, q.2)
  have hpull_eq : mpullback (𝓘(ℝ, K).prod 𝓘(ℝ)) (𝓘(ℝ, K).prod 𝓘(ℝ)) inc_W
      (mpullback (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ) Ω (innerProductContactForm V).val) q_W =
      mpullback (𝓘(ℝ, K).prod 𝓘(ℝ)) (𝓘(ℝ, K).prod 𝓘(ℝ)) inc_W (-β).contactization.val q_W := by
    rw [← mpullback_comp_at (((contMDiff_subtypeVal (n := ∞)).prodMap contMDiff_id).mdifferentiable
        (by simp) q_W) (Ω.mdifferentiableAt (n := ∞) (by simp) hq), hΩ_comp]
    simpa only [SmoothForm.coe_mpullback] using congrFun (congrArg Subtype.val hF_pull) q_W
  have hsurj : Function.Surjective
      (mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) (𝓘(ℝ, K).prod 𝓘(ℝ)) inc_W q_W) :=
    (((isLocalDiffeomorph_subtype_val.prodMap
      (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).isLocalDiffeomorph) q_W).isInvertible_mfderiv
      (by simp)).surjective
  have heval :=
    congrArg (fun A ↦ A ![u]) ((mpullback_apply_eq_mpullback_apply_iff hsurj).1 hpull_eq)
  rwa [mpullback_apply_one, ← mvfderiv_apply_eq_mfderiv_apply] at heval

omit [FiniteDimensional ℝ E] in
/-- Transport a composite chart `Ω ∘ Ψ` from an open subset `W₀ : Opens E` to the ambient normed
space `E`, preserving source membership, vanishing at `p₀`, and the chain-rule derivative. -/
private theorem exists_partialDiffeomorph_trans_opens {E₁ H₁ M₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {W₀ : Opens E} (p₀ : W₀)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I₁ W₀ M₁ ∞) (Ω : PartialDiffeomorph I₁ 𝓘(ℝ, E₂) M₁ E₂ ∞)
    (hp₀Ψ : p₀ ∈ Ψ.source) {q₀ : M₁} (hΨp₀ : Ψ p₀ = q₀) (hq₀Ω : q₀ ∈ Ω.source)
    {z₀ : E₂} (hΩ₀ : Ω q₀ = z₀) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E₂) E E₂ ∞,
      (p₀ : E) ∈ Φ.source ∧ Φ.source ⊆ W₀ ∧ Φ p₀ = z₀ ∧
      ∀ y ∈ Φ.source, ∃ hyW : y ∈ (W₀ : Set E),
        (⟨y, hyW⟩ : W₀) ∈ Ψ.source ∧ Ψ ⟨y, hyW⟩ ∈ Ω.source ∧
        Φ y = Ω (Ψ ⟨y, hyW⟩) ∧
        ∀ v : E, fderiv ℝ Φ y v = mvfderiv I₁ Ω (Ψ ⟨y, hyW⟩) (mfderiv 𝓘(ℝ, E) I₁ Ψ ⟨y, hyW⟩
          ((Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) (⟨y, hyW⟩ : W₀)).symm
            ((NormedSpace.fromTangentSpace y).symm v))) := by
  let Ξ := Ψ.trans Ω
  have hp₀Ξ : p₀ ∈ Ξ.source := by
    rw [PartialDiffeomorph.trans_source]; exact ⟨hp₀Ψ, by simpa [hΨp₀] using hq₀Ω⟩
  let sv := PartialDiffeomorph.subtypeVal 𝓘(ℝ, E) ∞ W₀ ⟨p₀⟩
  let Φ := sv.symm.trans Ξ
  have hΦ_src : Φ.source = (W₀ : Set E) ∩ sv.symm ⁻¹' Ξ.source := by
    simp [Φ, sv]
  have hsv_p (q : W₀) : sv.symm (q : E) = q := by
    rw [PartialDiffeomorph.symm_toPartialEquiv]
    exact PartialDiffeomorph.subtypeVal_symm_apply_coe W₀ ⟨p₀⟩ q
  have hp₀Φ : (p₀ : E) ∈ Φ.source := by
    rw [hΦ_src, mem_inter_iff, mem_preimage, hsv_p p₀]
    exact ⟨p₀.property, hp₀Ξ⟩
  have hΦW₀ : Φ.source ⊆ W₀ := fun y hy ↦ (hΦ_src ▸ hy).1
  have hΦp₀ : Φ p₀ = z₀ := by
    rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hsv_p p₀,
      PartialDiffeomorph.coe_trans, Function.comp_apply, hΨp₀, hΩ₀]
  have heq_Φ : (Φ ∘ (Subtype.val : W₀ → E)) = ⇑Ω ∘ ⇑Ψ := funext fun q ↦ by
    rw [Function.comp_apply, PartialDiffeomorph.coe_trans, Function.comp_apply, hsv_p q,
      PartialDiffeomorph.coe_trans, Function.comp_apply]
  refine ⟨Φ, hp₀Φ, hΦW₀, hΦp₀, fun y hy ↦ ?_⟩
  let p : W₀ := ⟨y, hΦW₀ hy⟩
  have hpΞ : p ∈ Ξ.source := hsv_p p ▸ (hΦ_src ▸ hy).2
  have ⟨hpΨ, hpΩ⟩ : p ∈ Ψ.source ∩ Ψ ⁻¹' Ω.source :=
    PartialDiffeomorph.trans_source (Φ := Ψ) (Ψ := Ω) ▸ hpΞ
  refine ⟨hΦW₀ hy, hpΨ, hpΩ, congrFun heq_Φ p, fun v ↦ ?_⟩
  let v_p : TangentSpace 𝓘(ℝ, E) p := (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) p).symm
    ((NormedSpace.fromTangentSpace y).symm v)
  have hΦ_d : mvfderiv 𝓘(ℝ, E) (Φ ∘ (Subtype.val : W₀ → E)) p v_p = fderiv ℝ Φ y v := by
    have hΦm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E₂) Φ p.val :=
      Φ.mdifferentiableAt (n := ∞) (by simp) hy
    have hsvm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : W₀ → E) p :=
      (contMDiff_subtypeVal (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp)
    simp only [mvfderiv_comp_apply p hΦm hsvm, Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, v_p,
      ContinuousLinearEquiv.apply_symm_apply]
    dsimp only [p]
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hΩΨ_d : mvfderiv 𝓘(ℝ, E) (⇑Ω ∘ ⇑Ψ) p v_p =
      mvfderiv I₁ Ω (Ψ p) (mfderiv 𝓘(ℝ, E) I₁ Ψ p v_p) :=
    mvfderiv_comp_apply p (Ω.mdifferentiableAt (n := ∞) (by simp) hpΩ)
      (Ψ.mdifferentiableAt (n := ∞) (by simp) hpΨ) v_p
  rw [← hΦ_d, heq_Φ, hΩΨ_d]

/-- **The strict contact Darboux theorem on normed spaces.** Let `η` be a smooth one-form on an
open subset `W` of a finite-dimensional real normed space `E`, which is a contact form at `y₀ ∈ W`.
Then there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `Φ` from `E` to
`ℝⁿ × ℝⁿ × ℝ` with `y₀ ∈ Φ.source ⊆ W` and `Φ y₀ = 0` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` back to `η` on `Φ.source`. -/
theorem IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq
    {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) (hW : IsOpen W) (hy₀W : y₀ ∈ W)
    (hη : ContDiffOn ℝ ∞ η W) :
    ∃ (n : ℕ) (Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) E
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ y₀ ∈ Φ.source ∧ Φ.source ⊆ W ∧ Φ y₀ = 0 ∧
      ∀ y ∈ Φ.source, ∀ v : E,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (Φ y) ![fderiv ℝ Φ y v] =
          η y ![v] := by
  obtain ⟨W₀, p₀, α₀, hp₀_eq, hW₀W, hα₀, hα₀_coe⟩ := exists_opens_isContactForm hc hW hy₀W hη
  obtain ⟨K, S_K, s₀, β, Ψ, hdimK, hnd₀, hp₀Ψ, hΨp₀, hΨ_pull⟩ :=
    exists_reebSliceChart_opens p₀ hα₀
  obtain ⟨n, ψ, hdim₂, hs₀ψ, hψs₀, hψ_symp⟩ := exists_symplecticSliceDarboux_opens hnd₀
  obtain ⟨Ω, hs₀Ω, hΩ₀, hΩ_pull⟩ :=
    exists_contactizationToInnerProductChart hs₀ψ hψs₀ hψ_symp
  obtain ⟨Φ, hp₀Φ, hΦW₀, hΦp₀, hΦ⟩ :=
    exists_partialDiffeomorph_trans_opens p₀ Ψ Ω hp₀Ψ hΨp₀ hs₀Ω hΩ₀
  refine ⟨n, Φ, by omega, hp₀_eq ▸ hp₀Φ, hΦW₀.trans hW₀W, hp₀_eq ▸ hΦp₀, fun y hy v ↦ ?_⟩
  obtain ⟨hyW, hpΨ, hpΩ, hΦy, hchain⟩ := hΦ y hy
  let p : W₀ := ⟨y, hyW⟩
  refine (innerProductContactForm_apply _ (Φ y) (fderiv ℝ Φ y v)).trans ?_
  rw [hΦy, hchain v]
  refine (innerProductContactForm_apply _ (Ω (Ψ p)) _).symm.trans ?_
  rw [hΩ_pull (Ψ p) hpΩ, hΨ_pull p hpΨ, hα₀_coe]
  simp only [p, ContinuousLinearEquiv.apply_symm_apply]

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem on normed spaces, in dimension `2 n + 1`.** -/
theorem IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq_of_finrank_eq
    {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    (hW : IsOpen W) (hy₀W : y₀ ∈ W) (hη : ContDiffOn ℝ ∞ η W) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) E
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      y₀ ∈ Φ.source ∧ Φ.source ⊆ W ∧ Φ y₀ = 0 ∧
      ∀ y ∈ Φ.source, ∀ v : E,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (Φ y) ![fderiv ℝ Φ y v] =
          η y ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, Φ, hm, hy₀, hsub, h0, hΦ⟩ :=
    hc.exists_partialDiffeomorph_innerProductContactForm_eq hW hy₀W hη
  obtain rfl : m = n := by omega
  exact ⟨Φ, hy₀, hsub, h0, hΦ⟩

end NormedSpace

/-! ### Strict Contact Darboux charts on manifolds -/

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
/-- **Coordinate reduction and chart lifting for local contact forms at an interior point.**
Given a one-form `α` smooth on an open set `U` and contact at an interior point `x₀ ∈ U`, this
produces an open neighbourhood `W` of `extChartAt I x₀ x₀` on which `α.inChartAt x₀` is smooth
and contact at `extChartAt I x₀ x₀`, together with a lifting map sending any model-space partial
diffeomorphism `Φ` on `W` with `Φ (extChartAt I x₀ x₀) = 0` to a manifold partial diffeomorphism
`chart` with `x₀ ∈ chart.source ⊆ U`, `chart x₀ = 0`, and the chain-rule identification of
`mvfderiv I chart` and `α`. -/
theorem IsContactFormAt.exists_inChartAt_pullback {α : RoughForm I M ℝ 1} {U : Set M}
    {x₀ : M} (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ W : Set E, IsOpen W ∧ extChartAt I x₀ x₀ ∈ W ∧
      ContDiffOn ℝ ∞ (α.inChartAt x₀) W ∧
      IsContactFormAt (I := 𝓘(ℝ, E)) (α.inChartAt x₀) (extChartAt I x₀ x₀) ∧
      ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞),
        extChartAt I x₀ x₀ ∈ Φ.source → Φ.source ⊆ W → Φ (extChartAt I x₀ x₀) = 0 →
        ∃ chart : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞,
          x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
          ∀ x ∈ chart.source, extChartAt I x₀ x ∈ Φ.source ∧
            chart x = Φ (extChartAt I x₀ x) ∧
            ∀ v : TangentSpace I x,
              mvfderiv I chart x v =
                fderiv ℝ Φ (extChartAt I x₀ x) (mvfderiv I (extChartAt I x₀) x v) ∧
              α x ![v] = α.inChartAt x₀ (extChartAt I x₀ x)
                ![mvfderiv I (extChartAt I x₀) x v] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  set e := extChartAt I x₀
  set W : Set E := interior e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hy₀W : e x₀ ∈ W :=
    ⟨I.isInteriorPoint_iff.1 hx₀, by rw [mem_preimage, extChartAt_to_inv]; exact hx₀U⟩
  refine ⟨W, hW, hy₀W, α.contDiffOn_inChartAt_of_contMDiffOn hU hα x₀,
    (isContactFormAt_inChartAt_iff hx₀).2 hc, fun Φ hy₀Φ hΦW hΦ₀ ↦ ?_⟩
  obtain ⟨chart, hsrc, hcoe, hmvf⟩ :=
    exists_partialDiffeomorph_comp_extChartAt I ∞ x₀ hW inter_subset_left (by simp) Φ
  have hx₀_src : x₀ ∈ chart.source := hsrc ▸ ⟨mem_extChartAt_source x₀, hy₀W, hy₀Φ⟩
  refine ⟨chart, hx₀_src, fun x hx ↦ ?_, by rw [hcoe, hΦ₀], fun x hx ↦ ?_⟩
  · rw [hsrc] at hx
    have hU' := (hΦW hx.2.2).2
    rwa [mem_preimage, e.left_inv hx.1] at hU'
  · have hxS := hsrc ▸ hx
    refine ⟨hxS.2.2, hcoe x, fun v ↦ ⟨hmvf x hx v, ?_⟩⟩
    rw [RoughForm.apply_eq_inChartAt_mvfderiv α hxS.1]
    simp only [Matrix.vec_single_eq_const, e]

/-- **The strict contact Darboux theorem** for a locally defined one-form. Let `α` be a one-form on
`M` which is smooth on an open set `U` and is a contact form at an interior point `x₀ ∈ U`. Then
there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `chart` from `M` to
`ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0` which pulls the standard contact
form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint {α : RoughForm I M ℝ 1}
    {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α x ![v] := by
  obtain ⟨W, hW, hy₀W, hη, hc_in, hlift⟩ := hc.exists_inChartAt_pullback hU hx₀U hα hx₀
  obtain ⟨n, Φ, hdim, hy₀Φ, hΦW, hΦ₀, hΦ⟩ :=
    hc_in.exists_partialDiffeomorph_innerProductContactForm_eq hW hy₀W hη
  obtain ⟨chart, hx₀_src, hsubU, hchart_x₀, hchart⟩ := hlift Φ hy₀Φ hΦW hΦ₀
  refine ⟨n, chart, hdim, hx₀_src, hsubU, hchart_x₀, fun x hx v ↦ ?_⟩
  obtain ⟨hxΦ, hcx, hmvf⟩ := hchart x hx
  rw [hcx, (hmvf v).1, hΦ _ hxΦ, (hmvf v).2]

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** On a
manifold of dimension `2 n + 1`, the strict contact Darboux chart of a local contact form at an
interior point lands in `ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : RoughForm I M ℝ 1} {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀) {n : ℕ}
    (hn : finrank ℝ E = 2 * n + 1) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α x ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, chart, hm, hx₀', h⟩ := hc.exists_strictDarbouxChart_of_isInteriorPoint hU hx₀U hα hx₀
  obtain rfl : m = n := by omega
  exact ⟨chart, hx₀', h⟩

/-- **The strict contact Darboux theorem at an interior point.** Around any interior point `x₀` of
a manifold with a smooth contact form `α`, there are `n` with `dim E = 2 n + 1` and a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0` which pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on
`chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨n, chart, hdim, hx₀', -, h0, hchart⟩ :=
    (SmoothForm.isContactForm_iff_forall_isContactFormAt.1 hα
      x₀).exists_strictDarbouxChart_of_isInteriorPoint isOpen_univ (mem_univ x₀)
      α.contMDiff.contMDiffOn hx₀
  exact ⟨n, chart, hdim, hx₀', h0, hchart⟩

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** On a
manifold of dimension `2 n + 1` with a smooth contact form, the strict contact Darboux chart at an
interior point lands in `ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, chart, hm, hx₀', h⟩ := hα.exists_strictDarbouxChart_of_isInteriorPoint hx₀
  obtain rfl : m = n := by omega
  exact ⟨chart, hx₀', h⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **The strict contact Darboux theorem** for a locally defined one-form on a boundaryless
manifold. -/
theorem IsContactFormAt.exists_strictDarbouxChart {α : RoughForm I M ℝ 1} {U : Set M} {x₀ : M}
    (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α x ![v] :=
  hc.exists_strictDarbouxChart_of_isInteriorPoint hU hx₀U hα BoundarylessManifold.isInteriorPoint

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem in dimension `2 n + 1`** for a locally defined one-form on
a boundaryless manifold. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq {α : RoughForm I M ℝ 1} {U : Set M}
    {x₀ : M} (hc : IsContactFormAt α x₀) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (hU : IsOpen U)
    (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α x ![v] :=
  hc.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn hU hx₀U hα
    BoundarylessManifold.isInteriorPoint

/-- **The strict contact Darboux theorem.** Around every point `x₀` of a boundaryless manifold with
a smooth contact form `α`, there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism
`chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0` which pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] :=
  hα.exists_strictDarbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem in dimension `2 n + 1`.** On a boundaryless manifold of
dimension `2 n + 1` with a smooth contact form, the strict contact Darboux chart lands in
`ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] :=
  hα.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint

end Boundaryless

end Manifold

end TauCeti
