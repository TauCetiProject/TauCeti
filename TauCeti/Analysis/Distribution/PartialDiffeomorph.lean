/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LinearEquiv
public import TauCeti.Analysis.Distribution.TestFunction.PartialDiffeomorph
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Pullback of distributions along partial diffeomorphisms

Let `Φ` be a smooth partial diffeomorphism of a finite-dimensional real normed space `E`, and let
`V`, `Ω` be open sets with `V` contained in the source of `Φ` and `Φ '' V ⊆ Ω`. A distribution `T`
on `Ω` pulls back along `Φ` to the distribution

`(Φ^* T) φ = T (|det D(Φ⁻¹)| (φ ∘ Φ⁻¹))`

on `V`, the transpose of the pushforward of test densities
`PartialDiffeomorph.pushforwardTestFunction`. The Jacobian factor is what makes the pullback of a
locally integrable function `f` the function `f ∘ Φ`
(`Distribution.compCLMOfPartialDiffeomorph_ofFun`), by the change of variables formula. So `Φ^*`
extends the pullback of functions to all distributions; this is how a distribution on a manifold is
read in a chart, and how its readings in two charts are compared. On the point mass at `Φ x` the
pullback is `|det DΦ(x)|⁻¹` times the point mass at `x`. Pullback is contravariantly functorial,
`(Ψ ∘ Φ)^* = Φ^* ∘ Ψ^*`, undone by the pullback along `Φ⁻¹`, and does not enlarge supports. For a
linear automorphism it is the linear change of variables
`Distribution.compCLMOfContinuousLinearEquiv`.

## Main declarations

* `Distribution.compCLMOfPartialDiffeomorph Φ hV hVΩ`: the pullback `T ↦ Φ^* T`, as a continuous
  linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(V, F)`.
* `Distribution.compCLMOfPartialDiffeomorph_ofFun`: `Φ^*` sends the distribution of a locally
  integrable function `f` to that of `f ∘ Φ`, for any additive Haar measure.
* `MeasureTheory.LocallyIntegrableOn.comp_partialDiffeomorph_of_mapsTo`: local integrability is
  preserved by such a change of variables.
* `Distribution.compCLMOfPartialDiffeomorph_delta`: `Φ^* δ_{Φ x} = |det DΦ(x)|⁻¹ δ_x`.
* `Distribution.compCLMOfPartialDiffeomorph_trans`,
  `Distribution.compCLMOfPartialDiffeomorph_symm_compCLMOfPartialDiffeomorph`: functoriality.
* `Distribution.inter_dsupport_compCLMOfPartialDiffeomorph_subset`: `supp Φ^* T ⊆ Φ⁻¹ (supp T)`
  on `V`.
* `Distribution.compCLMOfPartialDiffeomorph_toPartialDiffeomorph`: for a linear automorphism the
  pullback is `Distribution.compCLMOfContinuousLinearEquiv`.
* `Distribution.complexPairing_compCLMOfPartialDiffeomorph`: the complex-linear extension of
  `Φ^* T` is computed by the same formula.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (the pullback of
  distributions by a diffeomorphism).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞}

/-- **Local integrability is preserved by a smooth change of variables**: if `f` is locally
integrable on `t` for an additive Haar measure, and `Φ` maps an open subset `s` of its source into
`t`, then `f ∘ Φ` is locally integrable on `s`. -/
theorem MeasureTheory.LocallyIntegrableOn.comp_partialDiffeomorph_of_mapsTo [MeasurableSpace E]
    [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f : E → F} {s t : Set E} (hf : LocallyIntegrableOn f t μ)
    (hs : IsOpen s) (hsΦ : s ⊆ Φ.source) (hst : MapsTo Φ s t) :
    LocallyIntegrableOn (fun x ↦ f (Φ x)) s μ := by
  rw [locallyIntegrableOn_iff hs.isLocallyClosed]
  intro K hKs hK
  have hΦK : IsCompact (Φ '' K) :=
    hK.image_of_continuousOn (Φ.contMDiffOn.continuousOn.mono (hKs.trans hsΦ))
  have hK' : Φ '' K ⊆ Φ.target := image_subset_iff.2 fun x hx ↦ Φ.map_source (hsΦ (hKs hx))
  -- On `Φ '' K`, the function `|det D(Φ⁻¹)| f` is integrable: `f` is, and the Jacobian is
  -- continuous on this compact set.
  have hJ : ContinuousOn (fun y ↦ |(fderiv ℝ Φ.symm y).det|) (Φ '' K) :=
    Φ.contDiffOn_abs_det_fderiv_symm.continuousOn.mono hK'
  have hint : IntegrableOn (fun y ↦ |(fderiv ℝ Φ.symm y).det| • f y) (Φ '' K) μ :=
    (hf.integrableOn_compact_subset (image_subset_iff.2 (hst.mono_left hKs)) hΦK).continuousOn_smul
      hJ hΦK
  -- Change variables `y = Φ x` on `K`; the two Jacobians cancel.
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ hK.measurableSet
    (fun x hx ↦ (Φ.differentiableAt (by simp) (hsΦ (hKs hx))).hasFDerivAt.hasFDerivWithinAt)
    (Φ.toPartialEquiv.injOn.mono (hKs.trans hsΦ))] at hint
  refine hint.congr_fun (fun x hx ↦ ?_) hK.measurableSet
  beta_reduce
  rw [smul_smul, ← abs_mul, mul_comm, Φ.det_fderiv_symm_mul_det_fderiv (by simp) (hsΦ (hKs hx)),
    abs_one, one_smul]

namespace Distribution

variable {W V Ω : Opens E}

section General

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul ℝ F]

/-- The **pullback of a distribution along a partial diffeomorphism**: for `V` contained in the
source of `Φ` and `Φ '' V ⊆ Ω`, a distribution `T` on `Ω` pulls back to the distribution
`φ ↦ T (|det D(Φ⁻¹)| (φ ∘ Φ⁻¹))` on `V`, the transpose of the pushforward of test densities. On
the distribution of a locally integrable function `f` it gives that of `f ∘ Φ`
(`Distribution.compCLMOfPartialDiffeomorph_ofFun`). -/
def compCLMOfPartialDiffeomorph (Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)
    (hV : (V : Set E) ⊆ Φ.source) (hVΩ : MapsTo Φ V Ω) : 𝓓'(Ω, F) →L[ℝ] 𝓓'(V, F) :=
  (Φ.pushforwardTestFunction hV hVΩ).precompCompactConvergenceCLM F

variable {hV : (V : Set E) ⊆ Φ.source} {hVΩ : MapsTo Φ V Ω}

/-- The pullback `Φ^* T` pairs a test function `φ` with `T` through the pushforward of `φ`. -/
@[simp]
theorem compCLMOfPartialDiffeomorph_apply (T : 𝓓'(Ω, F)) (φ : 𝓓(V, ℝ)) :
    compCLMOfPartialDiffeomorph Φ hV hVΩ T φ = T (Φ.pushforwardTestFunction hV hVΩ φ) :=
  (rfl)

/-- **Functoriality.** Pulling back along a composite `Ψ ∘ Φ` of partial diffeomorphisms is pulling
back along `Ψ` and then along `Φ`. -/
theorem compCLMOfPartialDiffeomorph_trans {Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞}
    (hΩ : (Ω : Set E) ⊆ Ψ.source) (hΩW : MapsTo Ψ Ω W) (hVt : (V : Set E) ⊆ (Φ.trans Ψ).source)
    (hVW : MapsTo (Φ.trans Ψ) V W) (T : 𝓓'(W, F)) :
    compCLMOfPartialDiffeomorph (Φ.trans Ψ) hVt hVW T =
      compCLMOfPartialDiffeomorph Φ hV hVΩ (compCLMOfPartialDiffeomorph Ψ hΩ hΩW T) := by
  ext φ
  simp only [compCLMOfPartialDiffeomorph_apply,
    PartialDiffeomorph.pushforwardTestFunction_trans (hV := hV) (hVΩ := hVΩ) hΩ hΩW hVt hVW]

/-- Pulling back along `Φ` and then along `Φ⁻¹` gives back a distribution on a subset `Ω` of the
target that `Φ⁻¹` maps into `V`. -/
@[simp]
theorem compCLMOfPartialDiffeomorph_symm_compCLMOfPartialDiffeomorph
    (hΩ : (Ω : Set E) ⊆ Φ.symm.source) (hΩV : MapsTo Φ.symm Ω V) (T : 𝓓'(Ω, F)) :
    compCLMOfPartialDiffeomorph Φ.symm hΩ hΩV (compCLMOfPartialDiffeomorph Φ hV hVΩ T) = T := by
  ext φ
  simp

/-- **Support of a pullback.** On `V`, the support of the pullback `Φ^* T` lies in the preimage
under `Φ` of the support of `T`. -/
theorem inter_dsupport_compCLMOfPartialDiffeomorph_subset (T : 𝓓'(Ω, F)) :
    (V : Set E) ∩ dsupport (compCLMOfPartialDiffeomorph Φ hV hVΩ T) ⊆ Φ ⁻¹' dsupport T := by
  rintro x ⟨hxV, hx⟩
  by_contra hxT
  obtain ⟨s, hT, hs, hxs⟩ := (notMem_dsupport_iff _).1 hxT
  -- `T` vanishes on `s`, so `Φ^* T` vanishes on the open set `V ∩ Φ⁻¹ s`, which contains `x`.
  refine (notMem_dsupport_iff (f := compCLMOfPartialDiffeomorph Φ hV hVΩ T) x).2
    ⟨V ∩ Φ ⁻¹' s, fun φ hφ ↦ ?_,
      (Φ.contMDiffOn.continuousOn.mono hV).isOpen_inter_preimage V.isOpen hs, hxV, hxs⟩ hx
  rw [compCLMOfPartialDiffeomorph_apply]
  refine hT _ ((Φ.tsupport_pushforwardTestFunction_subset φ).trans ?_)
  exact image_subset_iff.2 fun y hy ↦ (hφ hy).2

/-- For a linear automorphism `e` of `E`, the pullback along `e` as a partial diffeomorphism is the
linear change of variables `Distribution.compCLMOfContinuousLinearEquiv`. -/
theorem compCLMOfPartialDiffeomorph_toPartialDiffeomorph (e : E ≃L[ℝ] E) (hVΩ : MapsTo e V Ω) :
    (compCLMOfPartialDiffeomorph (e.toPartialDiffeomorph (n := ∞)) (by simp) (by simpa using hVΩ) :
        𝓓'(Ω, F) →L[ℝ] 𝓓'(V, F)) =
      compCLMOfContinuousLinearEquiv e hVΩ := by
  ext T φ
  rw [compCLMOfPartialDiffeomorph_apply, compCLMOfContinuousLinearEquiv_apply,
    ContinuousLinearEquiv.pushforwardTestFunction_toPartialDiffeomorph, map_smul]

end General

/-- The pullback of the point mass at `Φ x` is `|det DΦ(x)|⁻¹` times the point mass at `x`. -/
theorem compCLMOfPartialDiffeomorph_delta {hV : (V : Set E) ⊆ Φ.source} {hVΩ : MapsTo Φ V Ω}
    {x : E} (hx : x ∈ V) :
    compCLMOfPartialDiffeomorph Φ hV hVΩ (delta (Φ x) : 𝓓'(Ω, ℝ)) =
      |(fderiv ℝ Φ x).det|⁻¹ • (delta x : 𝓓'(V, ℝ)) := by
  ext φ
  simp [PartialDiffeomorph.pushforwardTestFunction_apply_apply φ (hV hx)]

/-- **Change of variables.** On the distribution of a function `f` locally integrable on `Ω`, the
pullback along `Φ` is the distribution of `f ∘ Φ`, for any additive Haar measure. -/
theorem compCLMOfPartialDiffeomorph_ofFun [MeasurableSpace E] [BorelSpace E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {hV : (V : Set E) ⊆ Φ.source} {hVΩ : MapsTo Φ V Ω}
    (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → F} (hf : LocallyIntegrableOn f Ω μ) :
    compCLMOfPartialDiffeomorph Φ hV hVΩ (ofFun Ω f μ ⊤) = ofFun V (fun x ↦ f (Φ x)) μ ⊤ := by
  ext φ
  rw [compCLMOfPartialDiffeomorph_apply, ofFun_apply hf,
    ofFun_apply (hf.comp_partialDiffeomorph_of_mapsTo V.isOpen hV hVΩ)]
  -- Both integrands vanish off the open sets `Φ '' V` and `V`, which correspond under `Φ`.
  have hpush : ∀ y ∉ Φ '' V, Φ.pushforwardTestFunction hV hVΩ φ y • f y = 0 := fun y hy ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy
      (image_mono (φ.tsupport_subset) (Φ.tsupport_pushforwardTestFunction_subset φ h)), zero_smul]
  have hφ : ∀ x ∉ (V : Set E), φ x • f (Φ x) = 0 := fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (φ.tsupport_subset h), zero_smul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hpush,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hφ,
    integral_image_eq_integral_abs_det_fderiv_smul μ V.isOpen.measurableSet
      (fun x hx ↦ (Φ.differentiableAt (by simp) (hV hx)).hasFDerivAt.hasFDerivWithinAt)
      (Φ.toPartialEquiv.injOn.mono hV)]
  refine setIntegral_congr_fun V.isOpen.measurableSet fun x hx ↦ ?_
  have hdet := right_ne_zero_of_mul_eq_one (Φ.det_fderiv_symm_mul_det_fderiv (by simp) (hV hx))
  rw [PartialDiffeomorph.pushforwardTestFunction_apply_apply φ (hV hx), smul_eq_mul, smul_smul,
    ← mul_assoc, mul_inv_cancel₀ (abs_ne_zero.2 hdet), one_mul]

/-- The complex-linear extension of the pullback `Φ^* T` of a complex distribution pairs a complex
test function `φ` with `T` through the pushforward of `φ`. -/
theorem complexPairing_compCLMOfPartialDiffeomorph {hV : (V : Set E) ⊆ Φ.source}
    {hVΩ : MapsTo Φ V Ω} (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(V, ℂ)) :
    (compCLMOfPartialDiffeomorph Φ hV hVΩ T).complexPairing φ =
      T.complexPairing (Φ.pushforwardTestFunction hV hVΩ φ) := by
  simp only [complexPairing_apply, compCLMOfPartialDiffeomorph_apply,
    PartialDiffeomorph.pushforwardTestFunction_postcompCLM]

end Distribution
