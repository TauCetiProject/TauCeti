/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The formal adjoint of the linearized Floer operator

The linearized Floer operator along a map `u : ℝ × ℝ → V` into a symplectic vector space is
`D_u ξ = ∂s ξ + A ∂t ξ + S ξ`, with leading coefficient `A(z) = J(z, u z)` and zeroth-order
coefficient `S = TauCeti.SymplecticForm.floerLinearizationCoeff`
(`TauCeti.SymplecticForm.floerLinearization_eq_add`). Its cokernel is described by covector
fields `η : ℝ × ℝ → V →L[ℝ] ℝ` that annihilate the image of `D_u` under the pairing
`ξ ↦ ∫ η(D_u ξ)`; this is how cokernel elements enter the transversality arguments of
`TauCeti.Geometry.Symplectic.Floer.Transversality.AlmostComplexVariation`. This file identifies
these covector fields, when they are `C¹`, as the solutions of a first-order equation.

The **formal adjoint** of `D_u` acts on covector fields by
`D_u^* η = -∂s η - ∂t (η ∘ A) + η ∘ S`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint`).

* **Integration by parts.** For a `C¹` section `ξ` of compact support and a covector field `η`
  that is `C¹` on the support of `ξ`, `∫ η(D_u ξ) = ∫ (D_u^* η)(ξ)` for every additive Haar
  measure on `ℝ × ℝ`
  (`integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply`).
* **Cokernel elements solve the adjoint equation.** On an open set `U` of the domain where the
  data are regular, a `C¹` covector field annihilates `D_u ξ` for every smooth section `ξ`
  compactly supported in `U` exactly when `D_u^* η = 0` on `U`
  (`forall_integral_apply_floerLinearization_eq_zero_iff`).
* **The adjoint equation is of Cauchy–Riemann type.** By the product rule,
  `D_u^* η = -(∂s η + Aᵀ ∂t η + (∂t A - S)ᵀ η)`, where `Bᵀ θ = θ ∘ B` is the transpose
  (`floerLinearizationAdjoint_eq_neg`). When `A` is a complex structure, `A² = -1`, so is
  `Aᵀ`, and up to sign `D_u^*` is again an operator `∂s + Aᵀ ∂t + C` on covector fields with a
  complex structure as leading coefficient and a continuous zeroth-order term. So cokernel
  elements are governed by the same local theory as kernel elements, such as unique
  continuation. This is the step by which a cokernel element that vanishes on an open set, as
  the localized variations of the Hamiltonian perturbation force
  (`TauCeti.SymplecticForm.eqOn_zero_of_forall_integral_apply_floerOperator_add_sub_eq_zero`),
  is shown to vanish on the whole connected domain.

No Sobolev completion is used: test sections are classical, and the adjoint is applied to `C¹`
covector fields.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and the proof of Proposition 3.2.1, on the
  formal adjoint of the linearized operator and its role in transversality.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292.
-/

public section

open MeasureTheory Set ContinuousLinearMap

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u : ℝ × ℝ → V} {η η' : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ}

variable (ω J Ks Kt u η z) in
/-- The **formal adjoint of the linearized Floer operator** on covector fields:
`D_u^* η = -∂s η - ∂t (η ∘ J(·, u ·)) + η ∘ S`, where `S` is the zeroth-order part
`floerLinearizationCoeff` of the linearized Floer operator `floerLinearization`. -/
noncomputable def floerLinearizationAdjoint : V →L[ℝ] ℝ :=
  -fderiv ℝ η z stdComplexLineReal -
      fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
    (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z)

variable (ω J Ks Kt u η z) in
/-- The coordinate expression of the formal adjoint. -/
theorem floerLinearizationAdjoint_def :
    ω.floerLinearizationAdjoint J Ks Kt u η z =
      -fderiv ℝ η z stdComplexLineReal -
          fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
        (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z) :=
  (rfl)

/-- **The adjoint operator is of Cauchy–Riemann type.** With `A = J(·, u ·)` and `S` the
zeroth-order part of the linearized operator,
`D_u^* η = -(∂s η + (∂t η) ∘ A + η ∘ (∂t A - S))`. -/
theorem floerLinearizationAdjoint_eq_neg (hη : DifferentiableAt ℝ η z)
    (hA : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u η z =
      -(fderiv ℝ η z stdComplexLineReal + (fderiv ℝ η z stdComplexLineImag).comp (J z (u z)) +
        (η z).comp (fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
          ω.floerLinearizationCoeff J Ks Kt u z)) := by
  rw [floerLinearizationAdjoint_def, fderiv_clm_comp hη hA]
  simp only [add_apply, comp_apply, compL_apply, flip_apply, comp_sub]
  abel

/-- **The adjoint equation.** `D_u^* η` vanishes at `z` exactly when
`∂s η + (∂t η) ∘ A + η ∘ (∂t A - S) = 0` there, with `A = J(·, u ·)`. -/
theorem floerLinearizationAdjoint_eq_zero_iff (hη : DifferentiableAt ℝ η z)
    (hA : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u η z = 0 ↔
      fderiv ℝ η z stdComplexLineReal + (fderiv ℝ η z stdComplexLineImag).comp (J z (u z)) +
        (η z).comp (fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
          ω.floerLinearizationCoeff J Ks Kt u z) = 0 := by
  rw [floerLinearizationAdjoint_eq_neg hη hA, neg_eq_zero]

/-- The formal adjoint is additive on covector fields differentiable at the domain point, when
`J(·, u ·)` is differentiable there. -/
@[simp]
theorem floerLinearizationAdjoint_add (hη : DifferentiableAt ℝ η z)
    (hη' : DifferentiableAt ℝ η' z) (hA : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (η + η') z =
      ω.floerLinearizationAdjoint J Ks Kt u η z + ω.floerLinearizationAdjoint J Ks Kt u η' z := by
  rw [floerLinearizationAdjoint_eq_neg (hη.add hη') hA, floerLinearizationAdjoint_eq_neg hη hA,
    floerLinearizationAdjoint_eq_neg hη' hA, fderiv_add hη hη']
  simp only [add_apply, Pi.add_apply, add_comp]
  abel

/-- The formal adjoint is subtractive on covector fields differentiable at the domain point, when
`J(·, u ·)` is differentiable there. -/
@[simp]
theorem floerLinearizationAdjoint_sub (hη : DifferentiableAt ℝ η z)
    (hη' : DifferentiableAt ℝ η' z) (hA : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (η - η') z =
      ω.floerLinearizationAdjoint J Ks Kt u η z - ω.floerLinearizationAdjoint J Ks Kt u η' z := by
  rw [floerLinearizationAdjoint_eq_neg (hη.sub hη') hA, floerLinearizationAdjoint_eq_neg hη hA,
    floerLinearizationAdjoint_eq_neg hη' hA, fderiv_sub hη hη']
  simp only [sub_apply, Pi.sub_apply, sub_comp]
  abel

/-- The formal adjoint commutes with real scaling of covector fields differentiable at the domain
point, when `J(·, u ·)` is differentiable there. -/
@[simp]
theorem floerLinearizationAdjoint_smul (c : ℝ) (hη : DifferentiableAt ℝ η z)
    (hA : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationAdjoint J Ks Kt u (c • η) z =
      c • ω.floerLinearizationAdjoint J Ks Kt u η z := by
  rw [floerLinearizationAdjoint_eq_neg (hη.const_smul c) hA,
    floerLinearizationAdjoint_eq_neg hη hA, fderiv_const_smul hη c]
  simp only [smul_apply, Pi.smul_apply, smul_comp, smul_add, smul_neg]

/-- The formal adjoint sends the zero covector field to zero. -/
@[simp]
theorem floerLinearizationAdjoint_zero :
    ω.floerLinearizationAdjoint J Ks Kt u 0 z = 0 := by
  simp [floerLinearizationAdjoint_def]

/-- **Continuity of the formal adjoint.** If `J` is `C¹` and the Hamiltonians are `C²` at
`(z, u z)`, and `u` and the covector field `η` are `C¹` at `z`, then `D_u^* η` is continuous at
`z`. -/
theorem continuousAt_floerLinearizationAdjoint
    (hJ : ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z)
    (hη : ContDiffAt ℝ 1 η z) :
    ContinuousAt (ω.floerLinearizationAdjoint J Ks Kt u η) z := by
  have hA : ContDiffAt ℝ 1 (fun w ↦ J w (u w)) z := (hJ.comp z (contDiffAt_id.prodMk hu) :)
  have hdη (v : ℝ × ℝ) : ContinuousAt (fun w ↦ fderiv ℝ η w v) z :=
    (hη.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hdηA : ContinuousAt (fun w ↦ fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) w
      stdComplexLineImag) z :=
    ((hη.clm_comp hA).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  exact ((hdη _).neg.sub hdηA).add
    (hη.continuousAt.clm_comp (ω.continuousAt_floerLinearizationCoeff hJ hKs hKt hu))

/-- **Continuity of the formal adjoint on a set.** If `J` is `C¹` and the Hamiltonians are `C²`
at the points `(z, u z)` with `z ∈ K`, and `u` and `η` are `C¹` at the points of `K`, then
`D_u^* η` is continuous on `K`. -/
theorem continuousOn_floerLinearizationAdjoint {K : Set (ℝ × ℝ)}
    (hJ : ∀ z ∈ K, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ K, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ K, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ K, ContDiffAt ℝ 1 η z) :
    ContinuousOn (ω.floerLinearizationAdjoint J Ks Kt u η) K := fun z hz ↦
  (continuousAt_floerLinearizationAdjoint (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
    (hη z hz)).continuousWithinAt

variable {μ : Measure (ℝ × ℝ)} [μ.IsAddHaarMeasure] {ξ : ℝ × ℝ → V}

/-- **Integration by parts for the linearized Floer operator.** Let `ξ` be a `C¹` section of
compact support. Suppose that at the points `z` of its support `J` is `C¹` and the Hamiltonians
are `C²` at `(z, u z)`, and `u` and the covector field `η` are `C¹` at `z`. Then
`∫ η(D_u ξ) = ∫ (D_u^* η)(ξ)` for every additive Haar measure on `ℝ × ℝ`. -/
theorem integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply
    (hJ : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 η z)
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) :
    ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) ∂μ =
      ∫ z, ω.floerLinearizationAdjoint J Ks Kt u η z (ξ z) ∂μ := by
  set ηA : ℝ × ℝ → V →L[ℝ] ℝ := fun w ↦ (η w).comp (J w (u w))
  set S := ω.floerLinearizationCoeff J Ks Kt u
  have hηA (z : ℝ × ℝ) (hz : z ∈ tsupport ξ) : ContDiffAt ℝ 1 ηA z :=
    (hη z hz).clm_comp ((hJ z hz).comp z (contDiffAt_id.prodMk (hu z hz)) :)
  -- Every integrand below is continuous on the compact support of `ξ` and vanishes off it.
  have hξ0 (z : ℝ × ℝ) (hz : z ∉ tsupport ξ) : ξ z = 0 := image_eq_zero_of_notMem_tsupport hz
  have hint (F : ℝ × ℝ → ℝ) (hF : ∀ z ∈ tsupport ξ, ContinuousAt F z)
      (h0 : ∀ z ∉ tsupport ξ, F z = 0) : Integrable F μ :=
    (ContinuousOn.integrableOn_compact hξc fun z hz ↦
      (hF z hz).continuousWithinAt).integrable_of_forall_notMem_eq_zero h0
  have hdF (F : ℝ × ℝ → V →L[ℝ] ℝ) (hF : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 F z) (v : ℝ × ℝ) :
      Integrable (fun w ↦ fderiv ℝ F w v (ξ w)) μ :=
    hint _ (fun z hz ↦ (((hF z hz).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).clm_apply hξ.continuous.continuousAt) fun z hz ↦ by simp [hξ0 z hz]
  have hFdξ (F : ℝ × ℝ → V →L[ℝ] ℝ) (hF : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 F z) (v : ℝ × ℝ) :
      Integrable (fun w ↦ F w (fderiv ℝ ξ w v)) μ :=
    hint _ (fun z hz ↦ (hF z hz).continuousAt.clm_apply
      (((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt))
      fun z hz ↦ by simp [fderiv_of_notMem_tsupport ℝ hz]
  have hSξ : Integrable (fun w ↦ η w (S w (ξ w))) μ :=
    hint _ (fun z hz ↦ (hη z hz).continuousAt.clm_apply
      ((ω.continuousAt_floerLinearizationCoeff (hJ z hz) (hKs z hz) (hKt z hz)
        (hu z hz)).clm_apply hξ.continuous.continuousAt)) fun z hz ↦ by simp [hξ0 z hz]
  -- Integrate the two derivative terms by parts, against `η` and against `η ∘ A`.
  have hibp (F : ℝ × ℝ → V →L[ℝ] ℝ) (hF : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 F z) (v : ℝ × ℝ) :
      ∫ w, F w (fderiv ℝ ξ w v) ∂μ = -∫ w, fderiv ℝ F w v (ξ w) ∂μ :=
    integral_bilinear_fderiv_right_eq_neg_left_of_hasCompactSupport
      (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)) hF hξ hξc v
  have hlhs : (fun w ↦ η w (ω.floerLinearization J Ks Kt u ξ w)) =
      fun w ↦ η w (fderiv ℝ ξ w stdComplexLineReal) + ηA w (fderiv ℝ ξ w stdComplexLineImag) +
        η w (S w (ξ w)) :=
    funext fun w ↦ by simp only [floerLinearization_eq_add, map_add, ηA, S, comp_apply]
  have hrhs : (fun w ↦ ω.floerLinearizationAdjoint J Ks Kt u η w (ξ w)) =
      fun w ↦ -fderiv ℝ η w stdComplexLineReal (ξ w) - fderiv ℝ ηA w stdComplexLineImag (ξ w) +
        η w (S w (ξ w)) :=
    funext fun w ↦ by
      simp only [floerLinearizationAdjoint_def, add_apply, sub_apply, neg_apply, comp_apply, ηA, S]
  -- Split both integrals into their three terms. The integrands are stated as functions so that
  -- the integrals rewrite under binders.
  have ha' : Integrable (fun w ↦ -fderiv ℝ η w stdComplexLineReal (ξ w)) μ :=
    (hdF η hη stdComplexLineReal).neg
  have hab : Integrable (fun w ↦ η w (fderiv ℝ ξ w stdComplexLineReal) +
      ηA w (fderiv ℝ ξ w stdComplexLineImag)) μ := (hFdξ η hη _).add (hFdξ ηA hηA _)
  have hab' : Integrable (fun w ↦ -fderiv ℝ η w stdComplexLineReal (ξ w) -
      fderiv ℝ ηA w stdComplexLineImag (ξ w)) μ := ha'.sub (hdF ηA hηA _)
  rw [hlhs, hrhs, integral_add hab hSξ, integral_add (hFdξ η hη _) (hFdξ ηA hηA _), hibp η hη,
    hibp ηA hηA, integral_add hab' hSξ, integral_sub ha' (hdF ηA hηA _), integral_neg]
  abel

/-- A covector field that solves the adjoint equation on the support of a `C¹` section `ξ` of
compact support annihilates `D_u ξ`, under the regularity hypotheses of integration by parts. -/
theorem integral_apply_floerLinearization_eq_zero
    (hJ : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 η z)
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ)
    (h : ∀ z ∈ tsupport ξ, ω.floerLinearizationAdjoint J Ks Kt u η z = 0) :
    ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) ∂μ = 0 := by
  rw [integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply hJ hKs hKt hu
    hη hξ hξc]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  by_cases hz : z ∈ tsupport ξ
  · simp [h z hz]
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-- **Cokernel elements solve the adjoint equation.** Let `U` be an open set of the domain on which
`J` is `C¹` and the Hamiltonians are `C²` at the points `(z, u z)`, and `u` and the covector field
`η` are `C¹`. If `∫ η(D_u ξ) = 0` for every smooth section `ξ` compactly supported in `U`, then
`D_u^* η = 0` on `U`. -/
theorem floerLinearizationAdjoint_eq_zero_of_forall_integral_eq_zero {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ U, ContDiffAt ℝ 1 η z)
    (h : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) ∂μ = 0) :
    ∀ z ∈ U, ω.floerLinearizationAdjoint J Ks Kt u η z = 0 := by
  intro z hz
  ext v
  -- Test the scalar field `w ↦ (D_u^* η)(w) v` against `g` through the section `g • v`.
  set f : ℝ × ℝ → ℝ := fun w ↦ ω.floerLinearizationAdjoint J Ks Kt u η w v
  have hf : ContinuousOn f U :=
    (continuousOn_floerLinearizationAdjoint hJ hKs hKt hu hη).clm_apply continuousOn_const
  have htest (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
      (hgU : tsupport g ⊆ U) : ∫ w, g w • f w ∂μ = 0 := by
    have hξU : tsupport (g • fun _ : ℝ × ℝ ↦ v) ⊆ U :=
      (tsupport_smul_subset_left g _).trans hgU
    have hξ : ContDiff ℝ (⊤ : ℕ∞) (g • fun _ : ℝ × ℝ ↦ v) := hg.smul contDiff_const
    rw [← h _ hξ hgc.smul_right hξU,
      integral_apply_floerLinearization_eq_integral_floerLinearizationAdjoint_apply
        (fun z hz ↦ hJ z (hξU hz)) (fun z hz ↦ hKs z (hξU hz)) (fun z hz ↦ hKt z (hξU hz))
        (fun z hz ↦ hu z (hξU hz)) (fun z hz ↦ hη z (hξU hz)) (hξ.of_le (by simp))
        hgc.smul_right]
    simp only [f, Pi.smul_apply', map_smul]
  have hae : f =ᵐ[μ.restrict U] 0 :=
    (ae_restrict_iff' hU.measurableSet).2 <|
      hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn hU.measurableSet)
        htest
  exact Measure.eqOn_open_of_ae_eq hae hU hf continuousOn_const hz

/-- **The cokernel of the linearized Floer operator in `C¹` covector fields.** On an open set `U`
of the domain on which `J` is `C¹` and the Hamiltonians are `C²` at the points `(z, u z)`, and `u`
and the covector field `η` are `C¹`, `η` annihilates `D_u ξ` for every smooth section `ξ`
compactly supported in `U` exactly when it solves the adjoint equation `D_u^* η = 0` on `U`. -/
theorem forall_integral_apply_floerLinearization_eq_zero_iff {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ U, ContDiffAt ℝ 1 η z) :
    (∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
      ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) ∂μ = 0) ↔
      ∀ z ∈ U, ω.floerLinearizationAdjoint J Ks Kt u η z = 0 :=
  ⟨floerLinearizationAdjoint_eq_zero_of_forall_integral_eq_zero hU hJ hKs hKt hu hη,
    fun h ξ hξ hξc hξU ↦ integral_apply_floerLinearization_eq_zero (fun z hz ↦ hJ z (hξU hz))
      (fun z hz ↦ hKs z (hξU hz)) (fun z hz ↦ hKt z (hξU hz)) (fun z hz ↦ hu z (hξU hz))
      (fun z hz ↦ hη z (hξU hz)) (hξ.of_le (by simp)) hξc fun z hz ↦ h z (hξU hz)⟩

end TauCeti.SymplecticForm
