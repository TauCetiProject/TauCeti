/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Group.Measure
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.IsOpen
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The formal transpose of the linearized Floer operator

Let `(V, ω)` be a finite-dimensional symplectic vector space and let

`D_u ξ = ∂s ξ + J(z, u z) ∂t ξ + A(z) ξ`

be the linearized Floer operator along a map `u : ℝ × ℝ → V`
(`TauCeti.SymplecticForm.floerLinearization`), with zeroth-order part
`A = TauCeti.SymplecticForm.floerLinearizationCoeff`. The cokernel of `D_u` is described by
covector fields `η : ℝ × ℝ → V →L[ℝ] ℝ` that annihilate its range in the pairing
`∫ η(z) (D_u ξ (z))`. Integrating by parts moves `D_u` onto `η`: the **formal transpose**

`D_uᵗ η = -∂s η - ∂t (η ∘ J(·, u ·)) + η ∘ A`

(`TauCeti.SymplecticForm.floerLinearizationTranspose`) satisfies `∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`.
It is a first-order operator on covector fields. No metric, no compatibility of `J` with `ω` and no
nondegeneracy enter: the pairing of covectors with vectors is the only structure used.

## Main results

* `TauCeti.SymplecticForm.apply_floerLinearization_eq`: the pointwise Green formula
  `η (D_u ξ) = (D_uᵗ η) ξ + ∂s (η ξ) + ∂t ((η ∘ J) ξ)` at any point where `η`, `η ∘ J` and `ξ`
  are differentiable, and at every point off the support of `ξ`
  (`TauCeti.SymplecticForm.apply_floerLinearization_eq_of_notMem_tsupport`).
* `TauCeti.SymplecticForm.integral_apply_floerLinearization_eq`: for a compactly supported `C¹`
  section `ξ`, `∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ` over the plane, with `η` and the data regular only
  on the support of `ξ`.
* `TauCeti.SymplecticForm.setIntegral_apply_floerLinearization_eq`: the same identity over the
  fundamental domain `[a, b] × [0, 1]` of the cylinder, for sections `ξ` of period one in `t`
  vanishing for `s ∉ (a, b)`, and `η`, `J(·, u ·)` of period one in `t`.
* `TauCeti.SymplecticForm.forall_integral_apply_floerLinearization_eq_zero_iff`: on an open set
  `U`, a `C¹` covector field annihilates `D_u ξ` for every smooth section `ξ` compactly supported
  in `U` exactly when `D_uᵗ η` vanishes on `U`. This is the weak form of the cokernel of `D_u`,
  turned into the equation `D_uᵗ η = 0`.

The last statement is how the cokernel of `D_u` enters both the Fredholm theory of `D_u`, where
it is the kernel of `D_uᵗ`, and transversality, where a covector field annihilating the range of
`D_u` and all variations of the data must vanish. `TauCeti.crFormalAdjoint` is the related
Hilbert adjoint of a real Cauchy–Riemann operator on `ℂ` with rough coefficients and an inner
product on the target; here the target carries no inner product, the coefficients are those of the
Floer operator on the coordinate plane `ℝ × ℝ`, and `D_uᵗ` acts on covector fields.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Sections 3.1
  and 3.2, on the formal adjoint of the linearized operator and cokernel elements.
* A. Floer, H. Hofer and D. Salamon, *Transversality in elliptic Morse theory for the symplectic
  action*, Duke Math. J. 80 (1995), 251–292, on cokernel elements of the linearized Floer operator
  as solutions of the adjoint equation.
-/

public section

open Function Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The formal transpose of the linearized Floer operator**, acting on covector fields:
`D_uᵗ η = -∂s η - ∂t (η ∘ J(·, u ·)) + η ∘ A`, where `A` is the zeroth-order part
`floerLinearizationCoeff` of `D_u`. It satisfies `∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ` for compactly
supported sections `ξ` (`integral_apply_floerLinearization_eq`). -/
noncomputable def floerLinearizationTranspose (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) : V →L[ℝ] ℝ :=
  -fderiv ℝ η z stdComplexLineReal -
      fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
    (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z)

/-- The coordinate expression of the formal transpose. -/
theorem floerLinearizationTranspose_def (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) :
    ω.floerLinearizationTranspose J Ks Kt u η z =
      -fderiv ℝ η z stdComplexLineReal -
          fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) z stdComplexLineImag +
        (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z) :=
  (rfl)

/-- The transpose sends the zero covector field to zero. -/
@[simp]
theorem floerLinearizationTranspose_zero (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerLinearizationTranspose J Ks Kt u 0 z = 0 := by
  simp [floerLinearizationTranspose_def]

/-- The transpose respects real scaling of covector fields. -/
@[simp]
theorem floerLinearizationTranspose_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) (c : ℝ) :
    ω.floerLinearizationTranspose J Ks Kt u (c • η) z =
      c • ω.floerLinearizationTranspose J Ks Kt u η z := by
  have h : (fun w ↦ ((c • η) w).comp (J w (u w))) = c • fun w ↦ (η w).comp (J w (u w)) := by
    ext w v
    simp
  -- `fderiv_const_smul_field` does not unify with the scalar action on covector fields by `rw`.
  have hη := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := η) c) z
  have hηJ := congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun w ↦ (η w).comp (J w (u w))) c) z
  rw [floerLinearizationTranspose_def, floerLinearizationTranspose_def, h, hη, hηJ]
  simp only [Pi.smul_apply, smul_apply, smul_comp]
  module

/-- The transpose is additive on covector fields `η`, `θ` such that `η`, `θ`, `η ∘ J(·, u ·)` and
`θ ∘ J(·, u ·)` are differentiable at the domain point. -/
@[simp]
theorem floerLinearizationTranspose_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η θ : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z)
    (hθ : DifferentiableAt ℝ θ z)
    (hηJ : DifferentiableAt ℝ (fun w ↦ (η w).comp (J w (u w))) z)
    (hθJ : DifferentiableAt ℝ (fun w ↦ (θ w).comp (J w (u w))) z) :
    ω.floerLinearizationTranspose J Ks Kt u (η + θ) z =
      ω.floerLinearizationTranspose J Ks Kt u η z +
        ω.floerLinearizationTranspose J Ks Kt u θ z := by
  have h : (fun w ↦ ((η + θ) w).comp (J w (u w))) =
      (fun w ↦ (η w).comp (J w (u w))) + fun w ↦ (θ w).comp (J w (u w)) := by
    ext w v
    simp
  rw [floerLinearizationTranspose_def, floerLinearizationTranspose_def,
    floerLinearizationTranspose_def, h, fderiv_add hη hθ, fderiv_add hηJ hθJ]
  simp only [Pi.add_apply, add_apply, add_comp]
  abel

/-- The transpose at `z` depends only on the germ of the covector field at `z`. -/
theorem floerLinearizationTranspose_congr_of_eventuallyEq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η θ : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (h : η =ᶠ[𝓝 z] θ) :
    ω.floerLinearizationTranspose J Ks Kt u η z = ω.floerLinearizationTranspose J Ks Kt u θ z := by
  have hJ : (fun w ↦ (η w).comp (J w (u w))) =ᶠ[𝓝 z] fun w ↦ (θ w).comp (J w (u w)) :=
    h.mono fun w hw ↦ by simp only [hw]
  rw [floerLinearizationTranspose_def, floerLinearizationTranspose_def, h.fderiv_eq, hJ.fderiv_eq,
    h.eq_of_nhds]

/-- **Continuity of the transpose.** Let `u` and `η` be `C¹` at `z`, and let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` at `(z, u z)`, jointly in the domain and target point. Then the
transpose of the linearized Floer operator along `u` is continuous at `z` on `η`. -/
theorem continuousAt_floerLinearizationTranspose (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ}
    (hJ : ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiffAt ℝ 1 u z)
    (hη : ContDiffAt ℝ 1 η z) :
    ContinuousAt (ω.floerLinearizationTranspose J Ks Kt u η) z := by
  have hηJ := hη.clm_comp (hJ.comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk hu))
  have hdη : ContinuousAt (fun w ↦ fderiv ℝ η w stdComplexLineReal) z :=
    (hη.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hdηJ : ContinuousAt
      (fun w ↦ fderiv ℝ (fun w ↦ (η w).comp (J w (u w))) w stdComplexLineImag) z :=
    (hηJ.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  exact (hdη.neg.sub hdηJ).add
    (hη.continuousAt.clm_comp (ω.continuousAt_floerLinearizationCoeff hJ hKs hKt hu))

/-- **The pointwise Green formula for the linearized Floer operator.** At a point where the
covector field `η`, its composite `η ∘ J(·, u ·)` and the section `ξ` are differentiable,

`η (D_u ξ) = (D_uᵗ η) ξ + ∂s (η ξ) + ∂t ((η ∘ J) ξ)`.

The two derivative terms integrate to zero against compactly supported or periodic sections, which
gives the integral identities `integral_apply_floerLinearization_eq` and
`setIntegral_apply_floerLinearization_eq`. -/
theorem apply_floerLinearization_eq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z)
    (hηJ : DifferentiableAt ℝ (fun w ↦ (η w).comp (J w (u w))) z)
    (hξ : DifferentiableAt ℝ ξ z) :
    η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) +
        fderiv ℝ (fun w ↦ η w (ξ w)) z stdComplexLineReal +
        fderiv ℝ (fun w ↦ (η w).comp (J w (u w)) (ξ w)) z stdComplexLineImag := by
  rw [floerLinearization_eq_add, floerLinearizationTranspose_def, fderiv_clm_apply hη hξ,
    fderiv_clm_apply hηJ hξ]
  simp only [map_add, add_apply, sub_apply, neg_apply, comp_apply, coe_comp, flip_apply]
  ring

/-- **The Green formula off the support of the section.** Outside the topological support of `ξ`
all terms of `apply_floerLinearization_eq` vanish, so the formula holds there with no regularity
assumption on `η`. -/
theorem apply_floerLinearization_eq_of_notMem_tsupport (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} (hz : z ∉ tsupport ξ) :
    η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) +
        fderiv ℝ (fun w ↦ η w (ξ w)) z stdComplexLineReal +
        fderiv ℝ (fun w ↦ (η w).comp (J w (u w)) (ξ w)) z stdComplexLineImag := by
  have hξ := notMem_tsupport_iff_eventuallyEq.1 hz
  have hF : (fun w ↦ η w (ξ w)) =ᶠ[𝓝 z] fun _ ↦ 0 := hξ.mono fun w hw ↦ by simp [hw]
  have hG : (fun w ↦ (η w).comp (J w (u w)) (ξ w)) =ᶠ[𝓝 z] fun _ ↦ 0 :=
    hξ.mono fun w hw ↦ by simp [hw]
  rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u hξ, floerLinearization_zero,
    hF.fderiv_eq, hG.fderiv_eq, hξ.eq_of_nhds]
  simp

/-- **Integration by parts for the linearized Floer operator.** Let `ξ` be a compactly supported
`C¹` section, and on the support of `ξ` let `u` and the covector field `η` be `C¹`, `J` be `C¹`
and the Hamiltonians `K_s`, `K_t` be `C²`, jointly in the domain and target point. Then

`∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`

over the plane, for the formal transpose `D_uᵗ = floerLinearizationTranspose`. -/
theorem integral_apply_floerLinearization_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V}
    (hJ : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ tsupport ξ, ContDiffAt ℝ 1 η z)
    (hξ : ContDiff ℝ 1 ξ) (hξc : HasCompactSupport ξ) :
    ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z, ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) := by
  have hξ0 (z : ℝ × ℝ) (hz : z ∉ tsupport ξ) : ξ z = 0 := image_eq_zero_of_notMem_tsupport hz
  -- A function vanishing off the support of `ξ` has its support there too.
  have hsub {f : ℝ × ℝ → ℝ} (hf : ∀ z ∉ tsupport ξ, f z = 0) : tsupport f ⊆ tsupport ξ :=
    closure_minimal (support_subset_iff'.2 hf) (isClosed_tsupport ξ)
  have hηJ (z : ℝ × ℝ) (hz : z ∈ tsupport ξ) :
      ContDiffAt ℝ 1 (fun w ↦ (η w).comp (J w (u w))) z :=
    (hη z hz).clm_comp ((hJ z hz).comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk (hu z hz)))
  -- The two divergence terms of the Green formula are derivatives of compactly supported `C¹`
  -- functions, so they integrate to zero.
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF0 (z : ℝ × ℝ) (hz : z ∉ tsupport ξ) : F z = 0 := by simp [F, hξ0 z hz]
  have hG0 (z : ℝ × ℝ) (hz : z ∉ tsupport ξ) : G z = 0 := by simp [G, hξ0 z hz]
  have hF : ContDiff ℝ 1 F := by
    obtain ⟨U, hU, hξU, hηU⟩ := exists_isOpen_superset_contDiffOn (by simp) hη
    simpa using (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)).contDiff_of_tsupport_subset_right hηU
      hξ.contDiffOn hU hξU
  have hG : ContDiff ℝ 1 G := by
    obtain ⟨U, hU, hξU, hηU⟩ := exists_isOpen_superset_contDiffOn (by simp) hηJ
    simpa [G] using (ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)).contDiff_of_tsupport_subset_right hηU
      hξ.contDiffOn hU hξU
  have hFc : HasCompactSupport F := HasCompactSupport.intro hξc hF0
  have hGc : HasCompactSupport G := HasCompactSupport.intro hξc hG0
  -- The term `(D_uᵗ η) ξ` is continuous with compact support.
  have hT0 (z : ℝ × ℝ) (hz : z ∉ tsupport ξ) :
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) = 0 := by simp [hξ0 z hz]
  have hT : Integrable fun z ↦ ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) :=
    (continuous_of_tsupport fun z hz ↦
      (ω.continuousAt_floerLinearizationTranspose (hJ z (hsub hT0 hz)) (hKs z (hsub hT0 hz))
        (hKt z (hsub hT0 hz)) (hu z (hsub hT0 hz)) (hη z (hsub hT0 hz))).clm_apply
          hξ.continuous.continuousAt).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hξc hT0)
  -- The Green formula holds at every point.
  have hpt (z : ℝ × ℝ) : η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) + fderiv ℝ F z stdComplexLineReal +
        fderiv ℝ G z stdComplexLineImag := by
    by_cases hz : z ∈ tsupport ξ
    · exact ω.apply_floerLinearization_eq J Ks Kt u ((hη z hz).differentiableAt one_ne_zero)
        ((hηJ z hz).differentiableAt one_ne_zero) (hξ.differentiable one_ne_zero z)
    · exact ω.apply_floerLinearization_eq_of_notMem_tsupport J Ks Kt u η hz
  simp_rw [hpt]
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hdF : Integrable fun z ↦ fderiv ℝ F z stdComplexLineReal :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hF hFc _
  have hdG : Integrable fun z ↦ fderiv ℝ G z stdComplexLineImag :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hG hGc _
  rw [integral_add (hT.fun_add hdF) hdG, integral_add hT hdF,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hF hFc,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hG hGc, add_zero, add_zero]

/-- **Integration by parts for the linearized Floer operator on the cylinder.** Let `u` and the
covector field `η` be `C¹`, `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` along the graph of
`u`, and let `η` and the structures `J(z, u z)` have period one in `t`. Then every `C¹` section `ξ`
of period one in `t` that vanishes for `s ∉ (a, b)` satisfies

`∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`

over the fundamental domain `[a, b] × [0, 1]` of the cylinder `ℝ × S¹`. -/
theorem setIntegral_apply_floerLinearization_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ)
    (hJp : ∀ s t, J (s, t + 1) (u (s, t + 1)) = J (s, t) (u (s, t)))
    (hηp : ∀ s t, η (s, t + 1) = η (s, t)) (hξp : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hξ0 : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) := by
  have hηJ : ContDiff ℝ 1 fun w ↦ (η w).comp (J w (u w)) :=
    hη.clm_comp (contDiff_iff_contDiffAt.2 fun z ↦
      (hJ z).comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk hu.contDiffAt))
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF : ContDiff ℝ 1 F := hη.clm_apply hξ
  have hG : ContDiff ℝ 1 G := hηJ.clm_apply hξ
  have hrect : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hdF : Continuous fun z ↦ fderiv ℝ F z stdComplexLineReal :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdG : Continuous fun z ↦ fderiv ℝ G z stdComplexLineImag :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hT : Continuous fun z ↦ ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) :=
    continuous_iff_continuousAt.2 fun z ↦
      (ω.continuousAt_floerLinearizationTranspose (hJ z) (hKs z) (hKt z) hu.contDiffAt
        hη.contDiffAt).clm_apply hξ.continuous.continuousAt
  -- The divergence terms integrate to zero: `η ξ` vanishes on the sides `s = a`, `s = b`, and
  -- `(η ∘ J) ξ` takes equal values on the sides `t = 0`, `t = 1`.
  have hFint : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, fderiv ℝ F z stdComplexLineReal = 0 :=
    setIntegral_rect_eq_zero_of_hasDerivAt_fst hdF
      (fun s t ↦ hasDerivAt_slice_left (hF.differentiable one_ne_zero (s, t))) fun t ↦ by
      simp [F, hξ0 a t (by simp), hξ0 b t (by simp)]
  have hGint : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, fderiv ℝ G z stdComplexLineImag = 0 :=
    setIntegral_rect_eq_zero_of_hasDerivAt_snd hdG
      (fun s t ↦ hasDerivAt_slice_right (hG.differentiable one_ne_zero (s, t))) fun s ↦ by
      have hJ1 := hJp s 0
      have hη1 := hηp s 0
      have hξ1 := hξp s 0
      rw [zero_add] at hJ1 hη1 hξ1
      simp only [G, hJ1, hη1, hξ1]
  have hpt (z : ℝ × ℝ) : η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) + fderiv ℝ F z stdComplexLineReal +
        fderiv ℝ G z stdComplexLineImag :=
    ω.apply_floerLinearization_eq J Ks Kt u (hη.differentiable one_ne_zero z)
      (hηJ.differentiable one_ne_zero z) (hξ.differentiable one_ne_zero z)
  simp_rw [hpt]
  have hI {f : ℝ × ℝ → ℝ} (hf : Continuous f) : IntegrableOn f (Icc a b ×ˢ Icc (0 : ℝ) 1) :=
    hf.continuousOn.integrableOn_compact hrect
  rw [integral_add (hI (hT.fun_add hdF)) (hI hdG), integral_add (hI hT) (hI hdF), hFint, hGint,
    add_zero, add_zero]

/-- **The weak form of the cokernel of the linearized Floer operator.** Let `U` be open, and on
`U` let `u` and the covector field `η` be `C¹`, `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be
`C²`, jointly in the domain and target point. Then `η` annihilates `D_u ξ`, in the sense that
`∫ η (D_u ξ) = 0`, for every smooth section `ξ` compactly supported in `U` if and only if the
formal transpose `D_uᵗ η` vanishes on `U`. -/
theorem forall_integral_apply_floerLinearization_eq_zero_iff (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) (hη : ∀ z ∈ U, ContDiffAt ℝ 1 η z) :
    (∀ ξ : ℝ × ℝ → V, ContDiff ℝ (⊤ : ℕ∞) ξ → HasCompactSupport ξ → tsupport ξ ⊆ U →
        ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) = 0) ↔
      EqOn (ω.floerLinearizationTranspose J Ks Kt u η) 0 U := by
  have hint {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hξc : HasCompactSupport ξ)
      (hξU : tsupport ξ ⊆ U) : ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) =
        ∫ z, ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) :=
    ω.integral_apply_floerLinearization_eq (fun z hz ↦ hJ z (hξU hz))
      (fun z hz ↦ hKs z (hξU hz)) (fun z hz ↦ hKt z (hξU hz)) (fun z hz ↦ hu z (hξU hz))
      (fun z hz ↦ hη z (hξU hz)) (hξ.of_le (by norm_num)) hξc
  constructor
  · intro h z hz
    ext v
    -- Test against the sections `g • v`: the scalar field `w ↦ (D_uᵗ η)(w) v` is orthogonal to
    -- every smooth function compactly supported in `U`, and it is continuous on `U`.
    set f : ℝ × ℝ → ℝ := fun w ↦ ω.floerLinearizationTranspose J Ks Kt u η w v
    have hf : ContinuousOn f U := fun w hw ↦
      ((ω.continuousAt_floerLinearizationTranspose (hJ w hw) (hKs w hw) (hKt w hw) (hu w hw)
        (hη w hw)).clm_apply continuousAt_const).continuousWithinAt
    have hae : ∀ᵐ w, w ∈ U → f w = 0 :=
      hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn hU.measurableSet)
        fun g hg hgc hgU ↦ by
          have hgv : tsupport (fun w ↦ g w • v) ⊆ U :=
            (tsupport_smul_subset_left g fun _ ↦ v).trans hgU
          have hgs : ContDiff ℝ (⊤ : ℕ∞) fun w ↦ g w • v := hg.smul contDiff_const
          have hgsc : HasCompactSupport fun w ↦ g w • v := hgc.smul_right
          have := h _ hgs hgsc hgv
          rw [hint hgs hgsc hgv] at this
          simpa [f, smul_eq_mul] using this
    have hEq : EqOn f 0 U :=
      Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU hf
        continuousOn_const
    simpa [f] using hEq hz
  · intro h ξ hξ hξc hξU
    rw [hint hξ hξc hξU]
    have h0 (z : ℝ × ℝ) : ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) = 0 := by
      by_cases hz : z ∈ tsupport ξ
      · simp [h (hξU hz)]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp [h0]

end TauCeti.SymplecticForm
