/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic

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

* `TauCeti.SymplecticForm.floerLinearizationTranspose_eq_add`: the splitting of `D_uᵗ η` into the
  first-order part `-∂s η - (∂t η) ∘ J(z, u z)` and a zeroth-order term in `η z`.
* `TauCeti.SymplecticForm.floerLinearizationTranspose_smul_fst` and
  `TauCeti.SymplecticForm.floerLinearizationTranspose_exp_smul`: cutoffs and exponential weights
  in `s` commute with `D_uᵗ` up to a zeroth-order term.
* `TauCeti.SymplecticForm.apply_floerLinearization_eq`: the pointwise Green formula
  `η (D_u ξ) = (D_uᵗ η) ξ + ∂s (η ξ) + ∂t ((η ∘ J) ξ)` at any point where `η`, `η ∘ J` and `ξ`
  are differentiable.
* `TauCeti.SymplecticForm.integral_apply_floerLinearization_eq`: `∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`
  over the plane, when the common support of `η` and `ξ` is compact and `η`, `ξ` and the data are
  regular only there.
* `TauCeti.SymplecticForm.setIntegral_apply_floerLinearization_eq`: the same identity over a
  closed rectangle, with regularity only on the rectangle, when `η ξ` matches on the two vertical
  sides and `(η ∘ J) ξ` on the two horizontal sides. This covers the fundamental domain
  `[a, b] × [0, 1]` of the cylinder for `t`-periodic data.
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

/-- The formal transpose is the first-order part `-∂s η - (∂t η) ∘ J(z, u z)` plus the
zeroth-order term `η z ∘ (A(z) - ∂t (J(·, u ·)))`, when `η` and `J(·, u ·)` are differentiable at
the domain point. -/
theorem floerLinearizationTranspose_eq_add (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z)
    (hJ : DifferentiableAt ℝ (fun w ↦ J w (u w)) z) :
    ω.floerLinearizationTranspose J Ks Kt u η z =
      -fderiv ℝ η z stdComplexLineReal - (fderiv ℝ η z stdComplexLineImag).comp (J z (u z)) +
        (η z).comp (ω.floerLinearizationCoeff J Ks Kt u z -
          fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag) := by
  rw [floerLinearizationTranspose_def, fderiv_clm_comp hη hJ]
  simp only [add_apply, coe_comp, Function.comp_apply, compL_apply, flip_apply, comp_sub]
  abel

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

/-- The transpose commutes with negation of covector fields. -/
@[simp]
theorem floerLinearizationTranspose_neg (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    (η : ℝ × ℝ → V →L[ℝ] ℝ) (z : ℝ × ℝ) :
    ω.floerLinearizationTranspose J Ks Kt u (-η) z =
      -ω.floerLinearizationTranspose J Ks Kt u η z := by
  rw [← neg_one_smul ℝ η, floerLinearizationTranspose_smul]
  exact neg_one_smul ℝ (ω.floerLinearizationTranspose J Ks Kt u η z)

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

/-- The transpose is subtractive on covector fields `η`, `θ` such that `η`, `θ`, `η ∘ J(·, u ·)`
and `θ ∘ J(·, u ·)` are differentiable at the domain point. -/
@[simp]
theorem floerLinearizationTranspose_sub (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η θ : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hη : DifferentiableAt ℝ η z)
    (hθ : DifferentiableAt ℝ θ z)
    (hηJ : DifferentiableAt ℝ (fun w ↦ (η w).comp (J w (u w))) z)
    (hθJ : DifferentiableAt ℝ (fun w ↦ (θ w).comp (J w (u w))) z) :
    ω.floerLinearizationTranspose J Ks Kt u (η - θ) z =
      ω.floerLinearizationTranspose J Ks Kt u η z -
        ω.floerLinearizationTranspose J Ks Kt u θ z := by
  have h : (fun w ↦ ((η - θ) w).comp (J w (u w))) =
      (fun w ↦ (η w).comp (J w (u w))) - fun w ↦ (θ w).comp (J w (u w)) := by
    ext w v
    simp
  rw [floerLinearizationTranspose_def, floerLinearizationTranspose_def,
    floerLinearizationTranspose_def, h, fderiv_sub hη hθ, fderiv_sub hηJ hθJ]
  simp only [Pi.sub_apply, sub_apply, sub_comp]
  abel

/-- **Multiplying by a cutoff in `s`.** If `β` has derivative `β'` at `s`, the transpose at
`z = (s, t)` sends `β(s) η` to `β(s) D_uᵗ η - β' η`: the factor only differentiates in the `s`
direction, where the transpose has the leading term `-∂s`. -/
theorem floerLinearizationTranspose_smul_fst (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} {β : ℝ → ℝ} {β' : ℝ} (hβ : HasDerivAt β β' z.1)
    (hη : DifferentiableAt ℝ η z)
    (hηJ : DifferentiableAt ℝ (fun w ↦ (η w).comp (J w (u w))) z) :
    ω.floerLinearizationTranspose J Ks Kt u (fun w ↦ β w.1 • η w) z =
      β z.1 • ω.floerLinearizationTranspose J Ks Kt u η z - β' • η z := by
  have hb : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1) _ z := hβ.hasFDerivAt.comp z hasFDerivAt_fst
  have h : (fun w ↦ (β w.1 • η w).comp (J w (u w))) =
      fun w ↦ β w.1 • (η w).comp (J w (u w)) := by
    ext w v
    simp
  have hd : HasFDerivAt (fun w ↦ β w.1 • η w) _ z := hb.smul hη.hasFDerivAt
  have hdJ : HasFDerivAt (fun w ↦ β w.1 • (η w).comp (J w (u w))) _ z := hb.smul hηJ.hasFDerivAt
  rw [floerLinearizationTranspose_def, h, hd.fderiv, hdJ.fderiv, floerLinearizationTranspose_def]
  simp only [add_apply, smul_apply, smulRight_apply, ContinuousLinearMap.comp_apply, coe_fst',
    stdComplexLineReal_fst, toSpanSingleton_apply, smul_eq_mul, one_mul, neg_add_rev,
    stdComplexLineImag_fst, zero_mul, zero_smul, add_zero, smul_comp, smul_add]
  module

/-- **Conjugating the transpose by an exponential weight.** On covector fields of the form
`e^{-δ s} η`, the transpose acts as `e^{-δ s} (D_uᵗ + δ) η`: the weight only differentiates in the
`s` direction, where the transpose has the leading term `-∂s`. -/
theorem floerLinearizationTranspose_exp_smul (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (δ : ℝ) (hη : DifferentiableAt ℝ η z)
    (hηJ : DifferentiableAt ℝ (fun w ↦ (η w).comp (J w (u w))) z) :
    ω.floerLinearizationTranspose J Ks Kt u (fun w ↦ Real.exp (-(δ * w.1)) • η w) z =
      Real.exp (-(δ * z.1)) • (ω.floerLinearizationTranspose J Ks Kt u η z + δ • η z) := by
  have hβ : HasDerivAt (fun s ↦ Real.exp (-(δ * s))) (Real.exp (-(δ * z.1)) * -δ) z.1 := by
    simpa using ((hasDerivAt_id z.1).const_mul δ).neg.exp
  rw [ω.floerLinearizationTranspose_smul_fst J Ks Kt u hβ hη hηJ]
  module

/-- The transpose at `z` depends only on the germ of the covector field at `z`. -/
theorem floerLinearizationTranspose_congr_of_eventuallyEq (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η θ : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (h : η =ᶠ[𝓝 z] θ) :
    ω.floerLinearizationTranspose J Ks Kt u η z = ω.floerLinearizationTranspose J Ks Kt u θ z := by
  have hJ : (fun w ↦ (η w).comp (J w (u w))) =ᶠ[𝓝 z] fun w ↦ (θ w).comp (J w (u w)) :=
    h.mono fun w hw ↦ by simp only [hw]
  rw [floerLinearizationTranspose_def, floerLinearizationTranspose_def, h.fderiv_eq, hJ.fderiv_eq,
    h.eq_of_nhds]

/-- The transpose vanishes off the topological support of the covector field. -/
theorem floerLinearizationTranspose_of_notMem_tsupport (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {z : ℝ × ℝ} (hz : z ∉ tsupport η) :
    ω.floerLinearizationTranspose J Ks Kt u η z = 0 := by
  rw [ω.floerLinearizationTranspose_congr_of_eventuallyEq J Ks Kt u
    (notMem_tsupport_iff_eventuallyEq.1 hz), floerLinearizationTranspose_zero]

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

/-- **Global continuity of the transpose.** Let `u` and `η` be `C¹`, and let `J` be `C¹` and the
Hamiltonians `K_s`, `K_t` be `C²` at every point `(z, u z)`. Then the transpose of the linearized
Floer operator along `u` is continuous on `η`. -/
theorem continuous_floerLinearizationTranspose (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ}
    (hJ : ∀ z, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hη : ContDiff ℝ 1 η) : Continuous (ω.floerLinearizationTranspose J Ks Kt u η) :=
  continuous_iff_continuousAt.2 fun z ↦
    ω.continuousAt_floerLinearizationTranspose (hJ z) (hKs z) (hKt z) hu.contDiffAt hη.contDiffAt

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

/-- Off the common topological support of `η` and `ξ`, every term of the integrand
`η (D_u ξ)` and of the Green formula `apply_floerLinearization_eq` vanishes near the point. -/
private theorem eventually_notMem_tsupport_inter (ω : SymplecticForm V)
    (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V} {z : ℝ × ℝ} (hz : z ∉ tsupport η ∩ tsupport ξ) :
    ∀ᶠ w in 𝓝 z, η w (ω.floerLinearization J Ks Kt u ξ w) = 0 ∧
      ω.floerLinearizationTranspose J Ks Kt u η w (ξ w) = 0 ∧ η w (ξ w) = 0 ∧
        (η w).comp (J w (u w)) (ξ w) = 0 := by
  filter_upwards [((isClosed_tsupport η).inter (isClosed_tsupport ξ)).isOpen_compl.mem_nhds hz]
    with w hw
  rcases not_and_or.1 hw with h | h
  · simp [ω.floerLinearizationTranspose_of_notMem_tsupport J Ks Kt u h,
      image_eq_zero_of_notMem_tsupport h]
  · rw [ω.floerLinearization_congr_of_eventuallyEq J Ks Kt u
      (notMem_tsupport_iff_eventuallyEq.1 h)]
    simp [image_eq_zero_of_notMem_tsupport h]

/-- **Integration by parts for the linearized Floer operator.** Let the common topological
support of the covector field `η` and the section `ξ` be compact, and on it let `u`, `η` and `ξ` be
`C¹`, `J` be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²`, jointly in the domain and target point.
Then

`∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`

over the plane, for the formal transpose `D_uᵗ = floerLinearizationTranspose`. -/
theorem integral_apply_floerLinearization_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V}
    (hJ : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 u z)
    (hη : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 η z)
    (hξ : ∀ z ∈ tsupport η ∩ tsupport ξ, ContDiffAt ℝ 1 ξ z)
    (hc : IsCompact (tsupport η ∩ tsupport ξ)) :
    ∫ z, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z, ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) := by
  set K := tsupport η ∩ tsupport ξ
  have hK : IsClosed K := (isClosed_tsupport η).inter (isClosed_tsupport ξ)
  have hev {z : ℝ × ℝ} (hz : z ∉ K) := ω.eventually_notMem_tsupport_inter J Ks Kt u hz
  have hηJ (z : ℝ × ℝ) (hz : z ∈ K) : ContDiffAt ℝ 1 (fun w ↦ (η w).comp (J w (u w))) z :=
    (hη z hz).clm_comp ((hJ z hz).comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk (hu z hz)))
  -- The two divergence terms of the Green formula are derivatives of compactly supported `C¹`
  -- functions, so they integrate to zero.
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF : ContDiff ℝ 1 F := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ K
    · exact (hη z hz).clm_apply (hξ z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq ((hev hz).mono fun _ hw ↦ hw.2.2.1)
  have hG : ContDiff ℝ 1 G := contDiff_iff_contDiffAt.2 fun z ↦ by
    by_cases hz : z ∈ K
    · exact (hηJ z hz).clm_apply (hξ z hz)
    · exact contDiffAt_const.congr_of_eventuallyEq ((hev hz).mono fun _ hw ↦ hw.2.2.2)
  have hFc : HasCompactSupport F :=
    .intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.2.1
  have hGc : HasCompactSupport G :=
    .intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.2.2
  -- The term `(D_uᵗ η) ξ` is continuous with compact support.
  have hT : Integrable fun z ↦ ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) := by
    refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.2 fun z ↦ ?_)
      (.intro' hc hK fun _ hz ↦ (hev hz).self_of_nhds.2.1)
    by_cases hz : z ∈ K
    · exact (ω.continuousAt_floerLinearizationTranspose (hJ z hz) (hKs z hz) (hKt z hz) (hu z hz)
        (hη z hz)).clm_apply (hξ z hz).continuousAt
    · exact continuousAt_const.congr ((hev hz).mono fun _ hw ↦ hw.2.1.symm)
  -- The Green formula holds at every point.
  have hpt (z : ℝ × ℝ) : η z (ω.floerLinearization J Ks Kt u ξ z) =
      ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) + fderiv ℝ F z stdComplexLineReal +
        fderiv ℝ G z stdComplexLineImag := by
    by_cases hz : z ∈ K
    · exact ω.apply_floerLinearization_eq J Ks Kt u ((hη z hz).differentiableAt one_ne_zero)
        ((hηJ z hz).differentiableAt one_ne_zero) ((hξ z hz).differentiableAt one_ne_zero)
    · have hF0 : F =ᶠ[𝓝 z] fun _ ↦ 0 := (hev hz).mono fun _ hw ↦ hw.2.2.1
      have hG0 : G =ᶠ[𝓝 z] fun _ ↦ 0 := (hev hz).mono fun _ hw ↦ hw.2.2.2
      rw [(hev hz).self_of_nhds.1, (hev hz).self_of_nhds.2.1, hF0.fderiv_eq, hG0.fderiv_eq]
      simp
  simp_rw [hpt]
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hdF : Integrable fun z ↦ fderiv ℝ F z stdComplexLineReal :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hF hFc _
  have hdG : Integrable fun z ↦ fderiv ℝ G z stdComplexLineImag :=
    integrable_fderiv_apply_of_hasCompactSupport (μ := volume) hG hGc _
  rw [integral_add (hT.fun_add hdF) hdG, integral_add hT hdF,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hF hFc,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport (μ := volume) hG hGc, add_zero, add_zero]

/-- **Integration by parts for the linearized Floer operator on a rectangle.** On the closed
rectangle `R = [a₁, b₁] × [a₂, b₂]` let `u`, the covector field `η` and the section `ξ` be `C¹`, `J`
be `C¹` and the Hamiltonians `K_s`, `K_t` be `C²` along the graph of `u`. If the pairing `η ξ` takes
equal values on the vertical sides `s = a₁` and `s = b₁`, and `(η ∘ J) ξ` takes equal values on the
horizontal sides `t = a₂` and `t = b₂`, then

`∫ η (D_u ξ) = ∫ (D_uᵗ η) ξ`

over `R`. On the fundamental domain `[a, b] × [0, 1]` of the cylinder `ℝ × S¹`, both side
conditions hold when `ξ` vanishes at `s = a, b` and `η`, `ξ` and `J(·, u ·)` have period one
in `t`. -/
theorem setIntegral_apply_floerLinearization_eq (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}
    {η : ℝ × ℝ → V →L[ℝ] ℝ} {ξ : ℝ × ℝ → V} {a₁ b₁ a₂ b₂ : ℝ}
    (hJ : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 (uncurry J) (z, u z))
    (hKs : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 2 (uncurry Kt) (z, u z))
    (hu : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 u z)
    (hη : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 η z)
    (hξ : ∀ z ∈ Icc a₁ b₁ ×ˢ Icc a₂ b₂, ContDiffAt ℝ 1 ξ z)
    (hvert : ∀ t ∈ Icc a₂ b₂, η (b₁, t) (ξ (b₁, t)) = η (a₁, t) (ξ (a₁, t)))
    (hhor : ∀ s ∈ Icc a₁ b₁, η (s, b₂) (J (s, b₂) (u (s, b₂)) (ξ (s, b₂))) =
      η (s, a₂) (J (s, a₂) (u (s, a₂)) (ξ (s, a₂)))) :
    ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, η z (ω.floerLinearization J Ks Kt u ξ z) =
      ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) := by
  rcases lt_or_ge b₁ a₁ with h₁ | h₁
  · simp [Icc_eq_empty_of_lt h₁]
  rcases lt_or_ge b₂ a₂ with h₂ | h₂
  · simp [Icc_eq_empty_of_lt h₂]
  set R := Icc a₁ b₁ ×ˢ Icc a₂ b₂
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hηJ (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 (fun w ↦ (η w).comp (J w (u w))) z :=
    (hη z hz).clm_comp ((hJ z hz).comp (f := fun w ↦ (w, u w)) z (contDiffAt_id.prodMk (hu z hz)))
  set F : ℝ × ℝ → ℝ := fun w ↦ η w (ξ w)
  set G : ℝ × ℝ → ℝ := fun w ↦ (η w).comp (J w (u w)) (ξ w)
  have hF (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 F z := (hη z hz).clm_apply (hξ z hz)
  have hG (z : ℝ × ℝ) (hz : z ∈ R) : ContDiffAt ℝ 1 G z := (hηJ z hz).clm_apply (hξ z hz)
  have hT : ContinuousOn (fun z ↦ ω.floerLinearizationTranspose J Ks Kt u η z (ξ z)) R :=
    fun z hz ↦ ((ω.continuousAt_floerLinearizationTranspose (hJ z hz) (hKs z hz) (hKt z hz)
      (hu z hz) (hη z hz)).clm_apply (hξ z hz).continuousAt).continuousWithinAt
  have hdiv : ContinuousOn
      (fun z ↦ fderiv ℝ F z stdComplexLineReal + fderiv ℝ G z stdComplexLineImag) R :=
    fun z hz ↦ ((((hF z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).add
      (((hG z hz).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const)).continuousWithinAt
  -- By the divergence theorem, the divergence terms integrate to the differences of the values on
  -- opposite sides, which vanish.
  have hint :
      ∫ z in R, (fderiv ℝ F z stdComplexLineReal + fderiv ℝ G z stdComplexLineImag) = 0 := by
    have hRI : R = Icc (a₁, a₂) (b₁, b₂) := Icc_prod_Icc a₁ b₁ a₂ b₂
    have hsub : Ioo a₁ b₁ ×ˢ Ioo a₂ b₂ ⊆ R := prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
    rw [hRI] at hR hdiv ⊢
    rw [stdComplexLineReal_eq, stdComplexLineImag_eq,
      integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G (fderiv ℝ F) (fderiv ℝ G) _ _ ⟨h₁, h₂⟩
        (fun z hz ↦ (hF z (hRI ▸ hz)).continuousAt.continuousWithinAt)
        (fun z hz ↦ (hG z (hRI ▸ hz)).continuousAt.continuousWithinAt)
        (fun z hz ↦ ((hF z (hsub hz)).differentiableAt one_ne_zero).hasFDerivAt)
        (fun z hz ↦ ((hG z (hsub hz)).differentiableAt one_ne_zero).hasFDerivAt)
        (hdiv.integrableOn_compact hR)]
    dsimp only
    rw [intervalIntegral.integral_congr (f := fun s ↦ G (s, b₂)) (g := fun s ↦ G (s, a₂))
        fun s hs ↦ hhor s (uIcc_of_le h₁ ▸ hs),
      intervalIntegral.integral_congr (f := fun t ↦ F (b₁, t)) (g := fun t ↦ F (a₁, t))
        fun t ht ↦ hvert t (uIcc_of_le h₂ ▸ ht)]
    simp
  rw [setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦
      (ω.apply_floerLinearization_eq J Ks Kt u ((hη z hz).differentiableAt one_ne_zero)
        ((hηJ z hz).differentiableAt one_ne_zero) ((hξ z hz).differentiableAt one_ne_zero)).trans
      (add_assoc _ _ _),
    integral_add (hT.integrableOn_compact hR) (hdiv.integrableOn_compact hR), hint, add_zero]

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
    ω.integral_apply_floerLinearization_eq (fun z hz ↦ hJ z (hξU hz.2))
      (fun z hz ↦ hKs z (hξU hz.2)) (fun z hz ↦ hKt z (hξU hz.2)) (fun z hz ↦ hu z (hξU hz.2))
      (fun z hz ↦ hη z (hξU hz.2)) (fun _ _ ↦ (hξ.of_le (by norm_num)).contDiffAt)
      (hξc.isCompact.inter_left (isClosed_tsupport η))
  constructor
  · -- Test against compactly supported Schwartz sections supported in `U`.
    intro h
    refine hU.eqOn_of_integral_clm_apply_eq (μ := volume) (fun w hw ↦
      (ω.continuousAt_floerLinearizationTranspose (hJ w hw) (hKs w hw) (hKt w hw) (hu w hw)
        (hη w hw)).continuousWithinAt) continuousOn_const fun ξ hξc hξU ↦ ?_
    rw [← hint (ξ.smooth ⊤) hξc hξU, h ξ (ξ.smooth ⊤) hξc hξU]
    simp
  · intro h ξ hξ hξc hξU
    rw [hint hξ hξc hξU]
    have h0 (z : ℝ × ℝ) : ω.floerLinearizationTranspose J Ks Kt u η z (ξ z) = 0 := by
      by_cases hz : z ∈ tsupport ξ
      · simp [h (hξU hz)]
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp [h0]

end TauCeti.SymplecticForm
