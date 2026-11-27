/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere
public import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Sobolev.Poincare.Slab
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
import TauCeti.Geometry.Symplectic.Floer.Linearization.Infinity
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Sphere
import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# The linearized Floer operator on the Riemann sphere is Fredholm

Some Floer problems live on a closed domain: the comparison between the pair-of-pants product and
the quantum product deforms Floer data on the sphere with three poles, read in the coordinate
`w ∈ ℂ ≅ ℝ × ℝ` in which the poles are `0`, `1` and `∞`, with data that are a fixed compatible
structure `J₀` and the zero perturbation near `∞`. The realization of the linearized operator
`D_u : W^{1,2} → L²` of such data on the Sobolev space of the round metric of the sphere
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` for the weight `TauCeti.Floer.sphereWeight`)
has finite-dimensional kernel and closed range
(`TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere`). This file proves that its cokernel is
finite-dimensional
(`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`), so
that `D_u` is Fredholm (`isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base`), both in
the namespace `TauCeti.SymplecticForm`.

* **Cokernel elements are regular.** An element `h ∈ L²` orthogonal to the range of `D_u` is
  represented by a `C²` covector field `η` on the plane with `D_u^* η = 0`
  (`TauCeti.SymplecticForm.exists_contDiff_ae_eq_forall_floerLinearizationAdjoint_eq_zero`).
* **They extend across infinity.** Near `∞` the data are constant, and `η`, read in the chart
  `ζ = w⁻¹` as the `(0, 1)`-form `η' = η (ζ⁻¹) ∘ (a + b J₀)` (`TauCeti.Floer.covectorPullback`
  along the inversion), extends smoothly across `ζ = 0`
  (`exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero` in the
  namespace `TauCeti.SymplecticForm`). The extension is annihilated by the adjoint of the constant
  data, which transforms under the inversion by its Jacobian
  (`TauCeti.SymplecticForm.floerLinearizationAdjoint_const_covectorPullback_realChart_inv`).
* **The `L²` norm of a cokernel element lives on a disc.** Cut off by a function `ψ` of `|ζ|`
  which is one near `ζ = 0`, the extension is a compactly supported field in the chart, supported
  in a strip, so its `L²` norm is bounded by its Dirichlet energy (the Poincaré inequality), which
  is bounded by the `L²` norm of its adjoint (the energy estimate of constant data,
  `TauCeti.SymplecticForm.exists_forall_integral_norm_fderiv_sq_le_of_const`). That adjoint is
  `dψ`-times the extension, supported in an annulus. The `L²` norm of a covector field is
  invariant under the inversion, up to the factor `(1 + ‖J₀‖)²` of inverting `a + b J₀`, so the
  `L²` norm of `η` near `∞` is controlled by its `L²` norm on the image of that annulus, and
  `∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²` for every square-integrable `η` with `D_u^* η = 0`.
* **Peetre's argument.** Cut off near the disc `|w| ≤ b`, cokernel elements of norm at most one
  have jets bounded in `W^{1,2}` (by the estimate of the formal adjoint on a disc,
  `exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt`
  in the namespace `TauCeti.SymplecticForm`),
  so their restrictions to the disc lie in a compact set (Rellich's theorem,
  `TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`), and two of them
  close on the disc are close everywhere
  (`TauCeti.SymplecticForm.norm_sub_sq_le_of_setIntegral_le`). Hence the closed unit ball of the
  cokernel is totally bounded (`FiniteDimensional.of_norm_sub_le_mul_dist`).

The target is a symplectic inner product space. The index of `D_u` is not computed here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendices B and C, on the formal adjoint,
  the regularity of its weak solutions and the Fredholm property of real Cauchy–Riemann operators
  on closed surfaces.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  Floer problems on the sphere comparing the pair-of-pants and quantum products.
-/

public section

open Set Function Filter MeasureTheory Metric TauCeti.ConformalSobolev
open scoped Topology ENNReal

namespace TauCeti.SymplecticForm

open Floer

/-! ### The chart at infinity -/

section Inversion

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **A covector field read through the inversion, from below.** Where the structure is `J₀`, the
form `η' = η (ζ⁻¹) ∘ (a + b J₀)` read in the chart `ζ = w⁻¹` controls `η` at `w = ζ⁻¹`:
`|w|² ‖η w‖ ≤ (1 + ‖J₀‖) ‖η' ζ‖`. -/
private theorem mul_norm_le_norm_covectorPullback_realChart_inv {J : ℝ × ℝ → V → V →L[ℝ] V}
    {J₀ : AlmostComplexStructure V} {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ}
    (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0)
    (hJ : J (TauCeti.Complex.realChart (·⁻¹) ζ) (u (TauCeti.Complex.realChart (·⁻¹) ζ)) =
      J₀.toLinearMap.toContinuousLinearMap) :
    ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 2 *
        ‖η (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) *
        ‖covectorPullback (TauCeti.Complex.realChart (·⁻¹)) J u η ζ‖ := by
  have hr : 0 < ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 2 := by
    rw [TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
    positivity
  rw [covectorPullback_apply, hJ]
  exact J₀.mul_opNorm_le_opNorm_comp_smul_add_smul _
    (TauCeti.Complex.sq_add_sq_fderiv_realChart_inv hζ) hr

/-- **A covector field read through the inversion, from above.** Where the structure is `J₀`, the
form `η' = η (ζ⁻¹) ∘ (a + b J₀)` read in the chart `ζ = w⁻¹` is controlled by `η` at `w = ζ⁻¹`:
`‖η' ζ‖ ≤ (1 + ‖J₀‖) |w|² ‖η w‖`. -/
private theorem norm_covectorPullback_realChart_inv_le {J : ℝ × ℝ → V → V →L[ℝ] V}
    {J₀ : AlmostComplexStructure V} {u : ℝ × ℝ → V} {η : ℝ × ℝ → V →L[ℝ] ℝ} {ζ : ℝ × ℝ}
    (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0)
    (hJ : J (TauCeti.Complex.realChart (·⁻¹) ζ) (u (TauCeti.Complex.realChart (·⁻¹) ζ)) =
      J₀.toLinearMap.toContinuousLinearMap) :
    ‖covectorPullback (TauCeti.Complex.realChart (·⁻¹)) J u η ζ‖ ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) *
        ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 2 *
        ‖η (TauCeti.Complex.realChart (·⁻¹) ζ)‖ := by
  set a := (fderiv ℝ (TauCeti.Complex.realChart (·⁻¹)) ζ stdComplexLineReal).1
  set b := (fderiv ℝ (TauCeti.Complex.realChart (·⁻¹)) ζ stdComplexLineReal).2
  set r := ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 2
  set N := ‖J₀.toLinearMap.toContinuousLinearMap‖
  have hab : a ^ 2 + b ^ 2 = r ^ 2 := TauCeti.Complex.sq_add_sq_fderiv_realChart_inv hζ
  have hr : 0 ≤ r := by positivity
  have ha : |a| ≤ r := by
    rw [← abs_of_nonneg hr]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg b])
  have hb : |b| ≤ r := by
    rw [← abs_of_nonneg hr]
    exact sq_le_sq.1 (by nlinarith [sq_nonneg a])
  rw [covectorPullback_apply, hJ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc _ ≤ ‖η (TauCeti.Complex.realChart (·⁻¹) ζ)‖ * (r * (1 + N)) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_smul_one_add_smul_le _ ha hb)
          (norm_nonneg _)
    _ = _ := by ring

end Inversion

/-! ### The `L²` norm of a cokernel element is controlled on a disc -/

section Estimate

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {J₀ : AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- **The `L²` norm of a field supported in a disc, for constant data.** For an `ω`-compatible
`J₀` and `r > 0` there is `C` such that every compactly supported `C²` covector field `θ` vanishing
on `|ζ| ≥ r` satisfies `∫ ‖θ‖² ≤ C ∫ ‖D^* θ‖²` for the formal adjoint of the constant data `J₀`,
`0`. The field is supported in the strip `|t| < r`, so the Poincaré inequality bounds its `L²` norm
by its Dirichlet energy, which the energy estimate of constant data bounds by `∫ ‖D^* θ‖²`. -/
private theorem exists_integral_norm_sq_le_mul_integral_floerLinearizationAdjoint_const
    (h₀ : ω.Compatible J₀) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ ⦃θ : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 θ → HasCompactSupport θ →
      (∀ ζ, r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → θ ζ = 0) →
      ∫ ζ, ‖θ ζ‖ ^ 2 ≤ C * ∫ ζ, ‖ω.floerLinearizationAdjoint
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 θ
          ζ‖ ^ 2 := by
  obtain ⟨C, hC, hE⟩ := exists_forall_integral_norm_fderiv_sq_le_of_const (ω := ω) h₀
  refine ⟨(2 * r) ^ 2 * C, by positivity, fun θ hθ hθc hθ0 ↦ ?_⟩
  have hP := integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd (r := r)
    (hθ.of_le one_le_two) hθc fun ζ hζ ↦ hθ0 ζ (hζ.trans (by
      have h := Complex.abs_im_le_norm (Complex.equivRealProdCLM.symm ζ)
      rwa [Complex.equivRealProdCLM_symm_apply_im] at h))
  rw [← stdComplexLineImag_eq] at hP
  have hdθ := hθ.continuous_fderiv two_ne_zero
  have hdc (v : ℝ × ℝ) : Integrable fun ζ ↦ ‖fderiv ℝ θ ζ v‖ ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (f := fun ζ ↦ ‖fderiv ℝ θ ζ v‖ ^ 2)
      ((hdθ.clm_apply continuous_const).norm.pow 2)
      ((hθc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (ℝ × ℝ) →L[ℝ] (V →L[ℝ] ℝ) ↦ ‖L v‖ ^ 2)
        (by simp))
  have hIm : ∫ ζ, ‖fderiv ℝ θ ζ stdComplexLineImag‖ ^ 2 ≤
      ∫ ζ, (‖fderiv ℝ θ ζ stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ θ ζ stdComplexLineImag‖ ^ 2) :=
    integral_mono (hdc _) ((hdc _).add (hdc _)) fun ζ ↦ by
      nlinarith [sq_nonneg ‖fderiv ℝ θ ζ stdComplexLineReal‖]
  rw [mul_assoc]
  exact hP.trans (mul_le_mul_of_nonneg_left (hIm.trans (hE hθ hθc)) (by positivity))

/-- **The adjoint of a cut-off solution.** Let `η₀` be `C²` on the disc `|ζ| < a⁻¹` and annihilated
there, away from `ζ = 0`, by the formal adjoint of the constant data `J₀`, `0`. Let `ψ` be a smooth
cutoff whose derivative vanishes on `|ζ| < r` and has norm at most `M`, such that `ψ η₀` vanishes
near every point of `|ζ| > 2 r`, with `2 r < a⁻¹`. Then away from `ζ = 0` the adjoint of `ψ η₀` is
bounded by `M (1 + ‖J₀‖) ‖η₀‖` on the annulus `r ≤ |ζ| ≤ 2 r`, and vanishes off it. -/
private theorem norm_floerLinearizationAdjoint_smul_sq_le_indicator {a r M : ℝ}
    (hra : 2 * r < a⁻¹) {η₀ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₀ : ContDiffOn ℝ 2 η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹})
    (hD : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0)
    {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψd0 : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < r → fderiv ℝ ψ ζ = 0)
    (hψM : ∀ ζ, ‖fderiv ℝ ψ ζ‖ ≤ M)
    (hfar : ∀ ζ, 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖ → (fun ζ ↦ ψ ζ • η₀ ζ) =ᶠ[𝓝 ζ] 0)
    {ζ : ℝ × ℝ} (hζ : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 (fun ζ ↦ ψ ζ • η₀ ζ) ζ‖ ^ 2 ≤
      (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2 *
        {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
          ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}.indicator (fun ζ ↦ ‖η₀ ζ‖ ^ 2) ζ := by
  have hRHS : 0 ≤ (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖)) ^ 2 *
      {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
        ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}.indicator (fun ζ ↦ ‖η₀ ζ‖ ^ 2) ζ :=
    mul_nonneg (by positivity) (indicator_nonneg (fun _ _ ↦ by positivity) _)
  by_cases hζfar : 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖
  · rw [ω.floerLinearizationAdjoint_congr_of_eventuallyEq _ _ _ _ (hfar ζ hζfar),
      floerLinearizationAdjoint_zero, norm_zero, zero_pow two_ne_zero]
    exact hRHS
  have hζO : ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹ := lt_of_le_of_lt (not_lt.1 hζfar) hra
  have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero
    (J := fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (Ks := fun _ _ ↦ 0)
    (Kt := fun _ _ ↦ 0) (u := 0) (hψ.differentiable one_ne_zero ζ)
    ((hη₀.contDiffAt ((isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm
      continuous_const).mem_nhds hζO)).differentiableAt (by norm_num))
    (differentiableAt_const _) (hD ζ hζO hζ) (B := ‖J₀.toLinearMap.toContinuousLinearMap‖) le_rfl
  by_cases hnear : ‖Complex.equivRealProdCLM.symm ζ‖ < r
  · rw [hψd0 ζ hnear, norm_zero, zero_mul, zero_mul, norm_le_zero_iff] at hle
    rw [hle, norm_zero, zero_pow two_ne_zero]
    exact hRHS
  rw [indicator_of_mem (s := {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
    ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}) ⟨not_lt.1 hnear, not_lt.1 hζfar⟩]
  calc _ ≤ (‖fderiv ℝ ψ ζ‖ * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) * ‖η₀ ζ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ ≤ (M * (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) * ‖η₀ ζ‖) ^ 2 := by
        gcongr
        exact hψM ζ
    _ = _ := by ring

omit [FiniteDimensional ℝ V] in
/-- A field `η₀`, `C²` on the disc `|ζ| < a⁻¹`, cut off by a `C²` function `ψ` vanishing on
`|ζ| ≥ 2 r`, with `2 r < a⁻¹`, is a compactly supported `C²` field on the plane, vanishing on
`|ζ| ≥ 2 r` and near every point of `|ζ| > 2 r`. -/
private theorem contDiff_smul_of_contDiffOn {a r : ℝ} (hra : 2 * r < a⁻¹)
    {η₀ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₀ : ContDiffOn ℝ 2 η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹}) {ψ : ℝ × ℝ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ ζ, 2 * r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → ψ ζ = 0) :
    ContDiff ℝ 2 (fun ζ ↦ ψ ζ • η₀ ζ) ∧ HasCompactSupport (fun ζ ↦ ψ ζ • η₀ ζ) ∧
      (∀ ζ, 2 * r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → ψ ζ • η₀ ζ = 0) ∧
      ∀ ζ, 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖ → (fun ζ ↦ ψ ζ • η₀ ζ) =ᶠ[𝓝 ζ] 0 := by
  have hθ0 (ζ : ℝ × ℝ) (hζ : 2 * r ≤ ‖Complex.equivRealProdCLM.symm ζ‖) : ψ ζ • η₀ ζ = 0 := by
    simp [hψ0 ζ hζ]
  have hθfar (ζ : ℝ × ℝ) (hζ : 2 * r < ‖Complex.equivRealProdCLM.symm ζ‖) :
      (fun ζ ↦ ψ ζ • η₀ ζ) =ᶠ[𝓝 ζ] 0 := by
    filter_upwards [(isOpen_lt continuous_const
      Complex.equivRealProdCLM.symm.continuous.norm).mem_nhds hζ] with ζ' hζ'
    exact hθ0 ζ' hζ'.le
  refine ⟨contDiff_iff_contDiffAt.2 fun ζ ↦ ?_, HasCompactSupport.intro
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r)) fun ζ hζ ↦ hθ0 ζ (not_le.1 hζ).le,
    hθ0, hθfar⟩
  -- Near `|ζ| ≥ a⁻¹ > 2 r` the field vanishes.
  by_cases hζ : ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹
  · exact hψ.contDiffAt.smul (hη₀.contDiffAt ((isOpen_lt
      Complex.equivRealProdCLM.symm.continuous.norm continuous_const).mem_nhds hζ))
  · exact contDiffAt_const.congr_of_eventuallyEq (hθfar ζ (by linarith [not_lt.1 hζ]))

/-- **The `L²` norm of a solution near the centre of the chart at infinity.** Let `J₀` be
`ω`-compatible, `0 < r` and `2 r < a⁻¹`. A covector field `η₀`, `C²` on the disc `|ζ| < a⁻¹` and
annihilated there, away from `ζ = 0`, by the formal adjoint of the constant data `J₀`, `0`, has its
`L²` norm on the disc `|ζ| ≤ r` controlled by its `L²` norm on the annulus `r ≤ |ζ| ≤ 2 r`, with a
constant independent of `η₀`. The field cut off by a function `ψ` which is one on `|ζ| ≤ r` and zero
on `|ζ| ≥ 2 r` has its `L²` norm bounded by the `L²` norm of its adjoint, which is `dψ`-times
`η₀`, supported in the annulus. -/
private theorem exists_setIntegral_norm_sq_le_mul_setIntegral_of_floerLinearizationAdjoint_eq_zero
    (h₀ : ω.Compatible J₀) {a r : ℝ} (hr : 0 < r) (hra : 2 * r < a⁻¹) :
    ∃ c, 0 ≤ c ∧ ∀ ⦃η₀ : ℝ × ℝ → V →L[ℝ] ℝ⦄,
      ContDiffOn ℝ 2 η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹} →
      (∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹ → Complex.equivRealProdCLM.symm ζ ≠ 0 →
        ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
          (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0) →
      ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖η₀ ζ‖ ^ 2 ≤
        c * ∫ ζ in {ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
          ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}, ‖η₀ ζ‖ ^ 2 := by
  obtain ⟨C, hC, hP⟩ :=
    exists_integral_norm_sq_le_mul_integral_floerLinearizationAdjoint_const (ω := ω) h₀ (2 * r)
  obtain ⟨ψ, hψs, -, hψ1, hψ0, hψd0, -, hψM⟩ := exists_contDiff_cutoff_comp_continuousLinearMap
    (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hr
  set M := 2 * ‖(Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)‖ / r
  set N := 1 + ‖J₀.toLinearMap.toContinuousLinearMap‖
  set A := {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
    ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}
  refine ⟨C * (M * N) ^ 2, by positivity, fun η₀ hη₀ hD ↦ ?_⟩
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  set θ : ℝ × ℝ → V →L[ℝ] ℝ := fun ζ ↦ ψ ζ • η₀ ζ
  obtain ⟨hθ, hθc, hθ0, hθfar⟩ := contDiff_smul_of_contDiffOn hra hη₀ (hψs.of_le (by simp)) hψ0
  have hAc : IsCompact A := (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r)).inter_left
    (isClosed_le continuous_const Complex.equivRealProdCLM.symm.continuous.norm)
  have hAi : IntegrableOn (fun ζ ↦ ‖η₀ ζ‖ ^ 2) A :=
    ((hη₀.continuousOn.mono fun ζ (hζ : ζ ∈ A) ↦ lt_of_le_of_lt hζ.2 hra).norm.pow
      2).integrableOn_compact hAc
  -- The adjoint of `θ` is `dψ`-times `η₀`, supported in the annulus `A`.
  have hDθ : ∫ ζ, ‖ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 θ ζ‖ ^ 2 ≤ (M * N) ^ 2 * ∫ ζ in A, ‖η₀ ζ‖ ^ 2 := by
    rw [← integral_indicator (hAc.measurableSet), ← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
      ((hAi.integrable_indicator hAc.measurableSet).const_mul _) ?_
    filter_upwards [Measure.ae_ne volume 0] with ζ hζ0
    exact norm_floerLinearizationAdjoint_smul_sq_le_indicator hra hη₀ hD
      (hψs.of_le (by simp)) hψd0 hψM hθfar fun h ↦
        hζ0 (Complex.equivRealProdCLM.symm.map_eq_zero_iff.1 h)
  have hθη : ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖η₀ ζ‖ ^ 2 =
      ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖θ ζ‖ ^ 2 :=
    setIntegral_congr_fun (isCompact_setOf_norm_equivRealProdCLM_symm_le r).measurableSet
      fun ζ hζ ↦ by simp [θ, hψ1 ζ hζ]
  calc _ ≤ ∫ ζ, ‖θ ζ‖ ^ 2 := by
        rw [hθη]
        exact setIntegral_le_integral (hθ.continuous.integrable_norm_sq_of_hasCompactSupport hθc)
          (ae_of_all _ fun _ ↦ by positivity)
    _ ≤ C * ((M * N) ^ 2 * ∫ ζ in A, ‖η₀ ζ‖ ^ 2) :=
        (hP hθ hθc fun ζ hζ ↦ hθ0 ζ hζ).trans (mul_le_mul_of_nonneg_left hDθ hC)
    _ = _ := by ring

/-- **The `L²` norm near infinity, read in the chart at infinity.** Let `η₀` be continuous on the
disc `|ζ| ≤ r` and agree, away from `ζ = 0`, with `η` read through the inversion with the structure
`J₀`. Then the `L²` norm of `η` on `|w| > r⁻¹` is at most `(1 + ‖J₀‖)²` times that of `η₀` on
`|ζ| ≤ r`. -/
private theorem setIntegral_norm_sq_le_of_eq_covectorPullback {u : ℝ × ℝ → V}
    {η η₀ : ℝ × ℝ → V →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r)
    (hη₀ : ContinuousOn η₀ {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r})
    (heq : ∀ ζ, ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r → Complex.equivRealProdCLM.symm ζ ≠ 0 →
      η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ) :
    ∫ w in {w | r⁻¹ < ‖Complex.equivRealProdCLM.symm w‖}, ‖η w‖ ^ 2 ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
        ∫ ζ in {ζ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}, ‖η₀ ζ‖ ^ 2 := by
  set S := {ζ : ℝ × ℝ | Complex.equivRealProdCLM.symm ζ ≠ 0 ∧
    ‖Complex.equivRealProdCLM.symm ζ‖ < r}
  set B := {ζ : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm ζ‖ ≤ r}
  have hS : MeasurableSet S :=
    ((isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
      (isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm continuous_const)).measurableSet
  have hB : IsCompact B := isCompact_setOf_norm_equivRealProdCLM_symm_le r
  have hBi : IntegrableOn (fun ζ ↦ ‖η₀ ζ‖ ^ 2) B := (hη₀.norm.pow 2).integrableOn_compact hB
  have hSB : S ⊆ B := fun ζ hζ ↦ hζ.2.le
  rw [← TauCeti.Complex.image_realChart_inv_setOf_lt hr,
    TauCeti.Complex.setIntegral_image_realChart_inv hS fun ζ hζ ↦ hζ.1,
    ← integral_const_mul]
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
    ((hBi.mono_set hSB).const_mul _) (ae_restrict_of_forall_mem hS fun ζ hζ ↦ ?_)).trans
    (setIntegral_mono_set (hBi.const_mul _) (ae_of_all _ fun _ ↦ by positivity)
      (Eventually.of_forall hSB))
  have h := mul_norm_le_norm_covectorPullback_realChart_inv
    (J := fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (u := u) (η := η) hζ.1 rfl
  rw [← heq ζ hζ.2.le hζ.1] at h
  have h2 := pow_le_pow_left₀ (by positivity) h 2
  calc _ = (‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ ^ 2 *
        ‖η (TauCeti.Complex.realChart (·⁻¹) ζ)‖) ^ 2 := by ring
    _ ≤ _ := h2
    _ = _ := by ring

/-- **The `L²` norm on an annulus of the chart at infinity.** Let `η` be continuous and square
integrable, and let `η₀` agree on the annulus `r ≤ |ζ| ≤ 2 r` with `η` read through the inversion
with the structure `J₀`. Then the `L²` norm of `η₀` on that annulus is at most `(1 + ‖J₀‖)²` times
the `L²` norm of `η` on the disc `|w| ≤ r⁻¹`, which contains the image `(2 r)⁻¹ ≤ |w| ≤ r⁻¹` of the
annulus. -/
private theorem setIntegral_annulus_norm_sq_le_of_eq_covectorPullback {u : ℝ × ℝ → V}
    {η η₀ : ℝ × ℝ → V →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) (hη : Continuous η)
    (hηi : Integrable fun z ↦ ‖η z‖ ^ 2)
    (heq : ∀ ζ, r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ → ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r →
      η₀ ζ = covectorPullback (TauCeti.Complex.realChart (·⁻¹))
        (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ) :
    ∫ ζ in {ζ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧ ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r},
        ‖η₀ ζ‖ ^ 2 ≤
      (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
        ∫ w in {w | ‖Complex.equivRealProdCLM.symm w‖ ≤ r⁻¹}, ‖η w‖ ^ 2 := by
  set A := {ζ : ℝ × ℝ | r ≤ ‖Complex.equivRealProdCLM.symm ζ‖ ∧
    ‖Complex.equivRealProdCLM.symm ζ‖ ≤ 2 * r}
  set ι := TauCeti.Complex.realChart (·⁻¹)
  have hAc : IsCompact A := (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * r)).inter_left
    (isClosed_le continuous_const Complex.equivRealProdCLM.symm.continuous.norm)
  have hA0 (ζ : ℝ × ℝ) (hζ : ζ ∈ A) : Complex.equivRealProdCLM.symm ζ ≠ 0 :=
    norm_pos_iff.1 (hr.trans_le hζ.1)
  have hιc : ContinuousOn ι A := fun ζ hζ ↦
    (TauCeti.Complex.contDiffAt_realChart_inv (hA0 ζ hζ) (n := 0)).continuousAt.continuousWithinAt
  have hgi : IntegrableOn (fun ζ ↦ ‖Complex.equivRealProdCLM.symm (ι ζ)‖ ^ 4 * ‖η (ι ζ)‖ ^ 2) A :=
    (((Complex.equivRealProdCLM.symm.continuous.comp_continuousOn hιc).norm.pow 4).mul
      ((hη.comp_continuousOn hιc).norm.pow 2)).integrableOn_compact hAc
  have himage : ι '' A ⊆ {w | ‖Complex.equivRealProdCLM.symm w‖ ≤ r⁻¹} := by
    rintro _ ⟨ζ, hζ, rfl⟩
    rw [mem_ofPred_eq, TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
    exact inv_anti₀ hr hζ.1
  calc _ ≤ ∫ ζ in A, (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 *
        (‖Complex.equivRealProdCLM.symm (ι ζ)‖ ^ 4 * ‖η (ι ζ)‖ ^ 2) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity) (hgi.const_mul _)
          (ae_restrict_of_forall_mem hAc.measurableSet fun ζ hζ ↦ by
            have h := norm_covectorPullback_realChart_inv_le
              (J := fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (u := u) (η := η) (hA0 ζ hζ) rfl
            rw [← heq ζ hζ.1 hζ.2] at h
            calc ‖η₀ ζ‖ ^ 2 ≤ ((1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) *
                  ‖Complex.equivRealProdCLM.symm (ι ζ)‖ ^ 2 * ‖η (ι ζ)‖) ^ 2 :=
                  pow_le_pow_left₀ (norm_nonneg _) h 2
              _ = _ := by ring)
    _ = (1 + ‖J₀.toLinearMap.toContinuousLinearMap‖) ^ 2 * ∫ w in ι '' A, ‖η w‖ ^ 2 := by
        rw [integral_const_mul,
          TauCeti.Complex.setIntegral_image_realChart_inv hAc.measurableSet hA0]
    _ ≤ _ := mul_le_mul_of_nonneg_left (setIntegral_mono_set hηi.integrableOn
        (ae_of_all _ fun _ ↦ by positivity) (Eventually.of_forall himage)) (by positivity)

/-- **The extension across infinity solves the adjoint equation.** Let the data be `J₀` and `0`
on `‖w‖ ≥ T`, with `2 T < a`, and let `η` be a `C¹` covector field annihilated by `D_u^*`. A field
`η₀` agreeing on the punctured disc `0 < |ζ| < a⁻¹` with `η` read through the inversion is
annihilated there by the formal adjoint of the constant data `J₀`, `0`: the adjoint of the form
read through the inversion is the Jacobian of the inversion times the adjoint of `η`. -/
private theorem floerLinearizationAdjoint_eq_zero_of_eq_covectorPullback
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) {a : ℝ} (ha : 0 < a) (haT : 2 * T < a)
    {η η₀ : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0)
    (heq : ∀ ζ : ℝ × ℝ, ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹ →
      Complex.equivRealProdCLM.symm ζ ≠ 0 → η₀ ζ = covectorPullback
        (TauCeti.Complex.realChart (·⁻¹)) (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) u η ζ)
    {ζ : ℝ × ℝ} (hζ : ‖Complex.equivRealProdCLM.symm ζ‖ < a⁻¹)
    (hζ0 : Complex.equivRealProdCLM.symm ζ ≠ 0) :
    ω.floerLinearizationAdjoint (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ _ ↦ 0) 0 η₀ ζ = 0 := by
  have hev : η₀ =ᶠ[𝓝 ζ] covectorPullback (TauCeti.Complex.realChart (·⁻¹))
      (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) 0 η := by
    filter_upwards [((isOpen_lt Complex.equivRealProdCLM.symm.continuous.norm
      continuous_const).inter (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous
        continuous_const)).mem_nhds ⟨hζ, hζ0⟩] with ζ' hζ'
    rw [heq ζ' hζ'.1 hζ'.2, covectorPullback_apply, covectorPullback_apply]
  have hw : 2 * T < ‖Complex.equivRealProdCLM.symm (TauCeti.Complex.realChart (·⁻¹) ζ)‖ := by
    rw [TauCeti.Complex.norm_equivRealProdCLM_symm_realChart_inv]
    exact haT.trans ((lt_inv_comm₀ ha (norm_pos_iff.2 hζ0)).2 hζ)
  rw [ω.floerLinearizationAdjoint_congr_of_eventuallyEq _ _ _ _ hev,
    floerLinearizationAdjoint_const_covectorPullback_realChart_inv hζ0
      (hη.differentiable one_ne_zero _),
    ← floerLinearizationAdjoint_eq_const_of_eq_base hJ₀ hKs₀ hKt₀ 0 η hw, hD, smul_zero]

/-- **The `L²` norm of a solution of the formal adjoint on the sphere is controlled on a disc.**
Let the data be `J₀` and the zero perturbation on `‖w‖ ≥ T`, with `J₀` compatible with `ω`. There
are `b > 0` and `A ≥ 0` such that every square-integrable `C¹` covector field `η` annihilated by the
formal adjoint `D_u^*` satisfies `∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²`. Near the point at infinity `η`,
read in the chart `ζ = w⁻¹`, extends smoothly across `ζ = 0`
(`exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero`), and the
extension has its `L²` norm near `ζ = 0` controlled by its `L²` norm on an annulus, which is part
of the disc `|w| ≤ b`. -/
private theorem exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0) (h₀ : ω.Compatible J₀) :
    ∃ b A, 0 < b ∧ 0 ≤ A ∧ ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 1 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖η z‖ ^ 2 := by
  set a := 2 * |T| + 1
  have ha : 0 < a := by positivity
  have haT : 2 * T < a := by linarith [le_abs_self T]
  set r := (4 * a)⁻¹
  have hr : 0 < r := by positivity
  have hra : 2 * r < a⁻¹ := by
    rw [show 2 * r = (2 * a)⁻¹ by simp only [r]; field_simp; ring]
    exact inv_strictAnti₀ ha (by linarith)
  obtain ⟨c, hc, hest⟩ :=
    exists_setIntegral_norm_sq_le_mul_setIntegral_of_floerLinearizationAdjoint_eq_zero
      (ω := ω) h₀ hr hra
  set N := 1 + ‖J₀.toLinearMap.toContinuousLinearMap‖
  refine ⟨r⁻¹, 1 + N ^ 2 * c * N ^ 2, by positivity, by positivity, fun η hη hD hηi ↦ ?_⟩
  -- Far out the data are constant, so `η` extends smoothly across the point at infinity.
  obtain ⟨η₀, hη₀, heq⟩ :=
    ω.exists_contDiffOn_eq_covectorPullback_inv_of_floerLinearizationAdjoint_eq_zero h₀.invariant u
      (fun z _ ↦ hη.differentiable one_ne_zero z) (fun z hz ↦ by
        rw [← floerLinearizationAdjoint_eq_const_of_eq_base hJ₀ hKs₀ hKt₀ u η (haT.trans hz)]
        exact hD z) hηi.integrableOn
  have hra' : r < a⁻¹ := by linarith
  have hX := setIntegral_norm_sq_le_of_eq_covectorPullback (J₀ := J₀) (u := u) hr
    (hη₀.continuousOn.mono fun ζ hζ ↦ lt_of_le_of_lt hζ hra')
    fun ζ hζ hζ0 ↦ heq ζ (lt_of_le_of_lt hζ hra') hζ0
  have hY := setIntegral_annulus_norm_sq_le_of_eq_covectorPullback (J₀ := J₀) (u := u) hr
    hη.continuous hηi fun ζ h1 h2 ↦ heq ζ (lt_of_le_of_lt h2 hra) (norm_pos_iff.1 (hr.trans_le h1))
  have hE := hest (hη₀.of_le (by simp)) fun ζ hζ hζ0 ↦
    floerLinearizationAdjoint_eq_zero_of_eq_covectorPullback hJ₀ hKs₀ hKt₀ ha haT hη hD heq hζ hζ0
  have hDm : MeasurableSet {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ r⁻¹} :=
    (isCompact_setOf_norm_equivRealProdCLM_symm_le r⁻¹).measurableSet
  have hcompl : {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ r⁻¹}ᶜ =
      {z | r⁻¹ < ‖Complex.equivRealProdCLM.symm z‖} := by
    ext z
    simp
  rw [← integral_add_compl hDm hηi, hcompl]
  have hP : 0 ≤ ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ r⁻¹}, ‖η z‖ ^ 2 :=
    setIntegral_nonneg hDm fun _ _ ↦ by positivity
  have := mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hY hc))
    (by positivity : (0 : ℝ) ≤ N ^ 2)
  nlinarith [hP]

end Estimate

/-! ### The cokernel is finite-dimensional -/

section Fredholm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V} {J₀ : AlmostComplexStructure V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {T : ℝ}

/-- The structures `J(z, u z)` along a continuous map `u` are bounded when they are continuous in
`z` and equal to `J₀` on `‖z‖ ≥ T`. -/
private theorem exists_forall_norm_le_of_eq_base (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : Continuous u) :
    ∃ B, ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B := by
  have hf : Continuous fun z ↦ (J z (u z)).toLinearMap.toContinuousLinearMap :=
    continuous_iff_continuousAt.2 fun z ↦
      (hJ z).continuousAt.comp (f := fun z ↦ (z, u z)) (continuousAt_id.prodMk hu.continuousAt)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℝ × ℝ) T).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max B ‖J₀.toLinearMap.toContinuousLinearMap‖, fun z ↦ ?_⟩
  by_cases hz : ‖z‖ ≤ T
  · exact (hB z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · rw [hJ₀ z (not_le.1 hz).le]
    exact le_max_right _ _

/-- **The weighted energy of a cut-off cokernel element.** Let `J` be compatible along `u` with
`‖J(z, u z)‖ ≤ B`, and let `χ` be a `C²` cutoff with values in `[0, 1]`, vanishing on `|w| ≥ b`,
with `‖dχ‖ ≤ M`. Then there is `K` such that for every square-integrable `C²` covector field `η`
with `D_u^* η = 0` the `W^{1,2}` energy of `χ η` for the weight of the sphere is at most
`K ∫ ‖η‖²`: this is
`exists_forall_integral_weighted_smul_le_of_integral_floerLinearizationAdjoint_le` for the weight
`1`, with the adjoint term bounded pointwise by
`norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero`. -/
private theorem exists_integral_sphereWeight_smul_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχ01 : ∀ z, χ z ∈ Icc 0 1) {M b : ℝ}
    (hχb : ∀ z, b ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) :
    ∃ K, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, (sphereWeight z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z, ‖η z‖ ^ 2 := by
  obtain ⟨C, -, hE⟩ :=
    ω.exists_forall_integral_weighted_smul_le_of_integral_floerLinearizationAdjoint_le hJ hKs hKt hu
      (fun _ ↦ zero_le_one) continuous_const (lt_add_one b) (fun _ _ ↦ one_pos) (fun z _ ↦ hc z)
      continuous_sphereWeight sphereWeight_le_one hχ hχ01 hχb
  refine ⟨C * ((M * (1 + B)) ^ 2 + 1), fun η hη hD hηi ↦ hE hη hηi ?_⟩
  -- The adjoint of `χ η` is `dχ`-times `η`, of norm at most `M (1 + B) ‖η‖`.
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity) (hηi.const_mul _)
    (ae_of_all _ fun z ↦ ?_)
  have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero
    (hχ.differentiable two_ne_zero z) (hη.differentiable two_ne_zero z)
    (((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero) (hD z) (hB z)
  dsimp only
  calc _ ≤ (M * (1 + B) * ‖η z‖) ^ 2 := by
        rw [one_mul]
        exact pow_le_pow_left₀ (norm_nonneg _) (hle.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hχM z) (by linarith [(norm_nonneg _).trans (hB z)]))
          (norm_nonneg _))) 2
    _ = _ := by ring

/-- **Cokernel elements on the sphere are regular.** Under the hypotheses of
`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base`, the
coefficient field of `D_u` is essentially bounded, so every `h ∈ L²` orthogonal to the range of
`D_u` is represented by a `C²` covector field `η` on the whole plane with `D_u^* η = 0`. -/
private theorem exists_contDiff_ae_eq_forall_floerLinearizationAdjoint_eq_zero_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    {h : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))}
    (hh : h ∈ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ) :
    ∃ η : ℝ × ℝ → V →L[ℝ] ℝ, ContDiff ℝ 2 η ∧ (fun z ↦ innerSL ℝ (h z)) =ᵐ[volume] η ∧
      ∀ z, ω.floerLinearizationAdjoint (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0 :=
  ω.exists_contDiff_ae_eq_forall_floerLinearizationAdjoint_eq_zero
    (J := fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) isWeight_sphereWeight hJ
    (fun z ↦ (J z (u z)).toContinuousLinearMap_mul_self) hKs hKt hu
    (ω.memLp_floerConformalJetCoeff_of_eq_base isWeight_sphereWeight
      (J₀ := J₀.toLinearMap.toContinuousLinearMap) (fun z hz y ↦ by simp [hJ₀ z hz y]) hKs₀ hKt₀
      (fun z ↦ (hJ z).of_le (by norm_num)) (fun z ↦ (hKs z).of_le (by norm_num))
      (fun z ↦ (hKt z).of_le (by norm_num)) (hu.of_le (by norm_num))) hh

/-- **The cokernel of the linearized operator on the sphere is finite-dimensional.** Let the Floer
data `J`, `K_s`, `K_t` on the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero
perturbation on `‖w‖ ≥ T`, a neighbourhood of the point at infinity of the sphere. Let `J` be `C³`
and `K_s`, `K_t` be `C⁴` along a `C³` map `u`, with `J(w, u w)` compatible. Then the orthogonal
complement of the range of the realization of `D_u` from `W^{1,2}` of the sphere to `L²` is
finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  set E := (ω.floerConformalSobolevOperator univ sphereWeight
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- The constants: the `L²` estimate on a disc, the cutoff, the energy of cut-off cokernel
  -- elements, and the compact restriction to the disc `|w| ≤ b`.
  obtain ⟨b, A, hb, hA0, hglob⟩ :=
    exists_integral_norm_sq_le_of_floerLinearizationAdjoint_eq_zero (ω := ω) (u := u) hJ₀ hKs₀
      hKt₀ (hJ₀ (|T|, 0) (by simp [Prod.norm_def, le_abs_self]) (u (|T|, 0)) ▸ hc (|T|, 0))
  obtain ⟨B, hB⟩ := exists_forall_norm_le_of_eq_base hJ₀ hJ1 hu.continuous
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, -, -, hχM⟩ := exists_contDiff_cutoff_comp_continuousLinearMap
    (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) hb
  replace hχs : ContDiff ℝ 2 χ := hχs.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_integral_sphereWeight_smul_le ω hJ1 (fun z ↦ (hKs z).of_le (by norm_num))
    (fun z ↦ (hKt z).of_le (by norm_num)) hu1 hc hB hχs hχ01 hχ0 hχM
  set Kb := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hKb : IsCompact Kb := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  obtain ⟨B', hB'⟩ := exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq
    (V := V →L[ℝ] ℝ) isWeight_sphereWeight hKb (subset_univ _)
  -- Every cokernel element is represented by a `C²` solution of the formal adjoint.
  choose η hηs hηae hηD using fun h : E ↦
    exists_contDiff_ae_eq_forall_floerLinearizationAdjoint_eq_zero_of_eq_base ω hJ₀ hKs₀ hKt₀ hJ
      hKs hKt hu h.property
  -- Their cut-offs are test sections.
  have hgT (h : E) : (fun z ↦ χ z • η h z) ∈ testSection (V →L[ℝ] ℝ) univ :=
    mem_testSection_iff.2 ⟨hχs.smul (hηs h), HasCompactSupport.intro
      (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * b)) fun z hz ↦ by
        simp [hχ0 z (not_le.1 hz).le], subset_univ _⟩
  set j : E → H1 (V →L[ℝ] ℝ) univ sphereWeight := fun h ↦
    ⟨(memLp_jet isWeight_sphereWeight (hgT h)).toLp (jet sphereWeight fun z ↦ χ z • η h z),
      jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule isWeight_sphereWeight (hgT h))⟩
  set R := (restrictWeightedValue (V →L[ℝ] ℝ) univ Kb).comp
    (H1 (V →L[ℝ] ℝ) univ sphereWeight).subtypeL
  obtain ⟨Kc, hKc, hKcsub⟩ :=
    (isCompactOperator_restrictWeightedValue_comp_subtypeL (V := V →L[ℝ] ℝ) isWeight_sphereWeight
      hKb (subset_univ _)).image_closedBall_subset_compact (√(max K 0 * 1 ^ 2))
  -- By Rellich's theorem the cut-off representatives of the unit ball of `E` restrict to a compact
  -- set on the disc, and two cokernel elements close on the disc are close everywhere.
  refine FiniteDimensional.of_norm_sub_le_mul_dist (𝕜 := ℝ) (f := fun h ↦ R (j h)) hKc
    (fun h hh ↦ hKcsub ⟨j h, mem_closedBall_zero_iff.2 (by
      rw [← Submodule.norm_coe]
      exact norm_toLp_jet_le_of_ae_eq isWeight_sphereWeight (hηae h) (hgT h)
        (by rwa [Submodule.norm_coe]) (hK (hηs h) (hηD h))), rfl⟩) (C := √(A * |B'|))
    fun h h' _ _ ↦ ?_
  have hsq := norm_sub_sq_le_of_setIntegral_le hJ1 hu1 hKb.measurableSet hA0
    (fun η hη ↦ hglob (hη.of_le one_le_two)) (hηs h) (hηs h') (hηae h) (hηae h') (hηD h) (hηD h')
    (fun z hz ↦ by simp [hχ1 z hz]) (fun z hz ↦ by simp [hχ1 z hz])
    (hB' (((hχs.smul (hηs h)).sub (hχs.smul (hηs h'))).continuous.continuousOn)
      (toLp_jet_sub_ae_eq isWeight_sphereWeight (hgT h) (hgT h')))
  rw [← Submodule.coe_sub, Submodule.norm_coe] at hsq
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rwa [mul_pow, Real.sq_sqrt (by positivity), dist_eq_norm, ← map_sub]

/-- **The linearized operator on the sphere is Fredholm.** Let the Floer data `J`, `K_s`, `K_t` on
the plane `ℝ × ℝ ≅ ℂ` be the fixed structure `J₀` and the zero perturbation on `‖w‖ ≥ T`, a
neighbourhood of the point at infinity of the sphere. Let `J` be `C³` and `K_s`, `K_t` be `C⁴`
along a `C³` map `u`, with `J(w, u w)` compatible. Then the realization of `D_u` from `W^{1,2}` of
the sphere to `L²` is Fredholm. -/
theorem isFredholm_floerConformalSobolevOperator_sphereWeight_of_eq_base (ω : SymplecticForm V)
    (hJ₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, J z y = J₀)
    (hKs₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Ks z y = 0)
    (hKt₀ : ∀ z : ℝ × ℝ, T ≤ ‖z‖ → ∀ y, Kt z y = 0)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z))
    (hu : ContDiff ℝ 3 u) (hc : ∀ z, ω.Compatible (J z (u z))) :
    (ω.floerConformalSobolevOperator univ sphereWeight
      (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u).IsFredholm := by
  set D := ω.floerConformalSobolevOperator univ sphereWeight
    (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt u
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hKs2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Ks) (z, u z) := (hKs z).of_le (by norm_num)
  have hKt2 (z : ℝ × ℝ) : ContDiffAt ℝ 2 (uncurry Kt) (z, u z) := (hKt z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  rw [TauCeti.isFredholm_iff_finite_ker_coker]
  refine ⟨ω.finiteDimensional_ker_floerConformalSobolevOperator_sphereWeight_of_eq_base hJ₀ hKs₀
    hKt₀ hJ1 hKs2 hKt2 hu1 hc, ?_⟩
  -- The range is closed, so the cokernel is the orthogonal complement of the range.
  have hcl := ω.isClosed_range_floerConformalSobolevOperator_sphereWeight_of_eq_base hJ₀ hKs₀ hKt₀
    hJ1 hKs2 hKt2 hu1 hc
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range] at hcl
  have : CompleteSpace D.range := hcl.completeSpace_coe
  have := finiteDimensional_orthogonal_range_floerConformalSobolevOperator_sphereWeight_of_eq_base
    ω hJ₀ hKs₀ hKt₀ hJ hKs hKt hu hc
  exact (Submodule.quotientEquivOfIsCompl D.range D.rangeᗮ
    (Submodule.isCompl_orthogonal _)).symm.finiteDimensional

end Fredholm

end TauCeti.SymplecticForm
