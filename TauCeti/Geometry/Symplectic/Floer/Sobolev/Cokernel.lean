/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint

import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.MeasureTheory.Function.L2Space.InnerSL

/-!
# Finite cokernels of the linearized operator on the plane

Let `ρ ≤ 1` be a conformal weight on the whole plane `ℂ ≅ ℝ × ℝ`, and let
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` on `univ`) of the linearized Floer operator
along a map `u` into a finite-dimensional symplectic inner product space `(V, ω)`. The two weights
in use are the cylindrical weight `(1 + |w|²)⁻¹` of a PSS plane, a plane with a cylindrical end,
and the weight `(1 + |w|²)⁻²` of the round sphere, a plane with a point at infinity.

This file proves Peetre's argument for the finiteness of the cokernel of `D_u`, given the one
estimate that depends on the geometry at infinity: an `L²` bound of cokernel elements by their
`L²` norm on a disc. Precisely, suppose that every `C²` covector field `η` with `D_u^* η = 0` and
`‖η‖²` integrable satisfies `∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²`. Then the orthogonal complement of the
range of `D_u` is finite-dimensional
(`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_integral_norm_sq_le`, in the
namespace `TauCeti.SymplecticForm`).

* **Cokernel elements are regular.** An element `h ∈ L²(ℂ, V)` orthogonal to the range of `D_u`
  agrees almost everywhere with a `C²` covector field `η` with `D_u^* η = 0`
  (`TauCeti.SymplecticForm.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`).
* **Cut-off cokernel elements are bounded in `W^{1,2}`.** For a cutoff `χ` equal to `1` on the disc
  `|w| ≤ b`, the estimate of the formal adjoint on discs,
  `exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt`
  in the namespace `TauCeti.SymplecticForm`, bounds the weighted `W^{1,2}` norm of `χ η` by a
  constant times `∫ ‖η‖²`, since `D_u^* (χ η)` only involves the derivative of `χ`.
* **Peetre's argument.** By Rellich's theorem
  (`TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`), the
  restrictions of the cut-off cokernel elements of norm at most `R` to the disc `|w| ≤ b` form a
  compact family. An infinite-dimensional cokernel would contain a sequence of vectors of norm at
  most `R` at mutual distance at least one, two of which are close on the disc, hence everywhere by
  the hypothesis.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 3.1 and Appendices B and C, on the formal adjoint, the
  regularity of its weak solutions and the Fredholm property of real Cauchy–Riemann operators.
-/

public section

open Set Function Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti.SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {J : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

omit [FiniteDimensional ℝ V] in
/-- The jets in `W^{1,2}` of the cut-offs `χ η` of cokernel elements are bounded: if the weighted
energy of `χ η` is at most `K ∫ ‖η‖²`, `η` represents `h ∈ L²(ℂ, V)` and `‖h‖ ≤ r`, then the class
of the jet of `χ η` has norm at most `√(max K 0 r²)`. -/
private theorem norm_toLp_jet_le {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight univ ρ)
    {h : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))}
    {η g : ℝ × ℝ → V →L[ℝ] ℝ} (hηae : (fun z ↦ innerSL ℝ (h z)) =ᵐ[volume] η)
    (hg : g ∈ testSection (V →L[ℝ] ℝ) univ) {K r : ℝ} (hr : ‖h‖ ≤ r)
    (hK : Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, (ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 + ‖fderiv ℝ g z (0, 1)‖ ^ 2) ≤
        K * ∫ z, ‖η z‖ ^ 2) :
    ‖(memLp_jet hρ hg).toLp (jet ρ g)‖ ≤ √(max K 0 * r ^ 2) := by
  obtain ⟨hηn, hηi⟩ :=
    Lp.integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq (ae_restrict_of_ae hηae)
  rw [setIntegral_univ] at hηn
  replace hηi := integrableOn_univ.1 hηi
  have h1 := sq_norm_le_integral hρ hg (memLp_jet hρ hg).coeFn_toLp
  rw [setIntegral_univ] at h1
  have h4 : ∫ z, ‖η z‖ ^ 2 ≤ r ^ 2 := by
    rw [hηn]
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  refine Real.le_sqrt_of_sq_le ((h1.trans (hK hηi)).trans ?_)
  calc K * ∫ z, ‖η z‖ ^ 2 ≤ max K 0 * ∫ z, ‖η z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun z ↦ by positivity)
    _ ≤ max K 0 * r ^ 2 := mul_le_mul_of_nonneg_left h4 (le_max_right _ _)

/-- For `A ≥ 0`, `ε = (A |B| + 1)⁻¹` satisfies `A |B| ε² < 1`. -/
private theorem mul_abs_mul_inv_sq_lt_one {A B : ℝ} (hA : 0 ≤ A) :
    A * |B| * ((A * |B| + 1)⁻¹) ^ 2 < 1 := by
  have hpos : 0 < A * |B| + 1 := by positivity
  have hε1 : (A * |B| + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [abs_nonneg B])
  have h1 : A * |B| * (A * |B| + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    linarith
  calc A * |B| * ((A * |B| + 1)⁻¹) ^ 2 = A * |B| * (A * |B| + 1)⁻¹ * (A * |B| + 1)⁻¹ := by ring
    _ ≤ A * |B| * (A * |B| + 1)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hε1 (by positivity)
    _ < 1 := by linarith

/-- **Two cokernel elements close on a disc are close.** Let `η₁`, `η₂` be `C²` representatives
of `h₁, h₂ ∈ L²(ℂ, V)` annihilated by `D_u^*`, and let the `L²` estimate of cokernel elements on the
set `K_b` hold with constant `A`. If cutoffs `g_i` of `η_i` agree with them on `K_b` and the `L²`
norm of `g₁ - g₂` on `K_b` is at most `B ε²`, then `‖h₁ - h₂‖² ≤ max A 0 |B| ε²`. -/
private theorem norm_sub_sq_le_of_setIntegral_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {Kb : Set (ℝ × ℝ)} (hKb : MeasurableSet Kb) {A : ℝ}
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in Kb, ‖η z‖ ^ 2)
    {h₁ h₂ : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))} {η₁ η₂ g₁ g₂ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₁ : ContDiff ℝ 2 η₁) (hη₂ : ContDiff ℝ 2 η₂)
    (hae₁ : (fun z ↦ innerSL ℝ (h₁ z)) =ᵐ[volume] η₁)
    (hae₂ : (fun z ↦ innerSL ℝ (h₂ z)) =ᵐ[volume] η₂)
    (hD₁ : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η₁ z = 0)
    (hD₂ : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η₂ z = 0)
    (hg₁ : ∀ z ∈ Kb, g₁ z = η₁ z) (hg₂ : ∀ z ∈ Kb, g₂ z = η₂ z) {B ε : ℝ}
    (hsmall : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 ≤ B * ε ^ 2) :
    ‖h₁ - h₂‖ ^ 2 ≤ max A 0 * |B| * ε ^ 2 := by
  have hJu (z : ℝ × ℝ) : DifferentiableAt ℝ
      (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
    ((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero
  -- The difference `h₁ - h₂` is represented by `η₁ - η₂`, annihilated by `D_u^*`.
  have hae : (fun z ↦ innerSL ℝ ((h₁ - h₂) z)) =ᵐ[volume] η₁ - η₂ := by
    have hsub := (ae_restrict_iff' MeasurableSet.univ).1 (Lp.coeFn_sub h₁ h₂)
    filter_upwards [hsub, hae₁, hae₂] with z h1 h2 h3
    rw [h1 (mem_univ z), Pi.sub_apply, map_sub, h2, h3, Pi.sub_apply]
  obtain ⟨hdn, hdi⟩ :=
    Lp.integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq (ae_restrict_of_ae hae)
  rw [setIntegral_univ] at hdn
  replace hdi := integrableOn_univ.1 hdi
  have hdD (z : ℝ × ℝ) : ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (η₁ - η₂) z = 0 := by
    rw [floerLinearizationAdjoint_sub ((hη₁.differentiable (by norm_num)) z)
      ((hη₂.differentiable (by norm_num)) z) (hJu z), hD₁ z, hD₂ z, sub_zero]
  have hKeq : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 = ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 :=
    setIntegral_congr_fun hKb fun z hz ↦ by simp [hg₁ z hz, hg₂ z hz]
  rw [← hdn]
  calc _ ≤ max A 0 * ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 :=
        (hglob (hη₁.sub hη₂) hdD hdi).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (setIntegral_nonneg hKb fun _ _ ↦ sq_nonneg _))
    _ ≤ max A 0 * (|B| * ε ^ 2) := by
        rw [← hKeq]
        exact mul_le_mul_of_nonneg_left (hsmall.trans (mul_le_mul_of_nonneg_right
          (le_abs_self B) (sq_nonneg ε))) (le_max_right _ _)
    _ = max A 0 * |B| * ε ^ 2 := by ring

omit [FiniteDimensional ℝ V] in
/-- The weighted energy `∫ (ρ ‖g‖² + ‖∂s g‖² + ‖∂t g‖²)` of a `C¹` field `g` vanishing near every
point with `‖w‖ > a`, for a continuous weight `ρ ≤ 1`, is at most its `W^{1,2}` energy on the disc
`‖w‖ ≤ a`. -/
private theorem integral_weighted_le_setIntegral_sobolevDensity {ρ : ℝ × ℝ → ℝ}
    (hρc : Continuous ρ) (hρ1 : ∀ z, ρ z ≤ 1) {g : ℝ × ℝ → V →L[ℝ] ℝ}
    (hg : ContDiff ℝ 1 g) {a : ℝ}
    (hg0 : ∀ z, a < ‖Complex.equivRealProdCLM.symm z‖ → g =ᶠ[𝓝 z] 0) :
    ∫ z, (ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 + ‖fderiv ℝ g z (0, 1)‖ ^ 2) ≤
      ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, sobolevDensity g z := by
  have hD : IsCompact {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ a} :=
    isCompact_setOf_norm_equivRealProdCLM_symm_le _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}) fun z hz ↦ by
      have h := hg0 z (not_le.1 hz)
      simp [h.eq_of_nhds, h.fderiv_eq]]
  refine setIntegral_mono_on ?_ ((continuous_sobolevDensity hg).continuousOn.integrableOn_compact
    hD) hD.measurableSet fun z _ ↦ ?_
  · have := hg.continuous_fderiv one_ne_zero
    have := hg.continuous
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact hD
  · rw [sobolevDensity_apply]
    have := mul_le_mul_of_nonneg_right (hρ1 z) (sq_nonneg ‖g z‖)
    simp only [stdComplexLineReal, stdComplexLineImag] at *
    linarith

/-- **The weighted energy of a cut-off cokernel element.** Let `J` be `C¹` and `K_s`, `K_t` be `C²`
along a `C¹` map `u`, with `J` compatible along `u` and `‖J(z, u z)‖ ≤ B`, let `ρ ≤ 1` be a
continuous weight, and let `χ` be a cutoff with values in `[0, 1]`, vanishing off the disc
`‖w‖ < a`, whose derivative has norm at most `M`. Then there is `K` such that for
every square-integrable `C²` covector field `η` with `D_u^* η = 0` the weighted `W^{1,2}` energy of
`χ η` is at most `K ∫ ‖η‖²`. -/
private theorem exists_integral_weighted_smul_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) (hρ1 : ∀ z, ρ z ≤ 1)
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχ01 : ∀ z, χ z ∈ Icc 0 1) {M a : ℝ}
    (hχa : ∀ z, a ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) :
    ∃ K, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z, ‖η z‖ ^ 2 := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  set ν : ℝ × ℝ → ℝ := fun z ↦ ‖Complex.equivRealProdCLM.symm z‖
  obtain ⟨C', hC', hdisc⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt
      hJ hKs hKt hu (w := fun _ ↦ 1) (fun _ ↦ zero_le_one) continuous_const
      (fun _ _ ↦ one_pos) (fun z _ ↦ hc z) (show a < a + 1 by linarith)
  set c := (M * (1 + B)) ^ 2
  refine ⟨C' * (c + 1), fun η hη hD hηi ↦ ?_⟩
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g := hχ.smul hη
  have hg0 (z : ℝ × ℝ) (hz : a < ν z) : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [(isOpen_lt continuous_const
      Complex.equivRealProdCLM.symm.continuous.norm).mem_nhds hz] with w hw
    simp [g, hχa w (le_of_lt hw)]
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_setOf_norm_equivRealProdCLM_symm_le a) fun z hz ↦
      (hg0 z (not_le.1 hz)).self_of_nhds
  have hW := integral_weighted_le_setIntegral_sobolevDensity (a := a) hρc hρ1
    (hg.of_le one_le_two) hg0
  -- Since `D_u^* η = 0`, the adjoint of `χ η` only involves the derivative of `χ`.
  have hpt (z : ℝ × ℝ) : ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 ≤ c * ‖η z‖ ^ 2 := by
    have hJu : DifferentiableAt ℝ (fun w ↦ J' w (u w)) z :=
      ((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero
    have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le (Ks := Ks) (Kt := Kt)
      ((hχ.differentiable two_ne_zero) z) ((hη.differentiable two_ne_zero) z) hJu
    rw [hD z, norm_zero, mul_zero, zero_add] at hle
    have hle' : ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ≤ M * (1 + B) * ‖η z‖ :=
      hle.trans (by gcongr; exacts [(norm_nonneg _).trans (hχM z), hχM z, hB z])
    calc _ ≤ (M * (1 + B) * ‖η z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle' 2
      _ = c * ‖η z‖ ^ 2 := by ring
  have hT : ∫ z, (fun _ ↦ (1 : ℝ)) z * ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 ≤
      c * ∫ z, ‖η z‖ ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity) (hηi.const_mul _)
      (ae_of_all _ fun z ↦ by simpa using hpt z)
  have hL : ∫ z in {z | ν z ≤ a + 1}, ‖g z‖ ^ 2 ≤ ∫ z, ‖η z‖ ^ 2 := by
    refine (setIntegral_mono_on ((hg.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _)) hηi.integrableOn
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z _ ↦ ?_).trans
      (setIntegral_le_integral hηi (ae_of_all _ fun z ↦ by positivity))
    have h01 := hχ01 z
    simp only [g, Pi.pow_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [h01.1, h01.2])
  calc _ ≤ ∫ z in {z | ν z ≤ a}, sobolevDensity g z := hW
    _ ≤ C' * ((∫ z, (fun _ ↦ (1 : ℝ)) z * ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2) +
        ∫ z in {z | ν z ≤ a + 1}, ‖g z‖ ^ 2) := hdisc hg hgc
    _ ≤ C' * (c * (∫ z, ‖η z‖ ^ 2) + ∫ z, ‖η z‖ ^ 2) := by gcongr
    _ = C' * (c + 1) * ∫ z, ‖η z‖ ^ 2 := by ring

/-- **A cutoff of a disc and the weighted energy of cut-off cokernel elements.** Under the
hypotheses of `exists_integral_weighted_smul_le`, for every `b` there are a `C²` cutoff `χ` with
values in `[0, 1]`, equal to `1` on the disc `‖w‖ ≤ b` and vanishing on `‖w‖ ≥ a`, and a constant
`K` such that for every square-integrable `C²` covector field `η` with `D_u^* η = 0` the weighted
`W^{1,2}` energy of `χ η` is at most `K ∫ ‖η‖²`. -/
private theorem exists_cutoff_integral_weighted_smul_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ) (hρ1 : ∀ z, ρ z ≤ 1) (b : ℝ) :
    ∃ (χ : ℝ × ℝ → ℝ) (a K : ℝ), ContDiff ℝ 2 χ ∧
      (∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ b → χ z = 1) ∧
      (∀ z, a ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0) ∧
      ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
        (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
        ∫ z, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z, ‖η z‖ ^ 2 := by
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, -, -, hχM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (lt_max_of_lt_right one_pos : 0 < max b 1)
  have hχ2 : ContDiff ℝ 2 χ := hχs.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_integral_weighted_smul_le ω hJ hKs hKt hu hc hB hρc hρ1 hχ2 hχ01
    hχ0 hχM
  exact ⟨χ, _, K, hχ2, fun z hz ↦ hχ1 z (hz.trans (le_max_left _ _)), hχ0, hK⟩

/-- **Cokernel elements are regular.** An element `h ∈ L²(ℂ, V)` orthogonal to the range of `D_u`
agrees almost everywhere on the plane with a `C²` covector field `η` with `D_u^* η = 0`. This is
`exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero` on the whole plane. -/
private theorem exists_contDiff_ae_eq_of_mem_orthogonal_range (ω : SymplecticForm V)
    {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight univ ρ)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict univ))
    {h : Lp V 2 (volume.restrict (univ : Set (ℝ × ℝ)))}
    (hh : h ∈ (ω.floerConformalSobolevOperator univ ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ) :
    ∃ η : ℝ × ℝ → V →L[ℝ] ℝ, ContDiff ℝ 2 η ∧ (fun z ↦ innerSL ℝ (h z)) =ᵐ[volume] η ∧
      ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0 := by
  obtain ⟨η, hη, hae, hD⟩ := ω.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero
    (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) (u := u) hρ
    (fun z _ ↦ hJ z) (fun z _ ↦ (J z (u z)).toContinuousLinearMap_mul_self)
    (fun z _ ↦ hKs z) (fun z _ ↦ hKt z) (fun z _ ↦ hu.contDiffAt) hM hh
  exact ⟨η, contDiffOn_univ.1 hη, ((ae_restrict_iff' MeasurableSet.univ).1 hae).mono
    fun z hz ↦ hz (mem_univ z), fun z ↦ hD z (mem_univ z)⟩

/-- **Peetre's argument for the cokernel of the linearized operator on the plane.** Let `ρ ≤ 1` be
a conformal weight on the plane, let `J` be `C³` and `K_s`, `K_t` be `C⁴` at the points `(z, u z)`
along a `C³` map `u`, with `J` compatible along `u` and `‖J(z, u z)‖ ≤ B`, and let the coefficient
field of `D_u` on conformal jets be essentially bounded. Suppose that every square-integrable `C²`
covector field `η` with `D_u^* η = 0` satisfies `∫ ‖η‖² ≤ A ∫_{|w| ≤ b} ‖η‖²`. Then the
orthogonal complement of the range of the realization `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` is
finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_integral_norm_sq_le
    (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight univ ρ) (hρ1 : ∀ z, ρ z ≤ 1)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {B : ℝ}
    (hB : ∀ z, ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict univ))
    {A b : ℝ}
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}, ‖η z‖ ^ 2) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  have hJ1 (z : ℝ × ℝ) := (hJ z).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  set Kb := {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ b}
  have hKb : IsCompact Kb := isCompact_setOf_norm_equivRealProdCLM_symm_le b
  -- The constants: the cutoff, the weighted energy of cut-off cokernel elements, and the compact
  -- restriction to the disc `Kb`.
  obtain ⟨χ, a, K, hχ2, hχ1, hχ0, hK⟩ := exists_cutoff_integral_weighted_smul_le ω hJ1
    (fun z ↦ (hKs z).of_le (by norm_num)) (fun z ↦ (hKt z).of_le (by norm_num))
    (hu.of_le (by norm_num)) hc hB (continuousOn_univ.1 hρ.continuousOn) hρ1 b
  obtain ⟨B', hB'⟩ :=
    exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq (V := V →L[ℝ] ℝ) hρ hKb
      (subset_univ _)
  have hcpt := isCompactOperator_restrictWeightedValue_comp_subtypeL (V := V →L[ℝ] ℝ) hρ hKb
    (subset_univ _)
  -- An infinite-dimensional cokernel contains vectors of norm at most `Rr` at mutual distance ≥ 1.
  by_contra hfin
  obtain ⟨Rr, f, -, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
  choose η hηs hηae hηD using fun k ↦
    exists_contDiff_ae_eq_of_mem_orthogonal_range ω hρ hJ hKs hKt hu hM (f k).property
  -- The jets of their cut-offs are bounded in `W^{1,2}`.
  set g : ℕ → ℝ × ℝ → V →L[ℝ] ℝ := fun k z ↦ χ z • η k z
  have hg (k : ℕ) : ContDiff ℝ 2 (g k) := hχ2.smul (hηs k)
  have hgT (k : ℕ) : g k ∈ testSection (V →L[ℝ] ℝ) univ := by
    refine mem_testSection_iff.2 ⟨hg k, HasCompactSupport.intro
      (isCompact_setOf_norm_equivRealProdCLM_symm_le a) fun z hz ↦ ?_, subset_univ _⟩
    simp [g, hχ0 z (not_le.1 hz).le]
  set x : ℕ → H1 (V →L[ℝ] ℝ) univ ρ := fun k ↦ ⟨(memLp_jet hρ (hgT k)).toLp (jet ρ (g k)),
    jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ (hgT k))⟩
  have hxb (k : ℕ) : ‖x k‖ ≤ √(max K 0 * Rr ^ 2) := by
    rw [← Submodule.norm_coe]
    exact norm_toLp_jet_le hρ (hηae k) (hgT k) (by rw [Submodule.norm_coe]; exact hfR k)
      (hK (hηs k) (hηD k))
  -- By Rellich's theorem two of them are close on the disc, hence close everywhere.
  obtain ⟨k, l, hkl, hdist⟩ := hcpt.exists_dist_lt_of_norm_le hxb
    (by positivity : 0 < (max A 0 * |B'| + 1)⁻¹)
  rw [dist_eq_norm, ← map_sub] at hdist
  have hjet := toLp_jet_sub_ae_eq hρ (hgT k) (hgT l)
  have hgη (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Kb) : g k z = η k z := by
    simp [g, hχ1 z hz]
  have hle := norm_sub_sq_le_of_setIntegral_le ω hJ1 (hu.of_le (by norm_num)) hKb.measurableSet
    hglob (hηs k) (hηs l) (hηae k) (hηae l) (hηD k) (hηD l) (hgη k) (hgη l)
    (B := |B'|) ((hB' ((hg k).continuous.sub (hg l).continuous).continuousOn hjet).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self B') (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist.le 2) (abs_nonneg _))))
  rw [← Submodule.coe_sub, Submodule.norm_coe, abs_abs] at hle
  have := hsep hkl.ne
  nlinarith [mul_abs_mul_inv_sq_lt_one (B := B') (le_max_right A 0)]

end TauCeti.SymplecticForm
