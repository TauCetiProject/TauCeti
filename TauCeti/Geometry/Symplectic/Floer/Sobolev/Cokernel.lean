/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint

import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.MeasureTheory.Function.L2Space.InnerSL

/-!
# Finite cokernels of the linearized operator

Let `ρ` be a conformal weight on an open set `U` of the plane `ℂ ≅ ℝ × ℝ`, and let
`D_u : W^{1,2}_0(U, V) → L²(U, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator`) of the linearized Floer operator along a
map `u` into a finite-dimensional symplectic inner product space `(V, ω)`. The weights in use are
the cylindrical weight `(1 + |w|²)⁻¹` of a PSS plane on the whole plane, the weight
`(1 + |w|²)⁻²` of the round sphere, a plane with a point at infinity, and the cylindrical weight of
a sphere with moving input ends on the plane minus the input punctures.

This file proves Peetre's argument for the finiteness of the cokernel of `D_u`, given the one
estimate that depends on the geometry of the ends: an `L²` bound of cokernel elements by their
`L²` norm on a compact subset `K_b` of `U`. Precisely, suppose that every covector field `η`, `C²`
on `U`, with `D_u^* η = 0` on `U` and `‖η‖²` integrable on `U` satisfies
`∫_U ‖η‖² ≤ A ∫_{K_b} ‖η‖²`. Then the orthogonal complement of the range of `D_u` is
finite-dimensional
(`finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_setIntegral_norm_sq_le`, in
the namespace `TauCeti.SymplecticForm`).

* **Cokernel elements are regular.** An element `h ∈ L²(U, V)` orthogonal to the range of `D_u`
  agrees almost everywhere on `U` with a covector field `η`, `C²` on `U`, with `D_u^* η = 0` there
  (`TauCeti.SymplecticForm.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`).
* **Cut-off cokernel elements are bounded in `W^{1,2}`.** For a cutoff `χ` equal to `1` on `K_b`
  and supported in a compact subset `L` of `U`, the estimate of the formal adjoint on compact sets,
  `exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add` in
  the namespace `TauCeti.SymplecticForm`, bounds the weighted `W^{1,2}` norm of `χ η` by a
  constant times `∫_U ‖η‖²`, since `D_u^* (χ η)` only involves the derivative of `χ`, and the
  weight is bounded on `L`.
* **Peetre's argument.** By Rellich's theorem
  (`TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`), the
  restrictions of the cut-off cokernel elements of norm at most `R` to `K_b` form a compact
  family. An infinite-dimensional cokernel would contain a sequence of vectors of norm at most `R`
  at mutual distance at least one, two of which are close on `K_b`, hence everywhere by the
  hypothesis.

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
  {U : Set (ℝ × ℝ)}

omit [FiniteDimensional ℝ V] in
/-- The jets in `W^{1,2}` of the cut-offs `χ η` of cokernel elements are bounded: if the weighted
energy of `χ η` is at most `K ∫_U ‖η‖²`, `η` represents `h ∈ L²(U, V)` and `‖h‖ ≤ r`, then the
class of the jet of `χ η` has norm at most `√(max K 0 r²)`. -/
private theorem norm_toLp_jet_le {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ)
    {h : Lp V 2 (volume.restrict U)}
    {η g : ℝ × ℝ → V →L[ℝ] ℝ} (hηae : (fun z ↦ innerSL ℝ (h z)) =ᵐ[volume.restrict U] η)
    (hg : g ∈ testSection (V →L[ℝ] ℝ) U) {K r : ℝ} (hr : ‖h‖ ≤ r)
    (hK : IntegrableOn (fun z ↦ ‖η z‖ ^ 2) U →
      ∫ z in U, (ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 + ‖fderiv ℝ g z (0, 1)‖ ^ 2) ≤
        K * ∫ z in U, ‖η z‖ ^ 2) :
    ‖(memLp_jet hρ hg).toLp (jet ρ g)‖ ≤ √(max K 0 * r ^ 2) := by
  obtain ⟨hηn, hηi⟩ := Lp.integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq hηae
  have h1 := sq_norm_le_integral hρ hg (memLp_jet hρ hg).coeFn_toLp
  have h4 : ∫ z in U, ‖η z‖ ^ 2 ≤ r ^ 2 := by
    rw [hηn]
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  refine Real.le_sqrt_of_sq_le ((h1.trans (hK hηi)).trans ?_)
  calc K * ∫ z in U, ‖η z‖ ^ 2 ≤ max K 0 * ∫ z in U, ‖η z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (setIntegral_nonneg_of_ae_restrict
          (ae_of_all _ fun z ↦ by positivity))
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

/-- **Two cokernel elements close on `K_b` are close.** Let `η₁`, `η₂` be representatives, `C²` on
the open set `U`, of `h₁, h₂ ∈ L²(U, V)` annihilated by `D_u^*` on `U`, and let the `L²` estimate
of cokernel elements on the set `K_b` hold with constant `A`. If cutoffs `g_i` of `η_i` agree with
them on `K_b` and the `L²` norm of `g₁ - g₂` on `K_b` is at most `B ε²`, then
`‖h₁ - h₂‖² ≤ max A 0 |B| ε²`. -/
private theorem norm_sub_sq_le_of_setIntegral_le (ω : SymplecticForm V) (hU : IsOpen U)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z) {Kb : Set (ℝ × ℝ)} (hKb : MeasurableSet Kb) {A : ℝ}
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiffOn ℝ 2 η U →
      (∀ z ∈ U, ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z = 0) →
      IntegrableOn (fun z ↦ ‖η z‖ ^ 2) U →
      ∫ z in U, ‖η z‖ ^ 2 ≤ A * ∫ z in Kb, ‖η z‖ ^ 2)
    {h₁ h₂ : Lp V 2 (volume.restrict U)} {η₁ η₂ g₁ g₂ : ℝ × ℝ → V →L[ℝ] ℝ}
    (hη₁ : ContDiffOn ℝ 2 η₁ U) (hη₂ : ContDiffOn ℝ 2 η₂ U)
    (hae₁ : (fun z ↦ innerSL ℝ (h₁ z)) =ᵐ[volume.restrict U] η₁)
    (hae₂ : (fun z ↦ innerSL ℝ (h₂ z)) =ᵐ[volume.restrict U] η₂)
    (hD₁ : ∀ z ∈ U, ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η₁ z = 0)
    (hD₂ : ∀ z ∈ U, ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η₂ z = 0)
    (hg₁ : ∀ z ∈ Kb, g₁ z = η₁ z) (hg₂ : ∀ z ∈ Kb, g₂ z = η₂ z) {B ε : ℝ}
    (hsmall : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 ≤ B * ε ^ 2) :
    ‖h₁ - h₂‖ ^ 2 ≤ max A 0 * |B| * ε ^ 2 := by
  -- The difference `h₁ - h₂` is represented by `η₁ - η₂`, annihilated by `D_u^*`.
  have hae : (fun z ↦ innerSL ℝ ((h₁ - h₂) z)) =ᵐ[volume.restrict U] η₁ - η₂ := by
    filter_upwards [Lp.coeFn_sub h₁ h₂, hae₁, hae₂] with z h1 h2 h3
    rw [h1, Pi.sub_apply, map_sub, h2, h3, Pi.sub_apply]
  obtain ⟨hdn, hdi⟩ := Lp.integral_norm_sq_eq_and_integrable_of_innerSL_ae_eq hae
  have hdD (z : ℝ × ℝ) (hz : z ∈ U) : ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (η₁ - η₂) z = 0 := by
    have hJu : DifferentiableAt ℝ (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
      ((hJ z hz).comp₂ contDiffAt_id (hu z hz)).differentiableAt one_ne_zero
    rw [floerLinearizationAdjoint_sub
      ((hη₁.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz))
      ((hη₂.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hz)) hJu, hD₁ z hz,
      hD₂ z hz, sub_zero]
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

/-- **The weighted energy of a cut-off cokernel element.** Let `J` be `C¹` and `K_s`, `K_t` be
`C²` along a map `u`, `C¹` on the open set `U`, with `J` compatible along `u` there, let `ρ` be a
weight on `U`, and let `χ` be a `C²` cutoff with values in `[0, 1]` whose support is a compact
subset `L` of `U` and whose derivative has norm at most `M`. Then there is `K` such that for every
covector field `η`, `C²` on `U`, with `D_u^* η = 0` on `U` and `‖η‖²` integrable on `U`, the
weighted `W^{1,2}` energy of `χ η` is at most `K ∫_U ‖η‖²`. -/
private theorem exists_integral_weighted_smul_le (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ U, ω.Compatible (J z (u z)))
    {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχ01 : ∀ z, χ z ∈ Icc 0 1) {L : Set (ℝ × ℝ)}
    (hL : IsCompact L) (hLU : L ⊆ U) (hχL : tsupport χ ⊆ L) {M : ℝ}
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) :
    ∃ K, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiffOn ℝ 2 η U →
      (∀ z ∈ U, ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z = 0) →
      IntegrableOn (fun z ↦ ‖η z‖ ^ 2) U →
      ∫ z in U, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z in U, ‖η z‖ ^ 2 := by
  set J' : ℝ × ℝ → V → V →L[ℝ] V := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap
  have hJu (z : ℝ × ℝ) (hz : z ∈ U) : ContinuousAt (fun w ↦ J' w (u w)) z :=
    ((hJ z hz).comp₂ contDiffAt_id (hu z hz)).continuousAt
  -- The weight and `J` along `u` are bounded on the compact set `L`.
  obtain ⟨Rρ, hRρ⟩ := hL.exists_bound_of_continuousOn (hρ.continuousOn.mono hLU)
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn fun z hz ↦ (hJu z (hLU hz)).continuousWithinAt
  obtain ⟨C', hC', hloc⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_setIntegral_floerLinearizationAdjoint_add hL
      (fun z hz ↦ hJ z (hLU hz)) (fun z hz ↦ hKs z (hLU hz)) (fun z hz ↦ hKt z (hLU hz))
      (fun z hz ↦ hu z (hLU hz)) (fun z hz ↦ hc z (hLU hz))
  set R := max Rρ 0 + 1
  set c := (M * (1 + B)) ^ 2
  refine ⟨R * (C' * (c + 1)), fun η hη hD hηi ↦ ?_⟩
  set g : ℝ × ℝ → V →L[ℝ] ℝ := fun z ↦ χ z • η z
  have hg : ContDiff ℝ 2 g :=
    hη.contDiff_smul_of_tsupport_subset hρ.isOpen hχ.contDiffOn (hχL.trans hLU)
  have hgL : tsupport g ⊆ L := (tsupport_smul_subset_left χ η).trans hχL
  -- The weighted energy of `g` lives on `L`, where the weight is at most `max Rρ 0`.
  have hW : ∫ z in U, (ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 +
      ‖fderiv ℝ g z (0, 1)‖ ^ 2) ≤ R * ∫ z in L, sobolevDensity g z := by
    have hg1 := hg.of_le one_le_two
    have := hg1.continuous_fderiv one_ne_zero
    have := hg1.continuous
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hρ.isOpen.measurableSet hLU
      fun z hz ↦ by
        have hz' : z ∉ tsupport g := fun h ↦ hz.2 (hgL h)
        simp [image_eq_zero_of_notMem_tsupport hz', fderiv_of_notMem_tsupport ℝ hz']]
    refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
      (setIntegral_nonneg hL.measurableSet fun z _ ↦ sobolevDensity_nonneg g z))).1 ?_
    have hcont : ContinuousOn (fun z ↦ ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 +
        ‖fderiv ℝ g z (0, 1)‖ ^ 2) L := by
      refine (((hρ.continuousOn.mono hLU).mul ?_).add ?_).add ?_ <;> fun_prop
    rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_compact hL)
      ((ae_restrict_iff' hL.measurableSet).2 (ae_of_all _ fun z hz ↦
        add_nonneg (add_nonneg (mul_nonneg (hρ.pos z (hLU hz)).le (sq_nonneg _)) (sq_nonneg _))
          (sq_nonneg _)))]
    exact setLIntegral_le_ofReal_mul_setIntegral_sobolevDensity hL (le_max_right _ _)
      (fun z hz ↦ (le_abs_self _).trans ((hRρ z hz).trans (le_max_left _ _))) hg1
  -- Since `D_u^* η = 0`, the adjoint of `χ η` only involves the derivative of `χ`.
  have hpt (z : ℝ × ℝ) (hz : z ∈ L) :
      ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 + ‖g z‖ ^ 2 ≤ (c + 1) * ‖η z‖ ^ 2 := by
    have hzU := hLU hz
    have hJd : DifferentiableAt ℝ (fun w ↦ J' w (u w)) z :=
      ((hJ z hzU).comp₂ contDiffAt_id (hu z hzU)).differentiableAt one_ne_zero
    have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero (Ks := Ks) (Kt := Kt)
      ((hχ.differentiable two_ne_zero) z)
      ((hη.differentiableOn two_ne_zero).differentiableAt (hρ.isOpen.mem_nhds hzU)) hJd (hD z hzU)
    have hle' : ‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ≤ M * (1 + B) * ‖η z‖ :=
      hle.trans (by gcongr; exacts [(norm_nonneg _).trans (hχM z), hχM z, hB z hz])
    have hgη : ‖g z‖ ≤ ‖η z‖ := by
      simp only [g, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ01 z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχ01 z).2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hle' 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hgη 2
    calc _ ≤ (M * (1 + B) * ‖η z‖) ^ 2 + ‖η z‖ ^ 2 := add_le_add h1 h2
      _ = (c + 1) * ‖η z‖ ^ 2 := by ring
  have hT : ∫ z in L, (‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 + ‖g z‖ ^ 2) ≤
      (c + 1) * ∫ z in U, ‖η z‖ ^ 2 := by
    rw [← integral_const_mul]
    refine (integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity)
      ((hηi.mono_set hLU).const_mul _) ((ae_restrict_iff' hL.measurableSet).2
        (ae_of_all _ hpt))).trans ?_
    exact setIntegral_mono_set (hηi.const_mul _) (ae_of_all _ fun z ↦ by positivity)
      (ae_of_all _ hLU)
  calc _ ≤ R * ∫ z in L, sobolevDensity g z := hW
    _ ≤ R * (C' * ∫ z in L, (‖ω.floerLinearizationAdjoint J' Ks Kt u g z‖ ^ 2 + ‖g z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hloc hg hgL) (by positivity)
    _ ≤ R * (C' * ((c + 1) * ∫ z in U, ‖η z‖ ^ 2)) := by gcongr
    _ = R * (C' * (c + 1)) * ∫ z in U, ‖η z‖ ^ 2 := by ring

/-- **A cutoff of a compact set and the weighted energy of cut-off cokernel elements.** Under the
hypotheses of `exists_integral_weighted_smul_le`, for every compact subset `K_b` of `U` there are
a `C²` cutoff `χ` with values in `[0, 1]`, equal to `1` on `K_b`, with compact support in `U`, and
a constant `K` such that for every covector field `η`, `C²` on `U`, with `D_u^* η = 0` on `U` and
`‖η‖²` integrable on `U`, the weighted `W^{1,2}` energy of `χ η` is at most `K ∫_U ‖η‖²`. -/
private theorem exists_cutoff_integral_weighted_smul_le (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ}
    (hρ : IsWeight U ρ)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 1 u z)
    (hc : ∀ z ∈ U, ω.Compatible (J z (u z))) {Kb : Set (ℝ × ℝ)} (hKb : IsCompact Kb)
    (hKbU : Kb ⊆ U) :
    ∃ (χ : ℝ × ℝ → ℝ) (K : ℝ), ContDiff ℝ 2 χ ∧ (∀ z ∈ Kb, χ z = 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiffOn ℝ 2 η U →
        (∀ z ∈ U, ω.floerLinearizationAdjoint
          (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z = 0) →
        IntegrableOn (fun z ↦ ‖η z‖ ^ 2) U →
        ∫ z in U, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K * ∫ z in U, ‖η z‖ ^ 2 := by
  obtain ⟨χ, hχs, hχr, hχ1, hχc, hχU⟩ := hKb.exists_contDiff_cutoff hρ.isOpen hKbU
  have hχ2 : ContDiff ℝ 2 χ := hχs.of_le (by simp)
  obtain ⟨M, hM⟩ := (hχs.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hχc.fderiv ℝ).norm
  obtain ⟨K, hK⟩ := exists_integral_weighted_smul_le ω hρ hJ hKs hKt hu hc hχ2
    (fun z ↦ hχr (mem_range_self z)) hχc.isCompact hχU subset_rfl (M := M)
    fun z ↦ hM ⟨z, rfl⟩
  exact ⟨χ, K, hχ2, fun z hz ↦ interior_subset (hχ1 hz), hχc, hχU, hK⟩

/-- **Peetre's argument for the cokernel of the linearized operator.** Let `ρ` be a conformal
weight on an open set `U` of the plane, let `J` be `C³` and `K_s`, `K_t` be `C⁴` at the points
`(z, u z)` along a map `u` that is `C³` on `U`, with `J` compatible along `u` on `U`, and let the
coefficient field of `D_u` on conformal jets be essentially bounded on `U`. Suppose that every
covector field `η`, `C²` on `U`, with `D_u^* η = 0` on `U` and `‖η‖²` integrable on `U` satisfies
`∫_U ‖η‖² ≤ A ∫_{K_b} ‖η‖²` for a compact subset `K_b` of `U`. Then the orthogonal complement of
the range of the realization `D_u : W^{1,2}_0(U, V) → L²(U, V)` is finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_setIntegral_norm_sq_le
    (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight U ρ)
    (hJ : ∀ z ∈ U, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z ∈ U, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z ∈ U, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ∀ z ∈ U, ContDiffAt ℝ 3 u z)
    (hc : ∀ z ∈ U, ω.Compatible (J z (u z)))
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict U))
    {A : ℝ} {Kb : Set (ℝ × ℝ)} (hKb : IsCompact Kb) (hKbU : Kb ⊆ U)
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiffOn ℝ 2 η U →
      (∀ z ∈ U, ω.floerLinearizationAdjoint
        (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u η z = 0) →
      IntegrableOn (fun z ↦ ‖η z‖ ^ 2) U →
      ∫ z in U, ‖η z‖ ^ 2 ≤ A * ∫ z in Kb, ‖η z‖ ^ 2) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator U ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  have hJ1 (z : ℝ × ℝ) (hz : z ∈ U) := (hJ z hz).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hu1 (z : ℝ × ℝ) (hz : z ∈ U) := (hu z hz).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  -- The constants: the cutoff, the weighted energy of cut-off cokernel elements, and the compact
  -- restriction to `Kb`.
  obtain ⟨χ, K, hχ2, hχ1, hχc, hχU, hK⟩ := exists_cutoff_integral_weighted_smul_le ω hρ hJ1
    (fun z hz ↦ (hKs z hz).of_le (by norm_num)) (fun z hz ↦ (hKt z hz).of_le (by norm_num))
    hu1 hc hKb hKbU
  obtain ⟨B', hB'⟩ :=
    exists_setIntegral_norm_sq_le_mul_norm_restrictWeightedValue_sq (V := V →L[ℝ] ℝ) hρ hKb hKbU
  have hcpt := isCompactOperator_restrictWeightedValue_comp_subtypeL (V := V →L[ℝ] ℝ) hρ hKb hKbU
  -- An infinite-dimensional cokernel contains vectors of norm at most `Rr` at mutual distance ≥ 1.
  by_contra hfin
  obtain ⟨Rr, f, -, hfR, hsep⟩ := exists_seq_norm_le_one_le_norm_sub hfin
  choose η hηs hηae hηD using fun k ↦
    ω.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero
      (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) (u := u) hρ hJ
      (fun z _ ↦ (J z (u z)).toContinuousLinearMap_mul_self) hKs hKt hu hM (f k).property
  -- The jets of their cut-offs are bounded in `W^{1,2}`.
  set g : ℕ → ℝ × ℝ → V →L[ℝ] ℝ := fun k z ↦ χ z • η k z
  have hg (k : ℕ) : ContDiff ℝ 2 (g k) :=
    (hηs k).contDiff_smul_of_tsupport_subset hρ.isOpen hχ2.contDiffOn hχU
  have hgT (k : ℕ) : g k ∈ testSection (V →L[ℝ] ℝ) U :=
    mem_testSection_iff.2 ⟨hg k, hχc.smul_right, (tsupport_smul_subset_left _ _).trans hχU⟩
  set x : ℕ → H1 (V →L[ℝ] ℝ) U ρ := fun k ↦ ⟨(memLp_jet hρ (hgT k)).toLp (jet ρ (g k)),
    jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ (hgT k))⟩
  have hxb (k : ℕ) : ‖x k‖ ≤ √(max K 0 * Rr ^ 2) := by
    rw [← Submodule.norm_coe]
    exact norm_toLp_jet_le hρ (hηae k) (hgT k) (by rw [Submodule.norm_coe]; exact hfR k)
      (hK (hηs k) (hηD k))
  -- By Rellich's theorem two of them are close on `Kb`, hence close everywhere.
  obtain ⟨k, l, hkl, hdist⟩ := hcpt.exists_dist_lt_of_norm_le hxb
    (by positivity : 0 < (max A 0 * |B'| + 1)⁻¹)
  rw [dist_eq_norm, ← map_sub] at hdist
  have hjet := toLp_jet_sub_ae_eq hρ (hgT k) (hgT l)
  have hgη (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Kb) : g k z = η k z := by
    simp [g, hχ1 z hz]
  have hle := norm_sub_sq_le_of_setIntegral_le ω hρ.isOpen hJ1 hu1 hKb.measurableSet
    hglob (hηs k) (hηs l) (hηae k) (hηae l) (hηD k) (hηD l) (hgη k) (hgη l)
    (B := |B'|) ((hB' ((hg k).continuous.sub (hg l).continuous).continuousOn hjet).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self B') (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist.le 2) (abs_nonneg _))))
  rw [← Submodule.coe_sub, Submodule.norm_coe, abs_abs] at hle
  have := hsep hkl.ne
  nlinarith [mul_abs_mul_inv_sq_lt_one (B := B') (le_max_right A 0)]

end TauCeti.SymplecticForm
