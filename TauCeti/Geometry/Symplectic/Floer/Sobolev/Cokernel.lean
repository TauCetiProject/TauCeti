/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Conformal
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.Analysis.Calculus.BumpFunction.LipschitzCutoff
import TauCeti.Analysis.Complex.EquivRealProd
import TauCeti.Geometry.Symplectic.Floer.SemiFredholm.Adjoint
import TauCeti.Geometry.Symplectic.Floer.Transversality.Conformal
import TauCeti.MeasureTheory.Function.L2Space.Pairing
import TauCeti.Topology.Constructions.SumProd

/-!
# Peetre's argument for the cokernel of the linearized Floer operator

Let `D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` be the realization
(`TauCeti.SymplecticForm.floerConformalSobolevOperator` on the whole plane, for a conformal weight
`ρ`) of the linearized Floer operator of data `(J, K_s, K_t)` along a map `u`. Its cokernel is the
orthogonal complement of its range. When the data are regular enough, every element of it is
represented by a `C²` covector field `η` with `D_u^* η = 0` for the formal adjoint `D_u^*`
(`TauCeti.SymplecticForm.exists_contDiffOn_ae_eq_forall_floerLinearizationAdjoint_eq_zero`). This
file shows that the cokernel is finite-dimensional as soon as the `L²` norm of these covector fields
lives on a compact set `K`: `∫ ‖η‖² ≤ A ∫_K ‖η‖²`
(`TauCeti.SymplecticForm.finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_le`).

The proof is Peetre's argument. Fix a cutoff `χ` equal to `1` on `K`. Since `D_u^* η = 0`, the
adjoint of `χ η` only involves the derivative of `χ`, so the estimate of `D_u^*` on discs
(`exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt`,
in the namespace `TauCeti.SymplecticForm`) bounds the `W^{1,2}` norm of `χ η` by `∫ ‖η‖²`. An
infinite-dimensional cokernel would contain a bounded sequence `h_k` whose members are at mutual
distance at least one. The jets of the cut-off fields `χ η_k` are then bounded in `W^{1,2}`, so
by Rellich's theorem their restrictions to `K` have a Cauchy subsequence
(`TauCeti.ConformalSobolev.isCompactOperator_restrictWeightedValue_comp_subtypeL`). Two members
close on `K` are close everywhere, by the estimate on `K` applied to their difference, which is
again annihilated by `D_u^*`.

The estimate on `K` is where the geometry of the domain enters: on a PSS plane it comes from the
semi-Fredholm estimate of `D_u^*` on the cylindrical end
(`TauCeti.Geometry.Symplectic.Floer.Plane.Fredholm`), on the Riemann sphere from its estimate in
the chart at infinity (`TauCeti.Geometry.Symplectic.Floer.Sobolev.Sphere.Fredholm`).

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Appendices B and C, on the formal adjoint and the Fredholm
  property of real Cauchy–Riemann operators.
-/

public section

open Set Function Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology

namespace TauCeti

namespace SymplecticForm

open Floer ConformalSobolev

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

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
  obtain ⟨hηn, hηi⟩ := Lp.integral_norm_sq_eq_and_integrable_of_ae_eq (ae_restrict_of_ae hηae)
  rw [setIntegral_univ] at hηn
  rw [Measure.restrict_univ] at hηi
  have h1 := sq_norm_le_integral hρ hg (memLp_jet hρ hg).coeFn_toLp
  rw [setIntegral_univ] at h1
  have h4 : ∫ z, ‖η z‖ ^ 2 ≤ r ^ 2 := by
    rw [hηn]
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  refine Real.le_sqrt_of_sq_le ((h1.trans (hK hηi)).trans ?_)
  calc K * ∫ z, ‖η z‖ ^ 2 ≤ max K 0 * ∫ z, ‖η z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun z ↦ by positivity)
    _ ≤ max K 0 * r ^ 2 := mul_le_mul_of_nonneg_left h4 (le_max_right _ _)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] in
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

variable [FiniteDimensional ℝ V] {J : ℝ × ℝ → V → AlmostComplexStructure V}
  {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V}

/-- **Two cokernel elements close on `K` are close.** Let `η₁`, `η₂` be `C²` representatives
of `h₁, h₂ ∈ L²(ℂ, V)` annihilated by `D_u^*`, and let the `L²` estimate of cokernel elements on
`K` hold with constant `A`. If cutoffs `g_i` of `η_i` agree with them on `K` and the `L²` norm of
`g₁ - g₂` on `K` is at most `B ε²`, then `‖h₁ - h₂‖² ≤ A |B| ε²`. -/
private theorem norm_sub_sq_le_of_setIntegral_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {Kb : Set (ℝ × ℝ)} (hKb : MeasurableSet Kb) {A : ℝ} (hA : 0 ≤ A)
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
    ‖h₁ - h₂‖ ^ 2 ≤ A * |B| * ε ^ 2 := by
  have hJu (z : ℝ × ℝ) : DifferentiableAt ℝ
      (fun w ↦ (J w (u w)).toLinearMap.toContinuousLinearMap) z :=
    ((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero
  -- The difference `h₁ - h₂` is represented by `η₁ - η₂`, annihilated by `D_u^*`.
  have hae : (fun z ↦ innerSL ℝ ((h₁ - h₂) z)) =ᵐ[volume] η₁ - η₂ := by
    have hsub := (ae_restrict_iff' MeasurableSet.univ).1 (Lp.coeFn_sub h₁ h₂)
    filter_upwards [hsub, hae₁, hae₂] with z h1 h2 h3
    rw [h1 (mem_univ z), Pi.sub_apply, map_sub, h2, h3, Pi.sub_apply]
  obtain ⟨hdn, hdi⟩ := Lp.integral_norm_sq_eq_and_integrable_of_ae_eq (ae_restrict_of_ae hae)
  rw [setIntegral_univ] at hdn
  rw [Measure.restrict_univ] at hdi
  have hdD (z : ℝ × ℝ) : ω.floerLinearizationAdjoint
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u (η₁ - η₂) z = 0 := by
    rw [floerLinearizationAdjoint_sub ((hη₁.differentiable (by norm_num)) z)
      ((hη₂.differentiable (by norm_num)) z) (hJu z), hD₁ z, hD₂ z, sub_zero]
  have hKeq : ∫ z in Kb, ‖(g₁ - g₂) z‖ ^ 2 = ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 :=
    setIntegral_congr_fun hKb fun z hz ↦ by simp [hg₁ z hz, hg₂ z hz]
  rw [← hdn]
  calc _ ≤ A * ∫ z in Kb, ‖(η₁ - η₂) z‖ ^ 2 := hglob (hη₁.sub hη₂) hdD hdi
    _ ≤ A * (|B| * ε ^ 2) := by
        rw [← hKeq]
        exact mul_le_mul_of_nonneg_left (hsmall.trans (mul_le_mul_of_nonneg_right
          (le_abs_self B) (sq_nonneg ε))) hA
    _ = A * |B| * ε ^ 2 := by ring

omit [FiniteDimensional ℝ V] in
/-- The weighted energy `∫ (ρ ‖g‖² + ‖∂s g‖² + ‖∂t g‖²)` of a `C¹` field `g` vanishing near every
point with `|w| > a`, for a weight `ρ ≤ m` on the disc `|w| ≤ a` with `1 ≤ m`, is at most `m` times
its `W^{1,2}` energy on that disc. -/
private theorem integral_weighted_le_mul_setIntegral_sobolevDensity {ρ : ℝ × ℝ → ℝ}
    (hρc : Continuous ρ) {g : ℝ × ℝ → V →L[ℝ] ℝ} (hg : ContDiff ℝ 1 g) {a m : ℝ} (hm : 1 ≤ m)
    (hρm : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ a → ρ z ≤ m)
    (hg0 : ∀ z, a < ‖Complex.equivRealProdCLM.symm z‖ → g =ᶠ[𝓝 z] 0) :
    ∫ z, (ρ z * ‖g z‖ ^ 2 + ‖fderiv ℝ g z (1, 0)‖ ^ 2 + ‖fderiv ℝ g z (0, 1)‖ ^ 2) ≤
      m * ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}, sobolevDensity g z := by
  have hD : IsCompact {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ a} :=
    isCompact_setOf_norm_equivRealProdCLM_symm_le _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a}) fun z hz ↦ by
      have h := hg0 z (not_le.1 hz)
      simp [h.eq_of_nhds, h.fderiv_eq], ← integral_const_mul]
  refine setIntegral_mono_on ?_
    (((continuous_sobolevDensity hg).const_smul m).continuousOn.integrableOn_compact hD)
    hD.measurableSet fun z hz ↦ ?_
  · have := hg.continuous_fderiv one_ne_zero
    have := hg.continuous
    exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact hD
  · have hρ := mul_le_mul_of_nonneg_right (hρm z hz) (sq_nonneg ‖g z‖)
    rw [sobolevDensity_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
    nlinarith [sq_nonneg ‖fderiv ℝ g z (1, 0)‖, sq_nonneg ‖fderiv ℝ g z (0, 1)‖]

/-- **The adjoint of a cut-off cokernel element.** Let `D_u^* η = 0`, and let `χ` be a cutoff whose
derivative vanishes on `|w| > a` and has norm at most `M`, with `‖J(z, u z)‖ ≤ B` on `|w| ≤ a`.
Since the adjoint of `χ η` only involves the derivative of `χ`,
`∫ ‖D_u^* (χ η)‖² ≤ (M (1 + |B|))² ∫ ‖η‖²`. -/
private theorem integral_norm_floerLinearizationAdjoint_smul_sq_le (ω : SymplecticForm V)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hu : ContDiff ℝ 1 u) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {a M B : ℝ}
    (hB : ∀ z, ‖Complex.equivRealProdCLM.symm z‖ ≤ a →
      ‖(J z (u z)).toLinearMap.toContinuousLinearMap‖ ≤ B)
    (hχd : ∀ z, a < ‖Complex.equivRealProdCLM.symm z‖ → fderiv ℝ χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 1 η)
    (hD : ∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u η z = 0) (hηi : Integrable fun z ↦ ‖η z‖ ^ 2) :
    ∫ z, ‖ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u (fun z ↦ χ z • η z) z‖ ^ 2 ≤ (M * (1 + |B|)) ^ 2 * ∫ z, ‖η z‖ ^ 2 := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity) (hηi.const_mul _)
    (ae_of_all _ fun z ↦ ?_)
  have hle := ω.norm_floerLinearizationAdjoint_fun_smul_le_of_eq_zero (Ks := Ks) (Kt := Kt)
    (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
    ((hχ.differentiable one_ne_zero) z) ((hη.differentiable one_ne_zero) z)
    (((hJ z).comp₂ contDiffAt_id hu.contDiffAt).differentiableAt one_ne_zero) (hD z)
  have hle' : ‖ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
      Ks Kt u (fun z ↦ χ z • η z) z‖ ≤ M * (1 + |B|) * ‖η z‖ := by
    refine hle.trans ?_
    by_cases hz : ‖Complex.equivRealProdCLM.symm z‖ ≤ a
    · have hBz := (hB z hz).trans (le_abs_self B)
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hχM z)
      gcongr
      exact hχM z
    · rw [hχd z (not_le.1 hz), norm_zero, zero_mul, zero_mul]
      have := (norm_nonneg (fderiv ℝ χ z)).trans (hχM z)
      positivity
  calc _ ≤ (M * (1 + |B|) * ‖η z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle' 2
    _ = (M * (1 + |B|)) ^ 2 * ‖η z‖ ^ 2 := by ring

/-- **The weighted energy of a cut-off cokernel element.** Let `J` be `C¹` and `K_s`, `K_t` be
`C²` along a `C¹` map `u`, with `J` compatible along `u`, and let `ρ` be a continuous weight. Let
`χ` be a `C²` cutoff with values in `[0, 1]`, vanishing on `|w| ≥ a`, whose derivative has norm
at most `M`. Then there is `K₀` such that for every square-integrable `C²` covector field `η` with
`D_u^* η = 0` the weighted energy of `χ η` is at most `K₀ ∫ ‖η‖²`. -/
private theorem exists_integral_weighted_smul_le (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ}
    (hρc : Continuous ρ)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχ01 : ∀ z, χ z ∈ Icc 0 1) {a M : ℝ}
    (hχa : ∀ z, a ≤ ‖Complex.equivRealProdCLM.symm z‖ → χ z = 0)
    (hχM : ∀ z, ‖fderiv ℝ χ z‖ ≤ M) :
    ∃ K₀, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
          ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K₀ * ∫ z, ‖η z‖ ^ 2 := by
  have hDa : IsCompact {z : ℝ × ℝ | ‖Complex.equivRealProdCLM.symm z‖ ≤ a} :=
    isCompact_setOf_norm_equivRealProdCLM_symm_le a
  -- Bounds for the weight and for `J` along `u` on the disc `|w| ≤ a`.
  obtain ⟨m₀, hm₀⟩ := hDa.exists_bound_of_continuousOn hρc.continuousOn
  obtain ⟨B, hB⟩ := hDa.exists_bound_of_continuousOn
    (continuous_comp_prodMk_of_continuousAt (fun z ↦ (hJ z).continuousAt)
      hu.continuous).continuousOn
  obtain ⟨C', hC', hdisc⟩ :=
    ω.exists_forall_setIntegral_sobolevDensity_le_mul_integral_floerLinearizationAdjoint_add_of_lt
      hJ hKs hKt hu (w := fun _ ↦ 1) (fun _ ↦ zero_le_one) continuous_const
      (fun _ _ ↦ one_pos) (fun z _ ↦ hc z) (show a < a + 1 by linarith)
  simp only [one_mul] at hdisc
  -- `χ` vanishes near every point of `|w| > a`, and so do its derivative and the cut-offs `χ η`.
  have hχ0 (z : ℝ × ℝ) (hz : a < ‖Complex.equivRealProdCLM.symm z‖) : χ =ᶠ[𝓝 z] 0 :=
    eventually_of_mem ((isOpen_lt continuous_const
      Complex.equivRealProdCLM.symm.continuous.norm).mem_nhds hz) fun w hw ↦ hχa w (le_of_lt hw)
  have hχd (z : ℝ × ℝ) (hz : a < ‖Complex.equivRealProdCLM.symm z‖) : fderiv ℝ χ z = 0 := by
    rw [(hχ0 z hz).fderiv_eq, fderiv_zero, Pi.zero_apply]
  refine ⟨max m₀ 1 * (C' * ((M * (1 + |B|)) ^ 2 + 1)), fun η hη hD hηi ↦ ?_⟩
  have hg : ContDiff ℝ 2 fun z ↦ χ z • η z := hχ.smul hη
  have hg0 (z : ℝ × ℝ) (hz : a < ‖Complex.equivRealProdCLM.symm z‖) :
      (fun z ↦ χ z • η z) =ᶠ[𝓝 z] 0 :=
    (hχ0 z hz).mono fun w hw ↦ by simp [hw]
  have hW := integral_weighted_le_mul_setIntegral_sobolevDensity hρc (hg.of_le one_le_two)
    (le_max_right m₀ 1) (fun z hz ↦ ((le_abs_self _).trans (by simpa using hm₀ z hz)).trans
      (le_max_left _ _)) hg0
  have hT := integral_norm_floerLinearizationAdjoint_smul_sq_le ω hJ hu (hχ.of_le one_le_two)
    (fun z hz ↦ hB z hz) hχd hχM (hη.of_le one_le_two) hD hηi
  -- On the disc, `|χ| ≤ 1` bounds the `L²` term by `∫ ‖η‖²`.
  have hL : ∫ z in {z | ‖Complex.equivRealProdCLM.symm z‖ ≤ a + 1}, ‖χ z • η z‖ ^ 2 ≤
      ∫ z, ‖η z‖ ^ 2 := by
    refine (setIntegral_mono_on ((hg.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _)) hηi.integrableOn
      (isCompact_setOf_norm_equivRealProdCLM_symm_le _).measurableSet fun z _ ↦ ?_).trans
      (setIntegral_le_integral hηi (ae_of_all _ fun z ↦ by positivity))
    have h01 := hχ01 z
    simp only [Pi.pow_apply, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith [h01.1, h01.2])
  calc _ ≤ max m₀ 1 * _ := hW
    _ ≤ max m₀ 1 * (C' * ((M * (1 + |B|)) ^ 2 * (∫ z, ‖η z‖ ^ 2) + ∫ z, ‖η z‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ((hdisc hg (HasCompactSupport.intro hDa fun z hz ↦
          (hg0 z (not_le.1 hz)).self_of_nhds)).trans ?_) (le_max_of_le_right zero_le_one)
        gcongr
    _ = _ := by ring

/-- **A cutoff equal to `1` on a compact set.** Under the hypotheses of
`exists_integral_weighted_smul_le`, for a compact set `K` there is a compactly supported `C²`
cutoff `χ` equal to `1` on `K` such that the weighted energy of `χ η` is at most `K₀ ∫ ‖η‖²` for
every square-integrable `C²` covector field `η` with `D_u^* η = 0`. -/
private theorem exists_cutoff_integral_weighted_smul_le (ω : SymplecticForm V)
    {ρ : ℝ × ℝ → ℝ} (hρc : Continuous ρ)
    (hJ : ∀ z, ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hc : ∀ z, ω.Compatible (J z (u z))) {Kb : Set (ℝ × ℝ)} (hKb : IsCompact Kb) :
    ∃ χ : ℝ × ℝ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ (∀ z ∈ Kb, χ z = 1) ∧
      ∃ K₀, ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
        (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
          Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
        ∫ z, (ρ z * ‖χ z • η z‖ ^ 2 + ‖fderiv ℝ (fun z ↦ χ z • η z) z (1, 0)‖ ^ 2 +
            ‖fderiv ℝ (fun z ↦ χ z • η z) z (0, 1)‖ ^ 2) ≤ K₀ * ∫ z, ‖η z‖ ^ 2 := by
  obtain ⟨r₀, hr₀⟩ := (hKb.image Complex.equivRealProdCLM.symm.continuous).isBounded.exists_norm_le
  obtain ⟨χ, hχs, hχ01, hχ1, hχ0, -, -, hχM⟩ :=
    exists_contDiff_cutoff_comp_continuousLinearMap
      (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) (lt_max_of_lt_right one_pos : 0 < max r₀ 1)
  have hχ2 : ContDiff ℝ 2 χ := hχs.of_le (by simp)
  exact ⟨χ, hχ2, HasCompactSupport.intro
    (isCompact_setOf_norm_equivRealProdCLM_symm_le (2 * max r₀ 1))
      fun z hz ↦ hχ0 z (not_le.1 hz).le,
    fun z hz ↦ hχ1 z ((hr₀ _ (mem_image_of_mem _ hz)).trans (le_max_left _ _)),
    exists_integral_weighted_smul_le ω hρc hJ hKs hKt hu hc hχ2 hχ01 hχ0 hχM⟩

/-- **Cokernel elements are regular.** When the data are regular enough, every element of the
orthogonal complement of the range of `D_u` is represented by a `C²` covector field annihilated by
`D_u^*`. -/
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

/-- **Peetre's argument for the cokernel.** Let `J` be `C³` and `K_s`, `K_t` be `C⁴` at the points
`(z, u z)` along a `C³` map `u`, with `J` compatible along `u`, and let the coefficient field of
`D_u` on the conformal jets of a weight `ρ` on the plane be essentially bounded. Suppose that for a
compact set `K` every square-integrable `C²` covector field `η` with `D_u^* η = 0` satisfies
`∫ ‖η‖² ≤ A ∫_K ‖η‖²`. Then the orthogonal complement of the range of the realization
`D_u : W^{1,2}(ℂ, V) → L²(ℂ, V)` is finite-dimensional. -/
theorem finiteDimensional_orthogonal_range_floerConformalSobolevOperator_of_le
    (ω : SymplecticForm V) {ρ : ℝ × ℝ → ℝ} (hρ : IsWeight univ ρ)
    (hJ : ∀ z, ContDiffAt ℝ 3
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 4 (uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 4 (uncurry Kt) (z, u z)) (hu : ContDiff ℝ 3 u)
    (hc : ∀ z, ω.Compatible (J z (u z)))
    (hM : MemLp (ω.floerConformalJetCoeff ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u) ∞ (volume.restrict univ))
    {Kb : Set (ℝ × ℝ)} (hKb : IsCompact Kb) {A : ℝ}
    (hglob : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η →
      (∀ z, ω.floerLinearizationAdjoint (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap)
        Ks Kt u η z = 0) → Integrable (fun z ↦ ‖η z‖ ^ 2) →
      ∫ z, ‖η z‖ ^ 2 ≤ A * ∫ z in Kb, ‖η z‖ ^ 2) :
    FiniteDimensional ℝ (ω.floerConformalSobolevOperator univ ρ
      (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u).rangeᗮ := by
  have hJ1 (z : ℝ × ℝ) : ContDiffAt ℝ 1
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) (z, u z) :=
    (hJ z).of_le (by norm_num)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- A cutoff `χ` equal to `1` on `K`, and the bound on the weighted energy of `χ η`.
  obtain ⟨χ, hχ2, hχc, hχ1K, K₀, hK₀⟩ := exists_cutoff_integral_weighted_smul_le ω
    (continuousOn_univ.1 hρ.continuousOn) hJ1 (fun z ↦ (hKs z).of_le (by norm_num))
    (fun z ↦ (hKt z).of_le (by norm_num)) hu1 hc hKb
  -- A nonnegative constant for the estimate on `K`, and the compact restriction to `K`.
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hglob' := fun ⦃η⦄ hη hD hηi ↦ (hglob (η := η) hη hD hηi).trans
    (mul_le_mul_of_nonneg_right (le_max_left A 0)
      (setIntegral_nonneg_of_ae_restrict (ae_of_all _ fun z ↦ by positivity)))
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
  have hgT (k : ℕ) : g k ∈ testSection (V →L[ℝ] ℝ) univ :=
    mem_testSection_iff.2 ⟨hg k, hχc.smul_right, subset_univ _⟩
  set x : ℕ → H1 (V →L[ℝ] ℝ) univ ρ := fun k ↦ ⟨(memLp_jet hρ (hgT k)).toLp (jet ρ (g k)),
    jetSubmodule_le_H1 (toLp_jet_mem_jetSubmodule hρ (hgT k))⟩
  have hxb (k : ℕ) : ‖x k‖ ≤ √(max K₀ 0 * Rr ^ 2) := by
    rw [← Submodule.norm_coe]
    exact norm_toLp_jet_le hρ (hηae k) (hgT k) (by rw [Submodule.norm_coe]; exact hfR k)
      (hK₀ (hηs k) (hηD k))
  -- By Rellich's theorem two of them are close on `K`, hence close everywhere.
  obtain ⟨k, l, hkl, hdist⟩ := hcpt.exists_dist_lt_of_norm_le hxb
    (by positivity : 0 < (max A 0 * |B'| + 1)⁻¹)
  rw [dist_eq_norm, ← map_sub] at hdist
  have hjet := toLp_jet_sub_ae_eq hρ (hgT k) (hgT l)
  have hgη (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Kb) : g k z = η k z := by
    simp [g, hχ1K z hz]
  have hle := norm_sub_sq_le_of_setIntegral_le ω hJ1 hu1 hKb.measurableSet hA0 hglob' (hηs k)
    (hηs l) (hηae k) (hηae l) (hηD k) (hηD l) (hgη k) (hgη l)
    (B := |B'|) ((hB' ((hg k).continuous.sub (hg l).continuous).continuousOn hjet).trans
      ((mul_le_mul_of_nonneg_right (le_abs_self B') (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist.le 2) (abs_nonneg _))))
  rw [← Submodule.coe_sub, Submodule.norm_coe, abs_abs] at hle
  have := hsep hkl.ne
  nlinarith [mul_abs_mul_inv_sq_lt_one (B := B') hA0]

end SymplecticForm

end TauCeti
