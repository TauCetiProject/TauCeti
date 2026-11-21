/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Lp.Basic
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Pseudodifferential.Symbol.Map
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp

/-!
# Quantizations with integrable kernels on `Lᵖ` functions as tempered distributions

For a scalar symbol `b` of order `m < -n` whose estimates are uniform in the position, `Op(b)`
acts both on `Lᵖ` functions, as the integral operator with the kernel `K_b`
(`TauCeti.Symbol.quantizeLp`), and on tempered distributions, by duality
(`TauCeti.Symbol.quantizeTempered`). This file shows that the two actions agree: the transpose of
`Op(b)` is the integral operator with the transposed kernel, and on the tempered distribution of an
`Lᵖ` function `Op(b)` gives the tempered distribution of an `Lᵖ` function, with the scale-invariant
bound of `TauCeti.Symbol.norm_quantizeLp_le`. Functions with values in a complex Banach space `F`
are allowed, the scalar symbol acting on `F` by multiplication.

## Main declarations

* `TauCeti.Symbol.IsUniform.transposeUniformCLM_ae_eq_integral`: the transpose of `Op(b)` is the
  integral operator with the transposed kernel.
* `TauCeti.Symbol.exists_quantizeTempered_eq_and_norm_le`: `Op(b)` maps the tempered distribution
  of an `Lᵖ` function to the tempered distribution of an `Lᵖ` function, of norm at most
  `C A Rⁿ ‖f‖_p`.
-/

public section

noncomputable section

open MeasureTheory Function
open scoped SchwartzMap ENNReal NNReal

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (F) in
/-- A scalar coefficient `T : ℂ →L[ℂ] ℂ`, acting on `F` as multiplication by `T 1`. -/
private def scalarCLM : (ℂ →L[ℂ] ℂ) →L[ℝ] (F →L[ℂ] F) :=
  ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).smulRight
    (ContinuousLinearMap.id ℂ F)).restrictScalars ℝ

private theorem scalarCLM_apply_apply (T : ℂ →L[ℂ] ℂ) (v : F) : scalarCLM F T v = T 1 • v :=
  (rfl)

private theorem norm_scalarCLM_apply [Nontrivial F] (T : ℂ →L[ℂ] ℂ) : ‖scalarCLM F T‖ = ‖T‖ := by
  have hT : T = ContinuousLinearMap.toSpanSingleton ℂ (T 1) := by ext; simp
  have h : scalarCLM F T = T 1 • ContinuousLinearMap.id ℂ F := by
    ext v
    simp [scalarCLM_apply_apply]
  rw [h, norm_smul, ContinuousLinearMap.norm_id, mul_one]
  conv_rhs => rw [hT]
  rw [ContinuousLinearMap.norm_toSpanSingleton]

private theorem scalarCLM_circle_smul (c : Circle) (T : ℂ →L[ℂ] ℂ) :
    scalarCLM F (c • T) = c • scalarCLM F T := by
  ext v
  simp only [scalarCLM_apply_apply, FunLike.coe_smul, Pi.smul_apply, Circle.smul_def, smul_smul,
    smul_eq_mul]

variable [CompleteSpace F] {b : Symbol n ℂ ℂ m}

/-- The kernel of the image of `b` under `scalarCLM` is the image of the kernel of `b`. -/
private theorem quantizationKernel_map_scalarCLM (hm : m < -n) (x y : CoordinateSpace n) :
    quantizationKernel (b.map (scalarCLM F)).coefficient x y =
      scalarCLM F (quantizationKernel b.coefficient x y) := by
  simp only [quantizationKernel_def, coefficient_map]
  rw [← ContinuousLinearMap.integral_comp_comm]
  · simp only [scalarCLM_circle_smul]
  · exact integrable_quantizationKernel_integrand (b.integrable_coefficient hm x) y

private theorem quantizationKernel_map_scalarCLM_apply (hm : m < -n) (x y : CoordinateSpace n)
    (v : F) :
    quantizationKernel (b.map (scalarCLM F)).coefficient x y v =
      quantizationKernel b.coefficient x y 1 • v := by
  rw [quantizationKernel_map_scalarCLM hm, scalarCLM_apply_apply]

/-- The product `φ(x) K_b(x, y) 1` of a Schwartz function and the kernel of a uniform symbol of
order `m < -n` is integrable on `ℝⁿ × ℝⁿ`. -/
private theorem integrable_mul_quantizationKernel (hb : b.IsUniform) (hm : m < -n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      φ z.1 * quantizationKernel b.coefficient z.1 z.2 1) (volume.prod volume) := by
  obtain ⟨B, hrow, -⟩ := hb.exists_lintegral_enorm_quantizationKernel_le hm
  have hc : Continuous fun z : CoordinateSpace n × CoordinateSpace n ↦
      φ z.1 * quantizationKernel b.coefficient z.1 z.2 1 :=
    (φ.continuous.comp continuous_fst).mul
      ((b.continuous_quantizationKernel hm).clm_apply continuous_const)
  refine (integrable_prod_iff hc.aestronglyMeasurable).2 ⟨ae_of_all _ fun x ↦ ?_, ?_⟩
  · exact (((hb.integrable_quantizationKernel hm x).apply_continuousLinearMap 1).const_mul (φ x))
  refine (φ.integrable.norm.mul_const B).mono' hc.norm.aestronglyMeasurable.integral_prod_right'
    (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
  simp_rw [norm_mul]
  rw [integral_const_mul]
  gcongr
  have hK := hb.integrable_quantizationKernel hm x
  calc ∫ y, ‖quantizationKernel b.coefficient x y 1‖
      ≤ ∫ y, ‖quantizationKernel b.coefficient x y‖ :=
        integral_mono (hK.apply_continuousLinearMap 1).norm hK.norm fun y ↦ by
          simpa using (quantizationKernel b.coefficient x y).le_opNorm 1
    _ = (∫⁻ y, ‖quantizationKernel b.coefficient x y‖ₑ).toReal :=
        integral_norm_eq_lintegral_eNorm hK.aestronglyMeasurable
    _ ≤ B := ENNReal.toReal_le_of_le_ofReal B.coe_nonneg (by simpa using hrow x)

/-- **The kernel of the transpose.** For a uniform symbol `b` of order `m < -n`, the transpose
`Op(b)ᵗ` of its quantization is the integral operator with the transposed kernel:
`Op(b)ᵗ φ (y) = ∫ φ(x) K_b(x, y) dx` for almost every `y`. -/
theorem IsUniform.transposeUniformCLM_ae_eq_integral (hb : b.IsUniform) (hm : m < -n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    ⇑(transposeUniformCLM b hb φ) =ᵐ[volume]
      fun y ↦ ∫ x, φ x * quantizationKernel b.coefficient x y 1 := by
  have hint := integrable_mul_quantizationKernel hb hm φ
  set g : CoordinateSpace n → ℂ := fun y ↦ ∫ x, φ x * quantizationKernel b.coefficient x y 1
  have hg : LocallyIntegrable g volume := hint.integral_prod_right.locallyIntegrable
  set u : Lp ℂ 1 (volume : Measure (CoordinateSpace n)) := (transposeUniformCLM b hb φ).toLp 1
  have hu : (u : CoordinateSpace n → ℂ) =ᵐ[volume] transposeUniformCLM b hb φ :=
    (transposeUniformCLM b hb φ).coeFn_toLp 1
  refine hu.symm.trans (Lp.ae_eq_of_toTemperedDistribution_apply_eq u hg fun ψ ↦ ?_)
  have h₁ : (u : 𝓢'(CoordinateSpace n, ℂ)) ψ = ∫ y, transposeUniformCLM b hb φ y * ψ y := by
    rw [Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hu] with y hy
    rw [hy, smul_eq_mul, mul_comm]
  have h₂ (x : CoordinateSpace n) : φ x * quantizeUniformCLM b hb ψ x =
      ∫ y, φ x * quantizationKernel b.coefficient x y 1 * ψ y := by
    rw [quantizeUniformCLM_apply,
      quantizeSchwartzValue_eq_integral_quantizationKernel (b.integrable_coefficient hm x),
      ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    have := (quantizationKernel b.coefficient x y).map_smul (ψ y) 1
    rw [smul_eq_mul, smul_eq_mul, mul_one] at this
    dsimp only
    rw [this, mul_assoc, mul_comm (ψ y)]
  have h₃ : Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      φ z.1 * quantizationKernel b.coefficient z.1 z.2 1 * ψ z.2) (volume.prod volume) :=
    hint.mul_bdd (ψ.continuous.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ψ.norm_le_seminorm ℂ z.2)
  rw [h₁, ← integral_mul_quantizeUniformCLM b hb ψ φ]
  simp_rw [h₂]
  rw [integral_integral_swap h₃]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  simp only [g, smul_eq_mul]
  rw [integral_mul_const, mul_comm]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand `(φ(x) K_b(x, y) 1) • f(y)` pairing a Schwartz function, the kernel of a uniform
symbol of order `m < -n` and an `Lᵖ` function is integrable on `ℝⁿ × ℝⁿ`. -/
private theorem integrable_smul_quantizationKernel (hb : b.IsUniform) (hm : m < -n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) (f : Lp F p (volume : Measure (CoordinateSpace n))) :
    Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (φ z.1 * quantizationKernel b.coefficient z.1 z.2 1) • f z.2) (volume.prod volume) := by
  have hp : 1 ≤ p := Fact.out
  set KF := quantizationKernel (b.map (scalarCLM F)).coefficient
  obtain ⟨B, hrow, hcol⟩ := (hb.map (scalarCLM F)).exists_lintegral_enorm_quantizationKernel_le hm
  have hKFc : Continuous (uncurry KF) := (b.map (scalarCLM F)).continuous_quantizationKernel hm
  -- The real kernel `‖K_F(x, y)‖` and the function `‖f‖` give an `Lᵖ` majorant `N`.
  set Kr : CoordinateSpace n → CoordinateSpace n → ℝ →L[ℝ] ℝ :=
    fun x y ↦ ‖KF x y‖ • ContinuousLinearMap.id ℝ ℝ
  have hKr (x y : CoordinateSpace n) : ‖Kr x y‖ₑ ≤ ‖KF x y‖ₑ := by
    refine eNorm_le_iff_norm_le.2 ?_
    simp only [Kr, norm_smul, norm_norm]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  have hKrm : AEStronglyMeasurable (uncurry Kr) (volume.prod volume) :=
    (hKFc.norm.smul continuous_const).aestronglyMeasurable
  have hrow' : ∀ᵐ x ∂volume, ∫⁻ y, ‖Kr x y‖ₑ ≤ B :=
    ae_of_all _ fun x ↦ (lintegral_mono (hKr x)).trans (hrow x)
  have hcol' : ∀ᵐ y ∂volume, ∫⁻ x, ‖Kr x y‖ₑ ≤ B :=
    ae_of_all _ fun y ↦ (lintegral_mono fun x ↦ hKr x y).trans (hcol y)
  have hfn : MemLp (fun y ↦ ‖f y‖) p volume := (Lp.memLp f).norm
  have hN := memLp_integral_apply hKrm hfn hp hrow' hcol'
  have hNi := ae_integrable_apply_of_memLp hKrm hfn hp hrow' hcol'
  simp only [Kr, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    at hN hNi
  -- `‖φ‖` is in the dual exponent, so `‖φ‖ N` is integrable by Hölder's inequality.
  have : (1 - p⁻¹)⁻¹.HolderConjugate p := (ENNReal.HolderConjugate.inv_one_sub_inv' hp).symm
  have hφN := (φ.memLp (1 - p⁻¹)⁻¹ (μ := volume)).norm.integrable_mul hN
  have hm' : AEStronglyMeasurable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (φ z.1 * quantizationKernel b.coefficient z.1 z.2 1) • f z.2) (volume.prod volume) :=
    ((φ.continuous.comp continuous_fst).mul ((b.continuous_quantizationKernel hm).clm_apply
      continuous_const)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f).comp_snd
  have hpt (x y : CoordinateSpace n) :
      ‖(φ x * quantizationKernel b.coefficient x y 1) • f y‖ ≤ ‖φ x‖ * (‖KF x y‖ * ‖f y‖) := by
    rw [mul_smul, norm_smul, ← quantizationKernel_map_scalarCLM_apply hm]
    gcongr
    exact (KF x y).le_opNorm _
  refine (integrable_prod_iff hm').2 ⟨?_, ?_⟩
  · filter_upwards [hNi, hm'.prodMk_left] with x hx hxm
    exact (hx.const_mul ‖φ x‖).mono' hxm (ae_of_all _ fun y ↦ hpt x y)
  · refine hφN.mono' hm'.norm.integral_prod_right' ?_
    filter_upwards [hNi] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), Pi.mul_apply,
      ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) (hx.const_mul _)
      (ae_of_all _ fun y ↦ hpt x y)

/-- **Quantization of `Lᵖ` functions.** Let `b` be a uniform symbol of order `m < -n`. For
`1 ≤ p ≤ ∞` and `f ∈ Lᵖ(ℝⁿ; F)`, the quantization of the tempered distribution of `f` is the
tempered distribution of an `Lᵖ` function `v`. If `∫ ‖b(x, ξ)‖ dξ ≤ A` and
`∫ ‖∂_{ξ_j}^{n+1} b(x, ξ)‖ dξ ≤ A Rⁿ⁺¹` at every position and in every coordinate direction, then
`‖v‖_p ≤ C A Rⁿ ‖f‖_p`, with `C` depending only on `n`. -/
theorem exists_quantizeTempered_eq_and_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℝ} {b : Symbol n ℂ ℂ m} (hb : b.IsUniform), m < -n →
      ∀ {A R : ℝ}, 0 < R → (∀ x, ∫ ξ, ‖b.coefficient (x, ξ)‖ ≤ A) →
      (∀ x j, ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j) b.coefficient x ξ‖ ≤
        A * R ^ (n + 1)) →
      ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp F p (volume : Measure (CoordinateSpace n))),
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        quantizeTempered F b hb (f : 𝓢'(CoordinateSpace n, F)) = v ∧ ‖v‖ ≤ C * A * R ^ n * ‖f‖ := by
  refine ⟨2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * Real.pi) ^ n)⁻¹ *
    ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹, by positivity,
    fun {m b} hb hm {A R} hR h₀ h₁ {p} _ f ↦ ?_⟩
  have hA : 0 ≤ A := (integral_nonneg fun _ ↦ norm_nonneg _).trans (h₀ 0)
  rcases subsingleton_or_nontrivial F with hF | hF
  · refine ⟨0, ?_, by rw [norm_zero]; positivity⟩
    have hf : f = 0 := Lp.ext (by
      filter_upwards [Lp.coeFn_zero F p (volume : Measure (CoordinateSpace n))] with x _
      exact Subsingleton.elim _ _)
    rw [hf, Lp.toTemperedDistribution_zero, map_zero]
  set T := (b.map (scalarCLM F)).quantizeLp p hm (hb.map _)
  refine ⟨T f, ?_, ?_⟩
  · ext φ
    rw [quantizeTempered_apply_apply, Lp.toTemperedDistribution_apply,
      Lp.toTemperedDistribution_apply]
    calc ∫ y, transposeUniformCLM b hb φ y • f y
        = ∫ y, (∫ x, φ x * quantizationKernel b.coefficient x y 1) • f y := by
          refine integral_congr_ae ?_
          filter_upwards [hb.transposeUniformCLM_ae_eq_integral hm φ] with y hy
          rw [hy]
      _ = ∫ y, ∫ x, (φ x * quantizationKernel b.coefficient x y 1) • f y := by
          simp_rw [integral_smul_const]
      _ = ∫ x, ∫ y, (φ x * quantizationKernel b.coefficient x y 1) • f y :=
          (integral_integral_swap (integrable_smul_quantizationKernel hb hm φ f)).symm
      _ = ∫ x, φ x • T f x := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_quantizeLp (a := b.map (scalarCLM F)) (hm := hm)
            (ha := hb.map _) f] with x hx
          rw [hx, ← integral_smul]
          simp_rw [quantizationKernel_map_scalarCLM_apply hm, smul_smul]
  · have h₀' (x) : ∫ ξ, ‖(b.map (scalarCLM F)).coefficient (x, ξ)‖ ≤ A := by
      simpa only [coefficient_map, norm_scalarCLM_apply] using h₀ x
    have h₁' (x j) : ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) j)
        (b.map (scalarCLM F)).coefficient x ξ‖ ≤ A * R ^ (n + 1) := by
      rw [show (b.map (scalarCLM F)).coefficient = scalarCLM F ∘ b.coefficient from
        funext (coefficient_map _ b)]
      simp_rw [(scalarCLM F).mixedDeriv_comp_left b.contDiff_coefficient, norm_scalarCLM_apply]
      exact h₁ x j
    refine (T.le_opNorm f).trans ?_
    gcongr
    exact (norm_quantizeLp_le hR h₀' h₁').trans_eq (by ring)

end Symbol

end TauCeti
