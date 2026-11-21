/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
public import TauCeti.Analysis.Pseudodifferential.Lp
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.FourierMultiplier
import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Analysis.Pseudodifferential.Symbol.Map
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.AlmostDiagonal
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Pseudodifferential operators on Besov spaces

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{αβ} ⟨ξ⟩^(m - |β|)` hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). This file proves that its quantization `Op(a)`, acting on tempered
distributions (`TauCeti.Symbol.quantizeTempered`), maps the inhomogeneous Besov space `B^s_{p,q}` to
`B^{s-m}_{p,q}` for every real `s` and all `1 ≤ p, q ≤ ∞`
(`TauCeti.Symbol.IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le`,
`TemperedDistribution.MemBesov.quantizeTempered`, `TauCeti.Symbol.quantizeBesov`). For
`p = q = ∞` this is the mapping `𝒞^s → 𝒞^{s-m}` of the Hölder–Zygmund scale, which at non-integer
orders is the scale of the bounded Hölder spaces (`TauCeti.BesovSpace.ckHolderSpaceEquiv`). Unlike
the `Lᵖ` and `Hˢ` theories, no Calderón–Zygmund or `L²` argument is involved, and the endpoints
`p = 1, ∞` are included.

## The argument

The Bessel potential reduces the order to `0`: `Op(a) = Op(a ⟨ξ / 2π⟩ ^ (-m)) ∘ J^m`
(`TauCeti.Symbol.IsUniform.quantizeTempered_eq_comp_besselPotential`), and `J^m` is an
isomorphism `B^s_{p,q} ≃ B^{s-m}_{p,q}`. For a symbol of order `0`, `Op(a)` is almost diagonal
with respect to the Littlewood–Paley blocks `Δⱼ`: for every `N` there is `K` with

`‖Δⱼ Op(a) Δₖ u‖_p ≤ K 2^{-N |j - k|} ‖Δₖ u‖_p`,

and for `N > |s|` such an operator is bounded on `B^s_{p,q}`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le`). The three ranges
of `j` are handled as follows.

* **`Op(a)` on a block.** A tempered distribution whose spectrum lies in the `k`-th dyadic annulus
  is fixed by the Fourier multiplier of a cutoff equal to `1` near that annulus, so
  `Op(a) Δₖ u = Op(b) Δₖ u` for the symbol `b(x, ξ)` cut off in the frequency to a fixed number of
  Littlewood–Paley pieces (`TauCeti.Symbol.IsUniform.quantizeTempered_fourierMultiplierCLM`). A
  piece at frequency `2^i` has an integrable kernel with row and column integrals bounded
  independently of `i`, by the integrated dyadic estimates
  `TauCeti.Symbol.IsUniform.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le`; and on the
  tempered distribution of an `Lᵖ` function the quantization of such a symbol is the integral
  operator with that kernel (`TauCeti.Symbol.exists_quantizeTempered_eq_and_norm_le`).
  So `‖Op(a) Δₖ u‖_p ≤ C ‖Δₖ u‖_p`, and `j = k` follows.
* **High output frequencies, `j > k`.** A derivative falls either on the input or on the position
  variable of the symbol, `∂_v Op(a) = Op(a) ∂_v + Op(∂_{x, v} a)`
  (`TauCeti.Symbol.lineDerivOp_quantizeTempered_eq_add`), and Bernstein's inequality bounds the
  derivatives of the block `Δₖ u` by `2^k`. So the derivatives of order `N` of `Op(a) Δₖ u` are
  `O(2^{kN} ‖Δₖ u‖_p)`, and the reverse Bernstein inequality on the `j`-th annulus gives
  `‖Δⱼ Op(a) Δₖ u‖_p = O(2^{(k - j) N} ‖Δₖ u‖_p)`.
* **Low output frequencies, `j < k`.** On the `k`-th annulus `Δₖ u = ∑ᵢ ∂ᵢ gᵢ` with
  `‖gᵢ‖_p = O(2^{-k} ‖Δₖ u‖_p)`, and the commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` moves the
  derivative onto `Δⱼ`, where it costs `2^j`. Each repetition gains a factor `2^{j - k}`.

## Main declarations

* `TauCeti.Symbol.IsUniform.transposeUniformCLM_ae_eq_integral`: for a uniform symbol of order
  `m < -n`, the transpose of `Op(b)` is the integral operator with the transposed kernel.
* `TauCeti.Symbol.exists_quantizeTempered_eq_and_norm_le`: for such a symbol, `Op(b)` maps the
  tempered distribution of an `Lᵖ` function to an `Lᵖ` function, with the scale-invariant bound of
  `TauCeti.Symbol.norm_quantizeLp_le`.
* `TauCeti.Symbol.IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le`: the bound
  `‖Op(a) u‖_{B^{s-m}_{p,q}} ≤ C ‖u‖_{B^s_{p,q}}`.
* `TemperedDistribution.MemBesov.quantizeTempered`: `Op(a)` maps `B^s_{p,q}` into
  `B^{s-m}_{p,q}`.
* `TauCeti.Symbol.quantizeBesov`: `Op(a)` as a bounded operator `B^s_{p,q} → B^{s-m}_{p,q}`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3,
  (3.32)–(3.34) (the Hölder–Zygmund mapping of pseudodifferential operators).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8 (almost diagonal operators on
  Besov spaces).
-/

public section

noncomputable section

open MeasureTheory Complex Function
open scoped SchwartzMap ENNReal NNReal LineDeriv FourierTransform

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### Quantizations with integrable kernels on `Lᵖ` functions -/

section Kernel

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

variable {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- The integrand `(φ(x) K_b(x, y) 1) • f(y)` pairing a Schwartz function, the kernel of a uniform
symbol of order `m < -n` and an `Lᵖ` function is integrable on `ℝⁿ × ℝⁿ`. -/
private theorem integrable_smul_quantizationKernel (hb : b.IsUniform) (hm : m < -n)
    (φ : 𝓢(CoordinateSpace n, ℂ)) (f : Lp F p (volume : Measure (CoordinateSpace n))) :
    Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (φ z.1 * quantizationKernel b.coefficient z.1 z.2 1) • f z.2) (volume.prod volume) := by
  have hKF (x y : CoordinateSpace n) (v : F) :
      quantizationKernel (b.map (scalarCLM F)).coefficient x y v =
        quantizationKernel b.coefficient x y 1 • v := by
    rw [quantizationKernel_map_scalarCLM hm, scalarCLM_apply_apply]
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
  have hN := memLp_integral_apply hKrm hfn hp.out hrow' hcol'
  have hNi := ae_integrable_apply_of_memLp hKrm hfn hp.out hrow' hcol'
  simp only [Kr, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    at hN hNi
  -- `‖φ‖` is in the dual exponent, so `‖φ‖ N` is integrable by Hölder's inequality.
  have : (1 - p⁻¹)⁻¹.HolderConjugate p := (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  have hφN := (φ.memLp (1 - p⁻¹)⁻¹ (μ := volume)).norm.integrable_mul hN
  have hm' : AEStronglyMeasurable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (φ z.1 * quantizationKernel b.coefficient z.1 z.2 1) • f z.2) (volume.prod volume) :=
    ((φ.continuous.comp continuous_fst).mul ((b.continuous_quantizationKernel hm).clm_apply
      continuous_const)).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f).comp_snd
  have hpt (x y : CoordinateSpace n) :
      ‖(φ x * quantizationKernel b.coefficient x y 1) • f y‖ ≤ ‖φ x‖ * (‖KF x y‖ * ‖f y‖) := by
    rw [mul_smul, norm_smul, ← hKF]
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
`Lᵖ` function `x ↦ ∫ K_b(x, y) f(y) dy`. If `∫ ‖b(x, ξ)‖ dξ ≤ A` and
`∫ ‖∂_{ξ_j}^{n+1} b(x, ξ)‖ dξ ≤ A Rⁿ⁺¹` at every position and in every coordinate direction, its
norm is at most `C A Rⁿ ‖f‖_p`, with `C` depending only on `n`. -/
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
    have hKF (x y : CoordinateSpace n) (v : F) :
        quantizationKernel (b.map (scalarCLM F)).coefficient x y v =
          quantizationKernel b.coefficient x y 1 • v := by
      rw [quantizationKernel_map_scalarCLM hm, scalarCLM_apply_apply]
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
          simp_rw [hKF, smul_smul]
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

end Kernel


/-! ### Dyadic pieces -/

section Dyadic

variable [CompleteSpace F]

/-- The bump function `φ` dilated by `2π`, which converts cutoffs in the frequency `ζ` of Mathlib's
Fourier transform into cutoffs in the angular frequency `ξ = 2πζ` of the quantization. -/
private def twoPiDilate (φ : ContDiffBump (0 : CoordinateSpace n)) :
    ContDiffBump (0 : CoordinateSpace n) where
  rIn := 2 * Real.pi * φ.rIn
  rOut := 2 * Real.pi * φ.rOut
  rIn_pos := by have := φ.rIn_pos; positivity
  rIn_lt_rOut := mul_lt_mul_of_pos_left φ.rIn_lt_rOut (by positivity)

private theorem twoPiDilate_apply (φ : ContDiffBump (0 : CoordinateSpace n))
    (ξ : CoordinateSpace n) : twoPiDilate φ ξ = φ ((2 * Real.pi)⁻¹ • ξ) := by
  have h₁ : (twoPiDilate φ).rOut / (twoPiDilate φ).rIn = φ.rOut / φ.rIn :=
    mul_div_mul_left _ _ (by positivity)
  have h₂ : (twoPiDilate φ).rIn⁻¹ = φ.rIn⁻¹ * (2 * Real.pi)⁻¹ := by
    rw [twoPiDilate, mul_inv, mul_comm]
  simp only [ContDiffBump.apply, sub_zero, smul_smul, h₁, h₂]

private theorem inhomogeneousLittlewoodPaley_twoPiDilate (φ : ContDiffBump (0 : CoordinateSpace n))
    (j : ℕ) (ξ : CoordinateSpace n) :
    (twoPiDilate φ).inhomogeneousLittlewoodPaley j ξ =
      φ.inhomogeneousLittlewoodPaley j ((2 * Real.pi)⁻¹ • ξ) := by
  rcases j with _ | j
  · simp [twoPiDilate_apply]
  · simp only [ContDiffBump.inhomogeneousLittlewoodPaley_succ_apply, twoPiDilate_apply,
      smul_comm ((2 * Real.pi)⁻¹ : ℝ)]

variable (ψ : ContDiffBump (0 : CoordinateSpace n)) {a : Symbol n ℂ ℂ 0}

/-- The `j`-th Littlewood–Paley piece of `a`, which has bounded frequency support, as a symbol of
order `-(n + 1)`, where its kernel is integrable. -/
private def dyadicPiece (a : Symbol n ℂ ℂ 0) (j : ℕ) : Symbol n ℂ ℂ (-(n + 1)) :=
  ofBoundedFrequencySupport (a.littlewoodPaleyPiece ψ j).coefficient
    (a.littlewoodPaleyPiece ψ j).contDiff_coefficient (2 ^ j * ψ.rOut)
    fun x _ hξ ↦ a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm ψ x hξ

private theorem coefficient_dyadicPiece (a : Symbol n ℂ ℂ 0) (j : ℕ) :
    (dyadicPiece ψ a j).coefficient = (a.littlewoodPaleyPiece ψ j).coefficient :=
  coefficient_ofBoundedFrequencySupport _ _ _ _

private theorem isUniform_dyadicPiece (ha : a.IsUniform) (j : ℕ) :
    (dyadicPiece ψ a j).IsUniform :=
  (ha.littlewoodPaleyPiece ψ j).ofBoundedFrequencySupport _ _

/-- **The dyadic pieces are uniformly bounded on `Lᵖ`.** For a uniform symbol `a` of order `0`,
the quantizations of its Littlewood–Paley pieces act on `Lᵖ` functions, `1 ≤ p ≤ ∞`, with norms
bounded independently of the piece and of `p`. -/
private theorem IsUniform.exists_quantizeTempered_dyadicPiece_eq_and_norm_le (ha : a.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
      (f : Lp F p (volume : Measure (CoordinateSpace n))),
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        quantizeTempered F (dyadicPiece ψ a j) (isUniform_dyadicPiece ψ ha j) f = v ∧
          ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨C₀, hC₀, hreal⟩ := exists_quantizeTempered_eq_and_norm_le (F := F) (n := n)
  obtain ⟨c₀, hc₀, h₀⟩ := ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le ψ [] []
  choose c hc h₁ using fun i : Fin n ↦
    ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le ψ [] (List.replicate (n + 1) i)
  set c' := c₀ + ∑ i, c i
  have hc' : 0 ≤ c' := add_nonneg hc₀ (Finset.sum_nonneg fun i _ ↦ hc i)
  refine ⟨C₀ * c', by positivity, fun j {p} _ f ↦ ?_⟩
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hrpow (t : ℕ) : ((2 : ℝ) ^ j) ^ (t : ℝ) = (2 ^ j) ^ t := Real.rpow_natCast _ t
  have h₀' (x : CoordinateSpace n) :
      ∫ ξ, ‖(dyadicPiece ψ a j).coefficient (x, ξ)‖ ≤ c' * (2 ^ j) ^ n := by
    rw [coefficient_dyadicPiece]
    have := h₀ j x
    simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero, zero_add,
      hrpow] at this
    refine this.trans ?_
    gcongr
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hc i)
  have h₁' (x : CoordinateSpace n) (i : Fin n) :
      ∫ ξ, ‖mixedDeriv [] (List.replicate (n + 1) i) (dyadicPiece ψ a j).coefficient x ξ‖ ≤
        c' * (2 ^ j) ^ n * ((2 ^ j)⁻¹) ^ (n + 1) := by
    rw [coefficient_dyadicPiece]
    have := h₁ i j x
    rw [List.length_replicate, show (0 : ℝ) - ((n + 1 : ℕ) : ℝ) + n = ((-1 : ℤ) : ℝ) by
      push_cast; ring, Real.rpow_intCast] at this
    refine this.trans ?_
    rw [zpow_neg_one, inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_assoc c',
      mul_inv_cancel₀ (by positivity), mul_one]
    gcongr
    exact (Finset.single_le_sum (fun i _ ↦ hc i) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hc₀)
  obtain ⟨v, hv, hvn⟩ := hreal (isUniform_dyadicPiece ψ ha j) (by linarith)
    (inv_pos.2 h2) h₀' h₁' f
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  rw [inv_pow]
  field_simp

/-! ### Blocks -/

open Distribution TemperedDistribution Metric

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- The frequencies off the support of the `k`-th piece of the Littlewood–Paley partition of `φ`:
the complement of the closed ball of radius `φ.rOut` for `k = 0`, and for `k ≥ 1` the complement of
the annulus `2^{k-1} φ.rIn ≤ ‖ζ‖ ≤ 2^k φ.rOut`. -/
private def offSpectrum (k : ℕ) : Set (CoordinateSpace n) :=
  if k = 0 then (closedBall 0 φ.rOut)ᶜ
  else ball 0 (2 ^ k * φ.rIn / 2) ∪ (closedBall 0 (2 ^ k * φ.rOut))ᶜ

omit [CompleteSpace F] in
/-- The Fourier transform of `Δₖ u` vanishes off the spectrum of the `k`-th piece. -/
private theorem isVanishingOn_offSpectrum (k : ℕ) (u : 𝓢'(CoordinateSpace n, F)) :
    IsVanishingOn (𝓕 (littlewoodPaleyBlock F φ k u) : 𝓢'(CoordinateSpace n, F))
      (offSpectrum φ k) := by
  rcases k with _ | k
  · simpa [offSpectrum] using isVanishingOn_fourier_littlewoodPaleyBlock φ 0 u
  · have h := isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k u
    rw [Set.compl_sdiff] at h
    simpa [offSpectrum, show 2 ^ (k + 1) * φ.rIn / 2 = 2 ^ k * φ.rIn by ring] using h

/-- The enlarged Littlewood–Paley cutoff of width `L₀ + 3` is `1` on the annulus
`2^k φ.rIn / 4 < ‖ζ‖ < 2^{k+1} φ.rOut` (on the ball `‖ζ‖ < 2 φ.rOut` for `k = 0`), as soon as
`φ.rOut < 2^{L₀} φ.rIn`. -/
private theorem enlargedLittlewoodPaley_eq_one {L₀ : ℕ} (hL₀ : φ.rOut < 2 ^ L₀ * φ.rIn) {k : ℕ}
    {ζ : CoordinateSpace n} (hup : ‖ζ‖ < 2 ^ (k + 1) * φ.rOut)
    (hlow : k ≠ 0 → 2 ^ k * φ.rIn / 4 < ‖ζ‖) : φ.enlargedLittlewoodPaley (L₀ + 3) k ζ = 1 := by
  have hrIn := φ.rIn_pos
  have hφ1 : φ (((2 : ℝ) ^ (k + L₀ + 2))⁻¹ • ζ) = 1 := by
    refine φ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, norm_inv, norm_pow, Real.norm_two, inv_mul_le_iff₀ (by positivity)]
    calc ‖ζ‖ ≤ 2 ^ (k + 1) * φ.rOut := hup.le
      _ ≤ 2 ^ (k + 1) * (2 ^ L₀ * φ.rIn) := by gcongr
      _ ≤ 2 ^ (k + L₀ + 2) * φ.rIn := by
          have h := mul_pos (mul_pos (pow_pos (two_pos : (0 : ℝ) < 2) k)
            (pow_pos (two_pos : (0 : ℝ) < 2) L₀)) hrIn
          rw [pow_add, pow_add, pow_add]
          nlinarith
  rw [ContDiffBump.enlargedLittlewoodPaley_apply, Finset.sum_Ico_eq_sub _ (by omega),
    show k + (L₀ + 3) = (k + L₀ + 2) + 1 by omega, φ.sum_inhomogeneousLittlewoodPaley_range, hφ1]
  rcases le_or_gt k (L₀ + 2) with hk | hk
  · simp [show k + 1 - (L₀ + 3) = 0 by omega]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + L₀ + 3 := ⟨k - (L₀ + 3), by omega⟩
  rw [show j + L₀ + 3 + 1 - (L₀ + 3) = j + 1 by omega, φ.sum_inhomogeneousLittlewoodPaley_range,
    φ.zero_of_le_dist, sub_zero]
  rw [dist_zero_right, norm_smul, norm_inv, norm_pow, Real.norm_two,
    le_inv_mul_iff₀ (by positivity)]
  calc 2 ^ j * φ.rOut ≤ 2 ^ j * (2 ^ L₀ * φ.rIn) := by gcongr
    _ ≤ 2 ^ (j + L₀ + 3) * φ.rIn / 4 := by
        have h := mul_pos (mul_pos (pow_pos (two_pos : (0 : ℝ) < 2) j)
          (pow_pos (two_pos : (0 : ℝ) < 2) L₀)) hrIn
        rw [pow_add, pow_add]
        nlinarith
    _ ≤ ‖ζ‖ := (hlow (by omega)).le

/-- **The enlarged cutoff is `1` near the spectrum of the `k`-th piece**, for a width depending
only on `φ`. -/
private theorem exists_tsupport_enlargedLittlewoodPaley_sub_one_subset :
    ∃ L : ℕ, ∀ k, tsupport (fun ζ ↦ ((φ.enlargedLittlewoodPaley L k ζ : ℝ) : ℂ) - 1) ⊆
      offSpectrum φ k := by
  obtain ⟨L₀, hL₀⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  have hrIn := φ.rIn_pos
  have hrOut := φ.rOut_pos
  refine ⟨L₀ + 3, fun k ↦ ?_⟩
  set U : Set (CoordinateSpace n) := ball 0 (2 ^ (k + 1) * φ.rOut) ∩
    (if k = 0 then Set.univ else (closedBall 0 (2 ^ k * φ.rIn / 4))ᶜ)
  have hU : IsOpen U := isOpen_ball.inter (by split_ifs <;> simp [isOpen_univ, isClosed_closedBall])
  -- The window cutoff is `1` on `U`.
  have h1 (ζ : CoordinateSpace n) (hζ : ζ ∈ U) : φ.enlargedLittlewoodPaley (L₀ + 3) k ζ = 1 :=
    enlargedLittlewoodPaley_eq_one φ hL₀ (mem_ball_zero_iff.1 hζ.1) fun hk ↦ by
      have h := hζ.2
      rw [ite_eq_right hk] at h
      simpa using h
  -- `U` contains the spectrum.
  have h2 : Uᶜ ⊆ offSpectrum φ k := by
    intro ζ hζ
    simp only [U, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or, mem_ball_zero_iff,
      not_lt] at hζ
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [offSpectrum, ite_true, Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]
      rcases hζ with hζ | hζ
      · simp only [zero_add, pow_one] at hζ
        linarith
      · simp at hζ
    · simp only [offSpectrum, ite_eq_right hk, Set.mem_union, mem_ball_zero_iff, Set.mem_compl_iff,
        mem_closedBall_zero_iff, not_le]
      rw [ite_eq_right hk] at hζ
      rcases hζ with hζ | hζ
      · right
        calc 2 ^ k * φ.rOut < 2 ^ (k + 1) * φ.rOut := by
              rw [pow_succ]
              nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k]
          _ ≤ ‖ζ‖ := hζ
      · left
        have h := mem_closedBall_zero_iff.1 (not_not.1 hζ)
        have : 0 < 2 ^ k * φ.rIn := by positivity
        linarith
  refine (closure_minimal (fun ζ hζ ↦ ?_) hU.isClosed_compl).trans h2
  intro hζU
  exact hζ (by simp [h1 ζ hζU])

/-- **Quantization of a block.** For a uniform symbol `a` of order `0` there is `C`, depending
only on `a` and `φ`, with the following property. For `1 ≤ p ≤ ∞`, if the Fourier transform of
`f ∈ Lᵖ` vanishes off the spectrum of the `k`-th Littlewood–Paley piece, then `Op(a) f` is an `Lᵖ`
function of norm at most `C ‖f‖_p`. -/
private theorem IsUniform.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
      (f : Lp F p (volume : Measure (CoordinateSpace n))),
      IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
        (offSpectrum φ k) →
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        quantizeTempered F a ha f = v ∧ ‖v‖ ≤ C * ‖f‖ := by
  obtain ⟨L, hL⟩ := exists_tsupport_enlargedLittlewoodPaley_sub_one_subset φ
  obtain ⟨C, hC, hpiece⟩ :=
    ha.exists_quantizeTempered_dyadicPiece_eq_and_norm_le (F := F) (twoPiDilate φ)
  refine ⟨2 * L * C, by positivity, fun k {p} _ f hf ↦ ?_⟩
  set g : CoordinateSpace n → ℂ := fun ζ ↦ ((φ.enlargedLittlewoodPaley L k ζ : ℝ) : ℂ)
  have hg : g.HasTemperateGrowth := φ.hasTemperateGrowth_ofReal_enlargedLittlewoodPaley L k
  have hgf : fourierMultiplierCLM F g (f : 𝓢'(CoordinateSpace n, F)) = f :=
    fourierMultiplierCLM_eq_self_of_isVanishingOn hf hg (hL k)
  set s := Finset.Ico (k + 1 - L) (k + L)
  have hb (i : ℕ) := isUniform_dyadicPiece (twoPiDilate φ) ha i
  have hq : quantizeTempered F a ha (f : 𝓢'(CoordinateSpace n, F)) =
      ∑ i ∈ s, quantizeTempered F (dyadicPiece (twoPiDilate φ) a i) (hb i) f := by
    conv_lhs => rw [← hgf]
    rw [ha.quantizeTempered_fourierMultiplierCLM (IsUniform.sum fun i _ ↦ hb i) hg ?_,
      quantizeTempered_sum hb s, sum_apply]
    intro x ξ
    simp only [coefficient_sum, Finset.sum_apply, coefficient_dyadicPiece,
      coefficient_littlewoodPaleyPiece, inhomogeneousLittlewoodPaley_twoPiDilate, g,
      ContDiffBump.enlargedLittlewoodPaley_apply, ← Finset.sum_smul, Complex.coe_smul, s]
  choose v hv hvn using fun i ↦ hpiece i f
  refine ⟨∑ i ∈ s, v i, ?_, ?_⟩
  · rw [hq, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hv i
  · calc ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, C * ‖f‖ := Finset.sum_le_sum fun i _ ↦ hvn i
      _ = s.card * (C * ‖f‖) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * L : ℕ) * (C * ‖f‖) := by
          gcongr
          rw [Nat.card_Ico]
          omega
      _ = 2 * L * C * ‖f‖ := by push_cast; ring

private theorem compl_closedBall_subset_offSpectrum (k : ℕ) :
    (closedBall (0 : CoordinateSpace n) (2 ^ k * φ.rOut))ᶜ ⊆ offSpectrum φ k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [offSpectrum]
  · simp only [offSpectrum, ite_eq_right hk]
    exact Set.subset_union_right

/-- **Derivatives of the quantization of a block.** For a uniform symbol `a` of order `0` and
directions `w₁, …, w_M`, there is `C` such that for `1 ≤ p ≤ ∞`, if the Fourier transform of
`f ∈ Lᵖ` vanishes off the spectrum of the `k`-th Littlewood–Paley piece, then
`∂_{w₁} ⋯ ∂_{w_M} Op(a) f` is an `Lᵖ` function of norm at most `C 2^{kM} ‖f‖_p`. -/
private theorem IsUniform.exists_iteratedLineDerivOp_quantizeTempered_eq_and_norm_le (M : ℕ) :
    ∀ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (w : Fin M → CoordinateSpace n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
        (f : Lp F p (volume : Measure (CoordinateSpace n))),
        IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
          (offSpectrum φ k) →
        ∃ y : Lp F p (volume : Measure (CoordinateSpace n)),
          ∂^{w} (quantizeTempered F a ha f) = y ∧ ‖y‖ ≤ C * (2 ^ k) ^ M * ‖f‖ := by
  induction M with
  | zero =>
    intro a ha w
    obtain ⟨C, hC, h⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
    refine ⟨C, hC, fun k {p} _ f hf ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := h k f hf
    exact ⟨v, by rw [LineDeriv.iteratedLineDerivOp_fin_zero, hv], by simpa using hvn⟩
  | succ M ih =>
    intro a ha w
    set v := w (Fin.last M)
    obtain ⟨C₁, hC₁, h₁⟩ := ih ha (Fin.init w)
    obtain ⟨C₂, hC₂, h₂⟩ := ih (ha.dirSpatialDeriv v) (Fin.init w)
    obtain ⟨CB, hCB, hB⟩ :=
      exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := F)
    have hrOut := φ.rOut_pos
    refine ⟨C₁ * (CB * φ.rOut * ‖v‖) + C₂, by positivity, fun k {p} _ f hf ↦ ?_⟩
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    -- `∂_v f` is again a block, smaller by `2^k`.
    obtain ⟨g, hg, hgn⟩ := hB (p := p) (R := 2 ^ k * φ.rOut) (by positivity) f
      (hf.mono (compl_closedBall_subset_offSpectrum φ k)) v
    have hgv : IsVanishingOn (𝓕 (g : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
        (offSpectrum φ k) := hg ▸ isVanishingOn_fourier_lineDerivOp hf v
    obtain ⟨y₁, hy₁, hy₁n⟩ := h₁ k g hgv
    obtain ⟨y₂, hy₂, hy₂n⟩ := h₂ k f hf
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [LineDeriv.iteratedLineDerivOp_succ_right, lineDerivOp_quantizeTempered_eq_add, hg,
        LineDeriv.iteratedLineDerivOp_add, hy₁, hy₂, Lp.toTemperedDistribution_add]
    · calc ‖y₁ + y₂‖ ≤ ‖y₁‖ + ‖y₂‖ := norm_add_le _ _
        _ ≤ C₁ * (2 ^ k) ^ M * (CB * (2 ^ k * φ.rOut) * ‖v‖ * ‖f‖) +
            C₂ * (2 ^ k) ^ M * ‖f‖ := add_le_add (hy₁n.trans (by gcongr)) hy₂n
        _ ≤ (C₁ * (CB * φ.rOut * ‖v‖) + C₂) * (2 ^ k) ^ (M + 1) * ‖f‖ := by
          have hM : 0 ≤ C₂ * (2 ^ k) ^ M * ‖f‖ := by positivity
          rw [pow_succ]
          nlinarith

/-- **High output frequencies.** For a uniform symbol `a` of order `0` and `M : ℕ` there is `C`
such that for `1 ≤ p ≤ ∞` and `k < j`, if the Fourier transform of `f ∈ Lᵖ` vanishes off the
spectrum of the `k`-th Littlewood–Paley piece, then `‖Δⱼ Op(a) f‖_p ≤ C (2^k / 2^j)^M ‖f‖_p`. -/
private theorem IsUniform.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_lt
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {j k : ℕ}, k < j →
      ∀ f : Lp F p (volume : Measure (CoordinateSpace n)),
        IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
          (offSpectrum φ k) →
        ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
          littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
            ‖v‖ ≤ C * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  set b := stdOrthonormalBasis ℝ (CoordinateSpace n)
  obtain ⟨Cr, hCr, hrev⟩ :=
    exists_norm_littlewoodPaleyBlock_succ_le_of_iteratedLineDerivOp (F := F) φ M
  choose C hC hder using fun i : Fin M → Fin (Module.finrank ℝ (CoordinateSpace n)) ↦
    ha.exists_iteratedLineDerivOp_quantizeTempered_eq_and_norm_le (F := F) φ M (⇑b ∘ i)
  obtain ⟨C₀, -, hD⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  have hCs : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ hC i
  refine ⟨Cr * (∑ i, C i) * 2 ^ M, by positivity, fun {p} _ {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨v₀, hv₀, -⟩ := hD k f hf
  obtain ⟨w, hw, -⟩ := hΔ (j + 1) v₀
  have hwT : littlewoodPaleyBlock F φ (j + 1) (quantizeTempered F a ha f) = w := by
    rw [hv₀, hw]
  refine ⟨w, hwT, ?_⟩
  have hA (i : Fin M → Fin (Module.finrank ℝ (CoordinateSpace n))) :
      ∃ y : Lp F p (volume : Measure (CoordinateSpace n)),
        ∂^{⇑b ∘ i} (quantizeTempered F a ha f) = y ∧ ‖y‖ ≤ (∑ i, C i) * (2 ^ k) ^ M * ‖f‖ := by
    obtain ⟨y, hy, hyn⟩ := hder i k f hf
    have hCi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ i)
    exact ⟨y, hy, hyn.trans (by gcongr)⟩
  refine (hrev j (quantizeTempered F a ha f) w hwT hA).trans_eq ?_
  rw [div_pow, pow_succ, mul_pow]
  field_simp

private theorem offSpectrum_succ (k : ℕ) :
    offSpectrum φ (k + 1) = ball (0 : CoordinateSpace n) (2 ^ k * φ.rIn) ∪
      (closedBall 0 (2 * φ.rOut / φ.rIn * (2 ^ k * φ.rIn)))ᶜ := by
  rw [φ.two_mul_rOut_div_rIn_mul, offSpectrum, ite_eq_right k.succ_ne_zero,
    show 2 ^ (k + 1) * φ.rIn / 2 = 2 ^ k * φ.rIn by ring]

variable (F) in
/-- The bound `‖Δⱼ Op(a) f‖_p ≤ C (2^j / 2^k)^N ‖f‖_p` for every `1 ≤ p ≤ ∞`, every `j` and every
`f ∈ Lᵖ` whose Fourier transform vanishes off the spectrum of the `(k + 1)`-st Littlewood–Paley
piece. -/
private def LowFrequencyBound (a : Symbol n ℂ ℂ 0) (ha : a.IsUniform) (N : ℕ) (C : ℝ) : Prop :=
  ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (f : Lp F p (volume : Measure (CoordinateSpace n))),
    IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
      (offSpectrum φ (k + 1)) →
    ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
      littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
        ‖v‖ ≤ C * ((2 : ℝ) ^ j / 2 ^ k) ^ N * ‖f‖

omit [CompleteSpace F] in
/-- The commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` applied to a sum of derivatives, and
moved through the block `Δⱼ`. -/
private theorem littlewoodPaleyBlock_quantizeTempered_sum_lineDerivOp {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) (j : ℕ) (g : Fin n → 𝓢'(CoordinateSpace n, F)) :
    littlewoodPaleyBlock F φ j
        (quantizeTempered F a ha (∑ i, ∂_{EuclideanSpace.basisFun (Fin n) ℝ i} (g i))) =
      ∑ i, (∂_{EuclideanSpace.basisFun (Fin n) ℝ i}
          (littlewoodPaleyBlock F φ j (quantizeTempered F a ha (g i))) -
        littlewoodPaleyBlock F φ j
          (quantizeTempered F (Symbol.spatialDeriv i a) (ha.spatialDeriv i) (g i))) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [EuclideanSpace.basisFun_apply,
    eq_sub_of_add_eq (lineDerivOp_quantizeTempered a ha i (g i)).symm, map_sub,
    littlewoodPaleyBlock_lineDerivOp]

/-- **The inductive step for low output frequencies.** Writing `f = ∑ᵢ ∂ᵢ gᵢ` with
`‖gᵢ‖_p = O(2^{-k} ‖f‖_p)`, the commutator `Op(a) ∂ᵢ = ∂ᵢ Op(a) - Op(∂_{x_i} a)` moves the
derivative onto the block `Δⱼ`, where it costs `2^j`: bounds of order `N` for `a` and its spatial
derivatives give a bound of order `N + 1` for `a`. -/
private theorem IsUniform.exists_lowFrequencyBound_succ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (h : LowFrequencyBound F φ a ha N C) {C' : Fin n → ℝ}
    (hC' : ∀ i, 0 ≤ C' i)
    (h' : ∀ i, LowFrequencyBound F φ (Symbol.spatialDeriv i a) (ha.spatialDeriv i) N (C' i)) :
    ∃ C'' : ℝ, LowFrequencyBound F φ a ha (N + 1) C'' := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨c, -, hdec⟩ := b.exists_eq_sum_lineDerivOp_and_norm_le (F := F) (2 * φ.rOut / φ.rIn)
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := CoordinateSpace n) (F := F)
  have hrIn := φ.rIn_pos
  have hrOut := φ.rOut_pos
  refine ⟨∑ i, (CB * φ.rOut * C + C' i) * (c / φ.rIn), fun {p} _ j k f hf ↦ ?_⟩
  obtain ⟨g, hfg, hg⟩ := hdec (by positivity : (0 : ℝ) < 2 ^ k * φ.rIn) f
    (by rw [← offSpectrum_succ]; exact hf)
  choose v hv hvn using fun i ↦ h j k (g i) (offSpectrum_succ φ k ▸ (hg i).1)
  choose z hz hzn using fun i ↦ h' i j k (g i) (offSpectrum_succ φ k ▸ (hg i).1)
  -- The blocks `v i = Δⱼ Op(a) gᵢ` have spectrum in the ball of radius `2^j φ.rOut`.
  choose y hy hyn using fun i ↦ hB (p := p) (by positivity : (0 : ℝ) < 2 ^ j * φ.rOut) (v i)
    (hv i ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ j _) (b i)
  refine ⟨∑ i, (y i - z i), ?_, ?_⟩
  · rw [hfg, littlewoodPaleyBlock_quantizeTempered_sum_lineDerivOp, Lp.toTemperedDistribution_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hv, hy, hz, Lp.toTemperedDistribution_sub]
  set r : ℝ := 2 ^ j / 2 ^ k
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have hterm (i : Fin n) : ‖y i - z i‖ ≤
      (CB * φ.rOut * C + C' i) * (c / φ.rIn) * r ^ (N + 1) * ‖f‖ := by
    have hb1 : ‖b i‖ = 1 := b.orthonormal.1 i
    have hgi := (hg i).2
    have hCi := hC' i
    calc ‖y i - z i‖ ≤ ‖y i‖ + ‖z i‖ := norm_sub_le _ _
      _ ≤ CB * (2 ^ j * φ.rOut) * ‖b i‖ * (C * r ^ N * ‖g i‖) + C' i * r ^ N * ‖g i‖ :=
          add_le_add ((hyn i).trans (by gcongr; exact hvn i)) (hzn i)
      _ = (CB * φ.rOut * C * 2 ^ j + C' i) * r ^ N * ‖g i‖ := by rw [hb1]; ring
      _ ≤ (CB * φ.rOut * C * 2 ^ j + C' i * 2 ^ j) * r ^ N * (c / (2 ^ k * φ.rIn) * ‖f‖) := by
          gcongr
          exact le_mul_of_one_le_right hCi hj
      _ = _ := by
          rw [show (2 : ℝ) ^ j = r * 2 ^ k by simp only [r]; field_simp, pow_succ]
          field_simp
  calc ‖∑ i, (y i - z i)‖ ≤ ∑ i, ‖y i - z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (CB * φ.rOut * C + C' i) * (c / φ.rIn) * r ^ (N + 1) * ‖f‖ :=
        Finset.sum_le_sum fun i _ ↦ hterm i
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- **Low output frequencies.** For a uniform symbol `a` of order `0` and `N : ℕ` there is `C`
such that for `1 ≤ p ≤ ∞`, if the Fourier transform of `f ∈ Lᵖ` vanishes off the spectrum of the
`(k + 1)`-st Littlewood–Paley piece, then `‖Δⱼ Op(a) f‖_p ≤ C (2^j / 2^k)^N ‖f‖_p` for every `j`. -/
private theorem IsUniform.exists_lowFrequencyBound (N : ℕ) :
    ∀ {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform), ∃ C : ℝ, 0 ≤ C ∧ LowFrequencyBound F φ a ha N C := by
  induction N with
  | zero =>
    intro a ha
    obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
    obtain ⟨C₀, hC₀, hD⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
    refine ⟨max CΔ 0 * C₀, by positivity, fun {p} _ j k f hf ↦ ?_⟩
    obtain ⟨v₀, hv₀, hv₀n⟩ := hD (k + 1) f hf
    obtain ⟨v, hv, hvn⟩ := hΔ j v₀
    refine ⟨v, by rw [hv₀, hv], ?_⟩
    calc ‖v‖ ≤ CΔ * ‖v₀‖ := hvn
      _ ≤ max CΔ 0 * (C₀ * ‖f‖) := by gcongr; exact le_max_left _ _
      _ = _ := by rw [pow_zero, mul_one, mul_assoc]
  | succ N ih =>
    intro a ha
    obtain ⟨C, hC, h⟩ := ih ha
    choose C' hC' h' using fun i ↦ ih (ha.spatialDeriv i)
    obtain ⟨C'', h''⟩ := ha.exists_lowFrequencyBound_succ φ hC h hC' h'
    refine ⟨max C'' 0, le_max_right _ _, fun {p} _ j k f hf ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := h'' j k f hf
    exact ⟨v, hv, hvn.trans (by gcongr; exact le_max_left _ _)⟩

/-- **Almost diagonality.** For a uniform symbol `a` of order `0` and `N : ℕ` there is `K` such
that for `1 ≤ p ≤ ∞` and every block `Δₖ u = f ∈ Lᵖ` of a tempered distribution, every block
`Δⱼ Op(a) f` is an `Lᵖ` function of norm at most `K 2^{-N |j - k|} ‖f‖_p`. -/
private theorem IsUniform.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j k : ℕ) (u : 𝓢'(CoordinateSpace n, F))
      (f : Lp F p (volume : Measure (CoordinateSpace n))), littlewoodPaleyBlock F φ k u = f →
      ∃ v : Lp F p (volume : Measure (CoordinateSpace n)),
        littlewoodPaleyBlock F φ j (quantizeTempered F a ha f) = v ∧
          ‖v‖ ≤ K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨C₁, hC₁, h₁⟩ :=
    ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le_of_lt (F := F) φ N
  obtain ⟨C₂, hC₂, h₂⟩ := ha.exists_lowFrequencyBound (F := F) φ N
  obtain ⟨C₀, hC₀, hD⟩ := ha.exists_quantizeTempered_eq_and_norm_le_of_isVanishingOn (F := F) φ
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨C₁ + C₂ * 2 ^ N + max CΔ 0 * C₀, by positivity, fun {p} _ j k u f hf ↦ ?_⟩
  have hfv : IsVanishingOn (𝓕 (f : 𝓢'(CoordinateSpace n, F)) : 𝓢'(CoordinateSpace n, F))
      (offSpectrum φ k) := hf ▸ isVanishingOn_offSpectrum φ k u
  have hK (K : ℝ) (hKK : K ≤ C₁ + C₂ * 2 ^ N + max CΔ 0 * C₀) :
      K * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖f‖ ≤
        (C₁ + C₂ * 2 ^ N + max CΔ 0 * C₀) * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖f‖ := by
    gcongr
  have hC₂' : 0 ≤ C₂ * 2 ^ N := by positivity
  have hC₀' : 0 ≤ max CΔ 0 * C₀ := by positivity
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · -- High output frequency.
    obtain ⟨v, hv, hvn⟩ := h₁ hkj f hfv
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK C₁ (by linarith))⟩
    rw [Real.pow_div_pow_pow_eq_rpow_of_le two_pos hkj.le]
  · -- Equal frequencies: `Op(a)` is bounded on the block, and so is `Δⱼ`.
    obtain ⟨v₀, hv₀, hv₀n⟩ := hD k f hfv
    obtain ⟨v, hv, hvn⟩ := hΔ k v₀
    refine ⟨v, by rw [hv₀, hv], ?_⟩
    calc ‖v‖ ≤ max CΔ 0 * C₀ * (2 : ℝ) ^ (-(N * |(k : ℝ) - k|)) * ‖f‖ := by
          rw [sub_self, abs_zero, mul_zero, neg_zero, Real.rpow_zero, mul_one, mul_assoc]
          calc ‖v‖ ≤ CΔ * ‖v₀‖ := hvn
            _ ≤ max CΔ 0 * (C₀ * ‖f‖) := by gcongr; exact le_max_left _ _
      _ ≤ _ := hK _ (by linarith)
  · -- Low output frequency: the block `f` has spectrum in the `k`-th dyadic annulus.
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨v, hv, hvn⟩ := h₂ j k f hfv
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK (C₂ * 2 ^ N) (by linarith))⟩
    rw [abs_sub_comm, ← Real.pow_div_pow_pow_eq_rpow_of_le two_pos hjk.le, div_pow, div_pow,
      pow_succ]
    field_simp
    ring

end Dyadic

/-! ### Mapping properties on Besov spaces -/

section Besov

open Distribution TemperedDistribution

variable [CompleteSpace F] {φ : ContDiffBump (0 : CoordinateSpace n)} {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Uniform symbols of order zero on Besov spaces.** A symbol `a` of order `0` whose estimates
are uniform in the position quantizes to a bounded operator on every Besov space
`B^s_{p,q}`. -/
private theorem IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le_of_zero
    {a : Symbol n ℂ ℂ 0} (ha : a.IsUniform) (s : ℝ) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ s p q,
      v.toDistr = quantizeTempered F a ha u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set N : ℕ := ⌊|s|⌋₊ + 1
  have hN : |s| < N := by
    simp only [N, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨K, hK, hT⟩ := ha.exists_littlewoodPaleyBlock_quantizeTempered_eq_and_norm_le (F := F) φ N
  refine ⟨K * ∑' d : ℤ, ((2 : ℝ) ^ (|s| - N)) ^ d.natAbs, fun u ↦ ?_⟩
  exact BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le
    (quantizeTempered F a ha) hN hK u fun j k ↦ hT j k u.toDistr (u.block k)
      (BesovSpace.coe_block u k).symm

/-- **Pseudodifferential operators on Besov spaces.** A symbol `a` of order `m` whose estimates
are uniform in the position quantizes to a bounded operator `B^s_{p,q} → B^{s-m}_{p,q}`, for every
real `s` and all `1 ≤ p, q ≤ ∞`. For `p = q = ∞` this is the mapping `𝒞^s → 𝒞^{s-m}` of the
Hölder–Zygmund scale. -/
theorem IsUniform.exists_toDistr_eq_quantizeTempered_and_norm_le {a : Symbol n ℂ ℂ m}
    (ha : a.IsUniform) (s : ℝ) :
    ∃ C : ℝ, ∀ u : BesovSpace F φ s p q, ∃ v : BesovSpace F φ (s - m) p q,
      v.toDistr = quantizeTempered F a ha u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  set J := BesovSpace.besselPotentialEquiv F φ p q m (s := s) rfl
  obtain ⟨C₀, h₀⟩ := ((ha.comp (isUniform_besselPotential (-m))).inclusion
    (add_neg_cancel m).le).exists_toDistr_eq_quantizeTempered_and_norm_le_of_zero (F := F)
      (φ := φ) (p := p) (q := q) (s - m)
  refine ⟨max C₀ 0 * ‖(J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q)‖,
    fun u ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := h₀ (J u)
  refine ⟨v, ?_, ?_⟩
  · rw [hv, BesovSpace.toDistr_besselPotentialEquiv, ← ha.quantizeTempered_eq_comp_besselPotential]
  · calc ‖v‖ ≤ C₀ * ‖J u‖ := hvn
      _ ≤ max C₀ 0 * ‖J u‖ := by gcongr; exact le_max_left _ _
      _ ≤ max C₀ 0 * (‖(J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q)‖ * ‖u‖) := by
          gcongr
          exact (J : BesovSpace F φ s p q →L[ℂ] BesovSpace F φ (s - m) p q).le_opNorm u
      _ = _ := by ring

/-- **Pseudodifferential operators preserve Besov regularity up to their order.** If `u` lies in
the Besov space `B^s_{p,q}` and `a` is a symbol of order `m` whose estimates are uniform in the
position, then `Op(a) u` lies in `B^{s-m}_{p,q}`. -/
theorem _root_.TemperedDistribution.MemBesov.quantizeTempered {s : ℝ}
    {u : 𝓢'(CoordinateSpace n, F)} (hu : u.MemBesov φ s p q)
    {a : Symbol n ℂ ℂ m} (ha : a.IsUniform) :
    (quantizeTempered F a ha u).MemBesov φ (s - m) p q := by
  obtain ⟨C, hC⟩ := ha.exists_toDistr_eq_quantizeTempered_and_norm_le (F := F) (φ := φ)
    (p := p) (q := q) s
  obtain ⟨v, hv, -⟩ := hC hu.toBesovSpace
  rw [hu.toDistr_toBesovSpace] at hv
  exact hv ▸ v.memBesov_toDistr

variable (F φ p q) in
/-- **Pseudodifferential operators on Besov spaces.** For a symbol `a` of order `m` whose
estimates are uniform in the position, the quantization `Op(a)` as a bounded operator
`B^s_{p,q} → B^{s'}_{p,q}` for `s' = s - m`. It is the restriction of the action of `Op(a)` on
tempered distributions (`TauCeti.Symbol.toDistr_quantizeBesov`). -/
def quantizeBesov (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) {s s' : ℝ} (hs : s' = s - m) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s' p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := MemBesov.toBesovSpace (u := quantizeTempered F a ha u.toDistr)
        (by subst hs; exact u.memBesov_toDistr.quantizeTempered ha)
      map_add' u v := BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, BesovSpace.toDistr_add, map_add]
      map_smul' c u := BesovSpace.ext <| by
        simp only [MemBesov.toDistr_toBesovSpace, BesovSpace.toDistr_smul, map_smul,
          RingHom.id_apply] } <| by
    subst hs
    obtain ⟨C, hC⟩ := ha.exists_toDistr_eq_quantizeTempered_and_norm_le (F := F) (φ := φ)
      (p := p) (q := q) s
    refine ⟨C, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC u
    refine le_of_eq_of_le (congrArg norm (BesovSpace.ext ?_)) hvn
    simp only [LinearMap.coe_mk, AddHom.coe_mk, MemBesov.toDistr_toBesovSpace, hv]

/-- On tempered distributions, `TauCeti.Symbol.quantizeBesov` acts as `Op(a)`. -/
@[simp]
theorem toDistr_quantizeBesov (a : Symbol n ℂ ℂ m) (ha : a.IsUniform) {s s' : ℝ}
    (hs : s' = s - m) (u : BesovSpace F φ s p q) :
    (quantizeBesov F φ p q a ha hs u).toDistr = quantizeTempered F a ha u.toDistr :=
  MemBesov.toDistr_toBesovSpace _

end Besov

end Symbol

end TauCeti

