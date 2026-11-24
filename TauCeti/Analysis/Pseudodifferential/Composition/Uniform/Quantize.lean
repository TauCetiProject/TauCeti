/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Uniform.Basic
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Symbol.UniformlySmoothing
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Distribution.SchwartzSpace.Cutoff
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Analysis.Pseudodifferential.Symbol.Map

/-!
# Operator composition, associativity, and frequency multipliers for uniform symbols

This file completes the algebraic and operator calculus of `TauCeti.Symbol.uniformSharp`:
linearity, order inclusions, smoothing and uniformly smoothing ideals, and the operator composition
formula `Op(a #_u b) u = Op(a) (Op(b) u)` on Schwartz space
(`TauCeti.Symbol.quantizeSchwartzValue_uniformSharp`,
`TauCeti.Symbol.quantizeUniformCLM_uniformSharp`), proved by dyadic spatial truncation. Uniqueness
of a symbol from its quantization
(`TauCeti.Symbol.coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq`) then gives
associativity (`TauCeti.Symbol.uniformSharp_assoc`), the right identity law
(`TauCeti.Symbol.uniformSharp_const_id`), and exact composition with frequency multipliers and
Mathlib's Bessel potentials (`TauCeti.Symbol.uniformSharp_ofFrequency`,
`TauCeti.Symbol.uniformSharp_besselPotential`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §2.
-/

public section

open MeasureTheory Real FourierTransform Filter Function
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap Topology

noncomputable section

namespace TauCeti.Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### Linearity, order inclusions, and smoothing ideals -/

section LinearAndSmoothing

variable {a : Symbol n W U m'} {b : Symbol n V W m}

@[simp]
theorem zero_uniformSharp (hb : b.IsUniform) : (0 : Symbol n W U m').uniformSharp b hb = 0 := by
  simpa using smul_uniformSharp (0 : ℂ) (0 : Symbol n W U m') hb

@[simp]
theorem uniformSharp_zero (a : Symbol n W U m')
    (h : (0 : Symbol n V W m).IsUniform := isUniform_zero) :
    a.uniformSharp (0 : Symbol n V W m) h = 0 := by
  simpa using uniformSharp_smul a h 0

@[simp]
theorem neg_uniformSharp (a : Symbol n W U m') (hb : b.IsUniform) :
    (-a).uniformSharp b hb = -a.uniformSharp b hb := by
  simpa using smul_uniformSharp (-1 : ℂ) a hb

@[simp]
theorem uniformSharp_neg (a : Symbol n W U m') (hb : b.IsUniform)
    (hnb : (-b).IsUniform := hb.neg) :
    a.uniformSharp (-b) hnb = -a.uniformSharp b hb := by
  have heq : -b = (-1 : ℂ) • b := (neg_one_smul ℂ b).symm
  simpa [← heq] using uniformSharp_smul a hb (-1)

theorem sub_uniformSharp (a₁ a₂ : Symbol n W U m') (hb : b.IsUniform) :
    (a₁ - a₂).uniformSharp b hb = a₁.uniformSharp b hb - a₂.uniformSharp b hb := by
  rw [sub_eq_add_neg, add_uniformSharp, neg_uniformSharp, ← sub_eq_add_neg]

theorem uniformSharp_sub (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.IsUniform) (hb₂ : b₂.IsUniform) (hb₁₂ : (b₁ - b₂).IsUniform := hb₁.sub hb₂) :
    a.uniformSharp (b₁ - b₂) hb₁₂ = a.uniformSharp b₁ hb₁ - a.uniformSharp b₂ hb₂ := by
  have h1 : a.uniformSharp (b₁ - b₂) hb₁₂ = a.uniformSharp (b₁ + -b₂) (hb₁.add hb₂.neg) := by
    simp only [sub_eq_add_neg]
  rw [h1, uniformSharp_add a hb₁ hb₂.neg, uniformSharp_neg a hb₂ hb₂.neg, ← sub_eq_add_neg]

theorem inclusion_uniformSharp {m'' : ℝ} (h : m' ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    (Symbol.inclusion h a).uniformSharp b hb =
      Symbol.inclusion (by linarith) (a.uniformSharp b hb) :=
  Symbol.ext ((coefficient_uniformSharp_congr hb hb (coefficient_inclusion h a) rfl).trans
    (coefficient_inclusion _ _).symm)

theorem uniformSharp_inclusion {m'' : ℝ} (h : m ≤ m'') (a : Symbol n W U m') (hb : b.IsUniform) :
    a.uniformSharp (Symbol.inclusion h b) (hb.inclusion h) =
      Symbol.inclusion (by linarith) (a.uniformSharp b hb) :=
  Symbol.ext ((coefficient_uniformSharp_congr (hb.inclusion h) hb rfl
    (coefficient_inclusion h b)).trans (coefficient_inclusion _ _).symm)

/-- Smoothing symbols form a right ideal for `uniformSharp`. -/
theorem IsSmoothing.uniformSharp_right (ha : a.IsSmoothing) (b : Symbol n V W m)
    (hb : b.IsUniform) : (a.uniformSharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨a', ha'⟩ := isSmoothing_iff.1 ha (m'' - m)
  exact ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb),
    (coefficient_inclusion _ _).trans (coefficient_uniformSharp_congr hb hb ha' rfl)⟩

/-- Uniformly smoothing symbols form a right ideal under `uniformSharp` with uniform symbols. -/
theorem IsUniformlySmoothing.uniformSharp_right (ha : a.IsUniformlySmoothing)
    (hb : b.IsUniform) : (a.uniformSharp b hb).IsUniformlySmoothing :=
  isUniformlySmoothing_iff.2 fun m'' ↦ by
    obtain ⟨a', ha'u, ha'⟩ := isUniformlySmoothing_iff.1 ha (m'' - m)
    exact ⟨Symbol.inclusion (by linarith) (a'.uniformSharp b hb),
      (ha'u.uniformSharp hb).inclusion _,
      (coefficient_inclusion _ _).trans (coefficient_uniformSharp_congr hb hb ha' rfl)⟩

/-- Uniformly smoothing symbols form a left ideal under `uniformSharp` with uniform symbols. -/
theorem IsUniformlySmoothing.uniformSharp_left (hb : b.IsUniformlySmoothing)
    (ha : a.IsUniform) (hbu : b.IsUniform := hb.isUniform) :
    (a.uniformSharp b hbu).IsUniformlySmoothing :=
  isUniformlySmoothing_iff.2 fun m'' ↦ by
    obtain ⟨b', hb'u, hb'⟩ := isUniformlySmoothing_iff.1 hb (m'' - m')
    exact ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u),
      (ha.uniformSharp hb'u).inclusion _,
      (coefficient_inclusion _ _).trans (coefficient_uniformSharp_congr hb'u hbu rfl hb')⟩

/-- Composing any symbol `a` on the right with a uniformly smoothing symbol `b` yields a smoothing
symbol. -/
theorem IsSmoothing.uniformSharp_left (hbs : b.IsUniformlySmoothing) (a : Symbol n W U m')
    (hb : b.IsUniform := hbs.isUniform) : (a.uniformSharp b hb).IsSmoothing :=
  isSmoothing_iff.2 fun m'' ↦ by
    obtain ⟨b', hb'u, hb'⟩ := isUniformlySmoothing_iff.1 hbs (m'' - m')
    exact ⟨Symbol.inclusion (by linarith) (a.uniformSharp b' hb'u),
      (coefficient_inclusion _ _).trans (coefficient_uniformSharp_congr hb'u hb rfl hb')⟩

end LinearAndSmoothing

/-! ### Operator composition on Schwartz space via dyadic spatial truncation -/

section Operator

private def spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ)
    (b : Symbol n V W m) : Symbol n V W m :=
  smulLeft (Complex.ofRealCLM.contDiff.comp (φ.contDiff.comp
    (contDiff_id.const_smul ((2 : ℝ) ^ N)⁻¹))) b

private theorem coefficient_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ)
    (b : Symbol n V W m) (y ξ : CoordinateSpace n) :
    (spatialTrunc φ N b).coefficient (y, ξ) =
      (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ) • b.coefficient (y, ξ) := by
  simp [spatialTrunc]

private theorem hasCompactSpatialSupport_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n))
    (N : ℕ) (b : Symbol n V W m) : (spatialTrunc φ N b).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_smulLeft _
    ((φ.hasCompactSupport.comp_smul (inv_ne_zero (pow_ne_zero N two_ne_zero))).comp_left
      Complex.ofReal_zero) b

private theorem exists_norm_iteratedFDeriv_spatialTrunc_le
    (φ : ContDiffBump (0 : CoordinateSpace n)) {b : Symbol n V W m} (hb : b.IsUniform) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ N y ξ,
      ‖iteratedFDeriv ℝ k (fun y ↦ (spatialTrunc φ N b).coefficient (y, ξ)) y‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨Bφ, hBφ0, hBφ⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv φ.contDiff k
  choose Sb hSb0 hSb using hb.exists_norm_iteratedFDeriv_slice_le
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Bφ * Sb (k - i),
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hBφ0) (hSb0 _),
    fun N y ξ ↦ ?_⟩
  set s : ℝ := ((2 : ℝ) ^ N)⁻¹
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  have hcut : (fun y ↦ (spatialTrunc φ N b).coefficient (y, ξ)) =
      fun y ↦ φ (s • y) • b.coefficient (y, ξ) := by
    funext z; rw [coefficient_spatialTrunc]; exact Complex.coe_smul _ _
  rw [hcut]
  refine (norm_iteratedFDeriv_smul_le
    ((φ.contDiff.of_le (mod_cast le_top)).comp (contDiff_id.const_smul s))
    ((b.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)) y le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hf_le : ‖iteratedFDeriv ℝ i (fun z ↦ φ (s • z)) y‖ ≤ Bφ := by
    rw [norm_iteratedFDeriv_comp_const_smul (fun z ↦ (φ z : ℝ)) s y i, Real.norm_of_nonneg hs0]
    exact (mul_le_mul (pow_le_pow_left₀ hs0 hs1 i)
      (hBφ i (Finset.mem_range_succ_iff.1 hi) _) (norm_nonneg _)
      (by positivity)).trans_eq (by rw [one_pow, one_mul])
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hf_le (Nat.cast_nonneg _)) (hSb (k - i) y ξ)
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hBφ0)).trans_eq (by ring)

private theorem tendsto_spatialTrunc (φ : ContDiffBump (0 : CoordinateSpace n))
    (b : Symbol n V W m) (y ξ : CoordinateSpace n) :
    Tendsto (fun N ↦ (spatialTrunc φ N b).coefficient (y, ξ))
      atTop (𝓝 (b.coefficient (y, ξ))) := by
  have h0 : Tendsto (fun N : ℕ ↦ ((2 : ℝ) ^ N)⁻¹ • y) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).smul_const y
  have hφ1 : Tendsto (fun N : ℕ ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ)) atTop (𝓝 1) := by
    have h := (Complex.continuous_ofReal.tendsto (φ 0)).comp
      (((φ.continuous : Continuous fun z : CoordinateSpace n ↦ φ z).tendsto 0).comp h0)
    simpa [Function.comp_def, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)]
      using h
  simpa [coefficient_spatialTrunc] using hφ1.smul_const (b.coefficient (y, ξ))

private theorem quantizeSchwartzValue_sharp_spatialTrunc_eq [CompleteSpace W] [CompleteSpace U]
    (φ : ContDiffBump (0 : CoordinateSpace n)) (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.IsUniform) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp (spatialTrunc φ N b)
        (hasCompactSpatialSupport_spatialTrunc φ N b)).coefficient u x =
      quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM W (fun y ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ))
          (quantizeUniformCLM b hb u)) x := by
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  congr 1; ext y
  have h0 : ((2 : ℝ) ^ N)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero N two_ne_zero)
  have htgC : (fun y : CoordinateSpace n ↦ (φ (((2 : ℝ) ^ N)⁻¹ • y) : ℂ)).HasTemperateGrowth :=
    Complex.ofRealCLM.hasTemperateGrowth.comp
      ((φ.hasCompactSupport.comp_smul h0).hasTemperateGrowth
        (φ.contDiff.comp (contDiff_id.const_smul ((2 : ℝ) ^ N)⁻¹)))
  simp [spatialTrunc, quantizeSchwartzValue_smulLeft, SchwartzMap.smulLeftCLM_apply_apply htgC,
    quantizeUniformCLM_apply]

/-- **Composition of quantizations for uniform symbols.** For any symbol `a` of order `m'` and any
uniform symbol `b` of order `m`, the quantization of `a.uniformSharp b hb` on a Schwartz function
`u` equals the quantization of `a` applied to the Schwartz function `quantizeUniformCLM b hb u`. -/
theorem quantizeSchwartzValue_uniformSharp [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.uniformSharp b hb).coefficient u x =
      quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x := by
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  set cN : ℕ → Symbol n V U (m' + m) := fun N ↦
    a.sharp (spatialTrunc φ N b) (hasCompactSpatialSupport_spatialTrunc φ N b)
  obtain ⟨Ca_x, -, hCa_x⟩ := a.exists_bound_coefficient_slice x
  have hRHS_tendsto :
      Tendsto (fun N ↦ quantizeSchwartzValue (cN N).coefficient u x) atTop
        (𝓝 (quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x)) := by
    simp only [cN, quantizeSchwartzValue_sharp_spatialTrunc_eq φ _ a hb u x]
    exact ((continuous_quantizeSchwartzValue_input (a.continuous_coefficient_slice x)
      hCa_x).tendsto _).comp (SchwartzMap.tendsto_smulLeftCLM_contDiffBump
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))) φ (quantizeUniformCLM b hb u))
  obtain ⟨⟨K_x, -, hcN_bound⟩, hcN_tendsto⟩ := exists_bound_and_tendsto_coefficient_uniformSharp a
    hb (fun N ↦ (hasCompactSpatialSupport_spatialTrunc φ N b).isUniform)
    (exists_norm_iteratedFDeriv_spatialTrunc_le φ hb) (tendsto_spatialTrunc φ b) x
  have heq (N : ℕ) : (cN N).coefficient =
      (a.uniformSharp (spatialTrunc φ N b)
        (hasCompactSpatialSupport_spatialTrunc φ N b).isUniform).coefficient :=
    (coefficient_uniformSharp_eq_sharp (hasCompactSpatialSupport_spatialTrunc φ N b)).symm
  have hLHS_tendsto :
      Tendsto (fun N ↦ quantizeSchwartzValue (cN N).coefficient u x) atTop
        (𝓝 (quantizeSchwartzValue (a.uniformSharp b hb).coefficient u x)) := by
    simp only [quantizeSchwartzValue_def]
    refine tendsto_integral_of_dominated_convergence
      (fun ζ ↦ K_x * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m' + m) / 2) * ‖𝓕 u ζ‖))
      (fun N ↦ ((Real.continuous_fourierChar.comp (by fun_prop)).smul
        (((cN N).continuous_coefficient_slice x |>.comp (by fun_prop)).clm_apply
          (𝓕 u).continuous)).aestronglyMeasurable)
      (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m' + m)).const_mul K_x)
      (fun N ↦ .of_forall fun ζ ↦ ?_) (.of_forall fun ζ ↦ ?_)
    · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul, heq N]
      exact ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hcN_bound N _) (norm_nonneg _))).trans_eq (by ring)
    · simp only [heq]
      exact (((ContinuousLinearMap.apply ℂ U (𝓕 u ζ)).continuous.tendsto _).comp
        (hcN_tendsto ((2 * π) • ζ))).const_smul (𝐞 ⟪ζ, x⟫)
  exact tendsto_nhds_unique hLHS_tendsto hRHS_tendsto

/-- **Composition of uniform pseudodifferential operators on Schwartz space.** When both `a` and `b`
satisfy uniform estimates, `Op(a #_u b) = Op(a) ∘ Op(b)` as continuous linear maps on Schwartz
space. -/
theorem quantizeUniformCLM_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {a : Symbol n W U m'} {b : Symbol n V W m} (ha : a.IsUniform) (hb : b.IsUniform) :
    quantizeUniformCLM (a.uniformSharp b hb) (ha.uniformSharp hb) =
      (quantizeUniformCLM a ha).comp (quantizeUniformCLM b hb) := by
  ext u x
  rw [quantizeUniformCLM_apply, ContinuousLinearMap.comp_apply, quantizeUniformCLM_apply]
  exact quantizeSchwartzValue_uniformSharp a hb u x

/-- **Uniqueness of the uniform composition symbol.** Any symbol `c`, of any order, whose
quantization agrees with `Op(a) ∘ Op(b)` on compactly supported Schwartz functions has the
coefficient of `a.uniformSharp b hb`. -/
theorem coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.IsUniform)
    {m'' : ℝ} {c : Symbol n V U m''}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → ∀ x,
      quantizeSchwartzValue c.coefficient u x =
        quantizeSchwartzValue a.coefficient (quantizeUniformCLM b hb u) x) :
    c.coefficient = (a.uniformSharp b hb).coefficient :=
  coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦ funext fun x ↦
    (h u hu x).trans (quantizeSchwartzValue_uniformSharp a hb u x).symm

end Operator

/-! ### Associativity and composition with frequency multipliers -/

section Algebra

/-- **Associativity of uniform symbol composition.** For any symbol `a` and uniform symbols `b` and
`c`, `(a #_u b) #_u c = a #_u (b #_u c)` up to the identification of orders
`(m'' + m') + m = m'' + (m' + m)`. -/
theorem uniformSharp_assoc {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U']
    [CompleteSpace V] [CompleteSpace W] [CompleteSpace U] [CompleteSpace U'] {m'' : ℝ}
    (a : Symbol n U U' m'') {b : Symbol n W U m'} {c : Symbol n V W m}
    (hb : b.IsUniform) (hc : c.IsUniform) :
    (a.uniformSharp b hb).uniformSharp c hc =
      Symbol.inclusion (add_assoc m'' m' m).ge
        (a.uniformSharp (b.uniformSharp c hc) (hb.uniformSharp hc)) := by
  ext1; rw [coefficient_inclusion]
  refine coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a (hb.uniformSharp hc)
    fun u _ x ↦ ?_
  rw [quantizeSchwartzValue_uniformSharp (a.uniformSharp b hb) hc,
    quantizeSchwartzValue_uniformSharp a hb, quantizeUniformCLM_uniformSharp hb hc]; rfl

/-- **Exact composition with a frequency multiplier on the right.** Composing any symbol `a` on the
right with `ofFrequency g hg hgbound` gives `a.comp (ofFrequency g hg hgbound)`. -/
theorem uniformSharp_ofFrequency [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') {g : CoordinateSpace n → V →L[ℂ] W} (hg : ContDiff ℝ ∞ g)
    (hgbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k g ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - k) / 2))
    (hb : (ofFrequency g hg hgbound).IsUniform := isUniform_ofFrequency hg hgbound) :
    a.uniformSharp (ofFrequency g hg hgbound) hb = a.comp (ofFrequency g hg hgbound) := by
  ext1
  refine (coefficient_eq_uniformSharp_of_forall_quantizeSchwartzValue_eq a hb fun u _ x ↦ ?_).symm
  have hgu : quantizeUniformCLM (ofFrequency g hg hgbound) hb u = quantizeFrequencyCLM g u := by
    ext y; rw [quantizeUniformCLM_apply]; exact quantizeSchwartzValue_ofFrequency hg hgbound u y
  rw [hgu, quantizeSchwartzValue_quantizeFrequencyCLM
    (Function.HasTemperateGrowth.of_norm_iteratedFDeriv_le_one_add_norm_sq_rpow hg hgbound)]
  exact quantizeSchwartzValue_congr_left
    (fun ξ ↦ by simp only [coefficient_comp, coefficient_ofFrequency]) u

/-- **Exact composition with the Bessel potential on the right.** Composing any symbol `a` on the
right with `besselPotential s` in `uniformSharp` equals `a.comp (besselPotential s)`. -/
@[simp]
theorem uniformSharp_besselPotential [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m') (s : ℝ)
    (hs : (besselPotential s : Symbol n V V s).IsUniform := isUniform_besselPotential s) :
    a.uniformSharp (besselPotential s) hs = a.comp (besselPotential s) := by
  simp only [besselPotential_eq_ofFrequency] at hs ⊢
  exact uniformSharp_ofFrequency a _ _ hs

/-- Composing any symbol `a` on the right with `const T` gives `a.comp (const T)`. -/
theorem uniformSharp_const [CompleteSpace V] [CompleteSpace W] [CompleteSpace U]
    (a : Symbol n W U m') (T : V →L[ℂ] W)
    (hT : (const T : Symbol n V W 0).IsUniform := isUniform_const T) :
    a.uniformSharp (const T) hT = a.comp (const T) := by
  have hb : ∀ k : ℕ, ∃ C, ∀ ξ : CoordinateSpace n,
      ‖iteratedFDeriv ℝ k (fun _ : CoordinateSpace n ↦ T) ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - k) / 2) :=
    fun k ↦ ⟨‖T‖, fun ξ ↦ by
      rcases k with _ | k
      · simp
      · rw [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity⟩
  have hc : (const T : Symbol n V W 0) = ofFrequency (fun _ ↦ T) contDiff_const hb := by
    ext p : 2; simp
  rw [hc] at hT
  simpa only [hc] using uniformSharp_ofFrequency a contDiff_const hb hT

/-- The constant identity symbol `1` is a right identity for `uniformSharp` up to `m' + 0 = m'`. -/
@[simp]
theorem uniformSharp_const_id [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m')
    (h : (const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0).IsUniform := isUniform_const _) :
    a.uniformSharp (const (ContinuousLinearMap.id ℂ V)) h =
      Symbol.inclusion (add_zero m').ge a := by
  rw [uniformSharp_const, comp_const_id]

/-- **Composition with a frequency multiplier on the left** for a uniform symbol `a`:
`c(D) (Op(a) u) = Op(c #_u a) u`, where `c #_u a` is uniform of order `m' + m`. -/
theorem quantizeSchwartzValue_ofFrequency_uniformSharp [CompleteSpace W] [CompleteSpace U]
    {a : Symbol n V W m} (ha : a.IsUniform) {c : CoordinateSpace n → W →L[ℂ] U}
    (hc : ContDiff ℝ ∞ c)
    (hcbound : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k c ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - k) / 2))
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue ((ofFrequency c hc hcbound).uniformSharp a ha).coefficient u x =
      quantizeFrequencyCLM c (quantizeUniformCLM a ha u) x := by
  rw [quantizeSchwartzValue_uniformSharp _ ha, quantizeSchwartzValue_ofFrequency]

/-- **Composition with Mathlib's Bessel multiplier on the left** for a uniform symbol `a`:
`J^s (Op(a) u) = Op((besselPotential s) #_u a) u`. -/
theorem quantizeSchwartzValue_besselPotential_uniformSharp [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue ((besselPotential s : Symbol n W W s).uniformSharp a ha).coefficient u x =
      SchwartzMap.fourierMultiplierCLM W
        (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))
        (quantizeUniformCLM a ha u) x := by
  rw [quantizeSchwartzValue_uniformSharp _ ha, quantizeSchwartzValue_besselPotential]

end Algebra

end TauCeti.Symbol
