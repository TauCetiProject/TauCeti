/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
public import TauCeti.Analysis.Sobolev.BesselPotential.AnalyticFamily
public import TauCeti.Analysis.Sobolev.BesselPotential.ExponentInterpolation
import TauCeti.Algebra.Order.Floor.Abs
import TauCeti.Analysis.Complex.VerticalStrip.Basic
import TauCeti.Analysis.Complex.VerticalStrip.Gaussian
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Data.ENNReal.InterpolatedExponent

/-!
# Complex interpolation of Bessel-potential spaces of different orders

Let `E` be a finite-dimensional real inner product space, `F` a complex Hilbert space and
`H^{s,p} = H^{s,p}(E, F)` Mathlib's Bessel-potential spaces. For real orders `s₀`, `s₁`, exponents
`1 < p₀, p₁ < ∞` and `0 < θ < 1`, this file proves that Calderón's complex interpolation space of
the couple `(H^{s₀,p₀}, H^{s₁,p₁})` is again a Bessel-potential space, with equivalent norms:

`[H^{s₀,p₀}, H^{s₁,p₁}]_θ = H^{s_θ,p_θ}`, `s_θ = (1 - θ) s₀ + θ s₁`,
`1 / p_θ = (1 - θ) / p₀ + θ / p₁`

(`TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodContinuousLinearEquiv`). The
isomorphism keeps the underlying tempered distribution. For `s₀ = s₁` this is
`TauCeti.CompatibleCouple.besselPotentialSpaceOfOrderComplexMethodEquiv`, and for `p₀ = p₁ = 2` it
is `TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodEquiv`, both with equal norms.

## The argument

Both inclusions are instances of Stein's interpolation theorem for the analytic family of Bessel
potentials `J^{λ(z)}`, `λ(z) = (1 - z) λ₀ + z λ₁`, between the couples
`(H^{a₀,p₀}, H^{a₁,p₁})` and `(H^{b₀,p₀}, H^{b₁,p₁})` with `λⱼ = aⱼ - bⱼ`
(`TauCeti.CompatibleCouple.exists_besselPotentialSpace_complexMethod_map`): the inclusion
`[H^{s₀,p₀}, H^{s₁,p₁}]_θ ⊆ J^{-s_θ} [L^{p₀}, L^{p₁}]_θ` is the case `a = s`, `b = 0`, and the
reverse inclusion the case `a = 0`, `b = s`. Calderón's identity
`[H^{0,p₀}, H^{0,p₁}]_θ = H^{0,p_θ}` and the isometry `J^{s_θ} : H^{s_θ,p_θ} ≃ H^{0,p_θ}` finish
the proof.

To interpolate along `J^{λ(z)}`, the family is applied to elementary admissible functions
`G z = exp (δ z² + ω z) x` with `x ∈ H^{a₀,p₀} ∩ H^{a₁,p₁}`, which are dense among all admissible
functions (Calderón's density lemma, applied through
`TauCeti.CompatibleCouple.ComplexMethodSpace.exists_map_of_forall_elementaryStripTraces`). If
`λ₀ ≤ λ₁`, the function `z ↦ J^{λ(z)} x` is computed from the component of `x` in `H^{a₁,p₁}` as
`J^{-b₁} J^{λ(z) - λ₁} J^{a₁} x`, where `re (λ(z) - λ₁) = (1 - re z) (λ₀ - λ₁) ≤ 0` on the strip,
so that `J^{λ(z) - λ₁}` is the analytic family of
`BesselPotentialSpace.besselPotentialNonposCLM` on `Lᵖ`; if `λ₀ ≥ λ₁`, from the component in
`H^{a₀,p₀}`. On the boundary lines `re z = j` the family is `J^{λⱼ}` followed by the imaginary
power `J^{i t (λ₁ - λ₀)}`, whose norm grows at most polynomially in `t`
(`BesselPotentialSpace.exists_norm_besselPotentialNonposCLM_le`). The Gaussian factor
`exp ((z - θ)²)` absorbs this growth, so the constants are uniform but the norms are only
equivalent, not equal.

## Main declarations

* `TauCeti.CompatibleCouple.exists_besselPotentialSpace_complexMethod_map`: Stein interpolation
  of the Bessel potentials between Bessel-potential couples.
* `TauCeti.CompatibleCouple.besselPotentialSpaceComplexMethodContinuousLinearEquiv`: the
  isomorphism `[H^{s₀,p₀}, H^{s₁,p₁}]_θ ≃L[ℂ] H^{s_θ,p_θ}`, with
  `TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceComplexMethodContinuousLinearEquiv_apply`.
* `TemperedDistribution.MemSobolev.map_of_memSobolev_of_memSobolev`: a continuous linear map of
  tempered distributions that maps `H^{s₀,p₀}` into `H^{t₀,p₀}` and `H^{s₁,p₁}` into `H^{t₁,p₁}`
  maps `H^{s_θ,p_θ}` into `H^{t_θ,p_θ}`.
* `TemperedDistribution.MemSobolev.map_of_forall_intCast`: a continuous linear map of tempered
  distributions that preserves `H^{k,p}` for every integer `k` with `|k| ≤ ⌈|s|⌉` preserves
  `H^{s,p}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 4.2.2, Lemma 4.2.3 and Theorem 6.4.5 (7).
* E. M. Stein, *Interpolation of linear operators*, Trans. Amer. Math. Soc. 83 (1956), 482–492.
* H. Triebel, *Interpolation Theory, Function Spaces, Differential Operators*, North-Holland,
  1978, §2.4.2, Theorem 1.
-/

public section

noncomputable section

open MeasureTheory Module Set Filter Topology TemperedDistribution Complex
open Complex.HadamardThreeLines
open TauCeti.Complex.HadamardThreeLines (stripGaussian stripGaussian_self norm_stripGaussian
  differentiable_stripGaussian)
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace BoundedContinuousFunction ZeroAtInfty

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace TauCeti

namespace CompatibleCouple

open BesselPotentialSpace

/-! ### Preliminaries -/

section Preliminaries

/-- The operator `J^{-b} J^w J^a : H^{a,q} → H^{b,q}` for `re w ≤ 0`, used both on the boundary
lines and inside the strip. Its distribution is `J^{a - b + w} u`. -/
private def shiftedFamily {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) (a b : ℝ)
    (w : ℂ) : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F) :=
  ((toOrderZeroₗᵢ E F b q).symm.toContinuousLinearEquiv : H^{0, q}(E, F) →L[ℂ] H^{b, q}(E, F)) ∘L
    besselPotentialNonposCLM hq hq_top w ∘L
      ((toOrderZeroₗᵢ E F a q).toContinuousLinearEquiv : H^{a, q}(E, F) →L[ℂ] H^{0, q}(E, F))

private theorem toDistr_shiftedFamily {q : ℝ≥0∞} [Fact (1 ≤ q)] {hq : 1 < q} {hq_top : q ≠ ∞}
    {a b : ℝ} {w : ℂ} (hw : w.re ≤ 0) (u : H^{a, q}(E, F)) :
    (shiftedFamily hq hq_top a b w u).toDistr =
      fourierMultiplierCLM F (japaneseBracketCpow (a + w - b)) u.toDistr := by
  simp only [shiftedFamily, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [toDistr_toOrderZeroₗᵢ_symm, toDistr_besselPotentialNonposCLM hw, toDistr_toOrderZeroₗᵢ,
    besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow,
    besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow]
  congr 3
  push_cast
  ring

/-- The norm of `J^{-b} J^w J^a` grows at most polynomially in `w`, `re w ≤ 0`. -/
private theorem exists_norm_shiftedFamily_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) : ∃ C : ℝ≥0, ∀ (a b : ℝ) (w : ℂ), w.re ≤ 0 →
      ‖(shiftedFamily hq hq_top a b w : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F))‖ ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1) := by
  obtain ⟨C, hC⟩ := exists_norm_besselPotentialNonposCLM_le (E := E) (F := F) hq hq_top
  refine ⟨C, fun a b w hw ↦ ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_⟩
  simp only [shiftedFamily, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
  exact ((besselPotentialNonposCLM hq hq_top w).le_opNorm _).trans
    (by rw [LinearIsometryEquiv.norm_map]; gcongr; exact hC w hw)

private theorem continuousOn_shiftedFamily_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) (a b : ℝ) (u : H^{a, q}(E, F)) :
    ContinuousOn (fun w ↦ shiftedFamily hq hq_top a b w u) {w | w.re ≤ 0} :=
  ((toOrderZeroₗᵢ E F b q).symm.continuous.comp_continuousOn
    (continuousOn_besselPotentialNonposCLM_apply _))

private theorem differentiableOn_shiftedFamily_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) (a b : ℝ) (u : H^{a, q}(E, F)) :
    DifferentiableOn ℂ (fun w ↦ shiftedFamily hq hq_top a b w u) {w | w.re < 0} :=
  ((toOrderZeroₗᵢ E F b q).symm.toContinuousLinearEquiv : H^{0, q}(E, F) →L[ℂ] H^{b, q}(E, F)
    ).differentiable.comp_differentiableOn (differentiableOn_besselPotentialNonposCLM_apply _)

/-- On the closed unit strip, `‖exp ((z - θ)²)‖ ≤ e exp (-(im z)²)` for `0 ≤ θ ≤ 1`. -/
private theorem norm_stripGaussian_one_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖stripGaussian 1 θ z‖ ≤ Real.exp 1 * Real.exp (-z.im ^ 2) := by
  rw [norm_stripGaussian, ← Real.exp_add, Real.exp_le_exp]
  have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
  nlinarith [hz'.1, hz'.2, hθ.1, hθ.2]

end Preliminaries

/-! ### Stein interpolation of the Bessel potentials -/

section Stein

/-- The strip functions `z ↦ exp ((z - θ)²) exp (δ z² + ω z) ι (J^{-b} J^{(z - c) κ} J^a u)` are
bounded on the closed unit strip when `(re z - c) κ ≤ 0` there: the Gaussian factor beats the
polynomial growth of the family. -/
private theorem isBounded_aux {W₀ : Type*} [NormedAddCommGroup W₀] [NormedSpace ℂ W₀]
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) {a b : ℝ}
    (ι : H^{b, q}(E, F) →L[ℂ] W₀) {c κ : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hcl : ∀ x ∈ Icc (0 : ℝ) 1, (x - c) * κ ≤ 0) (u : H^{a, q}(E, F)) {δ : ℝ} (hδ : 0 < δ)
    (ω : ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    Bornology.IsBounded ((fun z ↦ stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
      ι (shiftedFamily hq hq_top a b ((z - c) * κ) u)) '' verticalClosedStrip 0 1) := by
  set ν : ℂ → ℂ := fun z ↦ (z - c) * κ
  have hre (z : ℂ) : (ν z).re = (z.re - c) * κ := by simp [ν]
  set f : ℂ → W₀ := fun z ↦ ι (shiftedFamily hq hq_top a b (ν z) u)
  -- The Gaussian factor beats the polynomial growth of the family on the strip.
  obtain ⟨C, hC⟩ := exists_norm_shiftedFamily_le (E := E) (F := F) hq hq_top
  set N := finrank ℝ E / 2 + 1
  refine isBounded_iff_forall_norm_le.2 ⟨Real.exp 1 * Real.exp (δ + |ω|) * (‖ι‖ * (C *
    ((1 + |κ|) ^ N * (N.factorial / (1 / 2 : ℝ) ^ N * Real.exp 1)) * ‖u‖)), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
  have hνz : ‖ν z‖ ≤ (1 + |z.im|) * |κ| := by
    have h1 : |z.re - c| ≤ 1 := abs_le.2 ⟨by linarith [hz'.1, hc.2], by linarith [hz'.2, hc.1]⟩
    have h2 := Complex.norm_le_abs_re_add_abs_im (z - c)
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at h2
    simp only [ν, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    linarith
  have hf : ‖f z‖ ≤ ‖ι‖ * (C * ((1 + |κ|) ^ N * (1 + |z.im|) ^ N) * ‖u‖) := by
    refine (ι.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine ((shiftedFamily hq hq_top a b (ν z)).le_opNorm u).trans ?_
    gcongr
    refine (hC a b (ν z) ((hre z).trans_le (hcl _ hz))).trans ?_
    rw [← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) C.coe_nonneg
    nlinarith [abs_nonneg κ, abs_nonneg z.im]
  rw [norm_smul, norm_smul]
  have hg := one_add_pow_mul_exp_neg_mul_sq_le one_pos N (r := |z.im|)
  rw [sq_abs, neg_one_mul] at hg
  calc ‖stripGaussian 1 θ z‖ * (‖cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z)‖ * ‖f z‖)
      ≤ Real.exp 1 * Real.exp (-z.im ^ 2) * (Real.exp (δ + |ω|) *
          (‖ι‖ * (C * ((1 + |κ|) ^ N * (1 + |z.im|) ^ N) * ‖u‖))) := by
        gcongr
        · exact norm_stripGaussian_one_le hθ hz
        · exact norm_exp_ofReal_mul_sq_add_ofReal_mul_le hδ.le ω hz
    _ = Real.exp 1 * Real.exp (δ + |ω|) * (‖ι‖ * (C * ((1 + |κ|) ^ N * ((1 + |z.im|) ^ N *
          Real.exp (-z.im ^ 2))) * ‖u‖)) := by ring
    _ ≤ _ := by gcongr

/-- The strip functions `z ↦ exp ((z - θ)²) exp (δ z² + ω z) ι (J^{-b} J^{(z - c) κ} J^a u)` are
holomorphic inside the unit strip, continuous up to its boundary and bounded, as long as
`(re z - c) κ ≤ 0` on the strip. -/
private theorem diffContOnCl_and_isBounded_aux {W₀ : Type*} [NormedAddCommGroup W₀]
    [NormedSpace ℂ W₀] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) {a b : ℝ}
    (ι : H^{b, q}(E, F) →L[ℂ] W₀) {c κ : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hcl : ∀ x ∈ Icc (0 : ℝ) 1, (x - c) * κ ≤ 0)
    (hop : κ = 0 ∨ ∀ x ∈ Ioo (0 : ℝ) 1, (x - c) * κ < 0) (u : H^{a, q}(E, F)) {δ : ℝ}
    (hδ : 0 < δ) (ω : ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    DiffContOnCl ℂ (fun z ↦ stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
        ι (shiftedFamily hq hq_top a b ((z - c) * κ) u)) (verticalStrip 0 1) ∧
      Bornology.IsBounded ((fun z ↦ stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
        ι (shiftedFamily hq hq_top a b ((z - c) * κ) u)) '' verticalClosedStrip 0 1) := by
  set ν : ℂ → ℂ := fun z ↦ (z - c) * κ
  have hν : Differentiable ℂ ν := (differentiable_id.sub_const _).mul_const _
  have hre (z : ℂ) : (ν z).re = (z.re - c) * κ := by simp [ν]
  set f : ℂ → W₀ := fun z ↦ ι (shiftedFamily hq hq_top a b (ν z) u)
  have hfc : ContinuousOn f (verticalClosedStrip 0 1) :=
    ι.continuous.comp_continuousOn ((continuousOn_shiftedFamily_apply hq hq_top a b u).comp
      hν.continuous.continuousOn fun z hz ↦ (hre z).trans_le (hcl _ hz))
  have hfd : DifferentiableOn ℂ f (verticalStrip 0 1) := by
    rcases hop with hκ | hop
    · have : f = fun _ ↦ ι (shiftedFamily hq hq_top a b 0 u) := by
        funext z; simp [f, ν, hκ]
      rw [this]
      exact differentiableOn_const _
    · exact ι.differentiable.comp_differentiableOn
        ((differentiableOn_shiftedFamily_apply hq hq_top a b u).comp hν.differentiableOn
          fun z hz ↦ (hre z).trans_lt (hop _ hz))
  have hdc : DiffContOnCl ℂ f (verticalStrip 0 1) :=
    ⟨hfd, by rwa [TauCeti.Complex.HadamardThreeLines.closure_verticalStrip zero_lt_one]⟩
  have he₂ : Differentiable ℂ fun z : ℂ ↦ cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) := by fun_prop
  exact ⟨(differentiable_stripGaussian 1 θ).diffContOnCl.smul (he₂.diffContOnCl.smul hdc),
    isBounded_aux hq hq_top ι hc hcl u hδ ω hθ⟩

/-- `‖T t‖ ≤ K` for the boundary operators `T t = exp ((x + i t - θ)²) J^{-b} J^{i t κ} J^a`. -/
private theorem norm_exp_smul_shiftedFamily_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) {C : ℝ≥0} (hC : ∀ (a b : ℝ) (w : ℂ), w.re ≤ 0 →
      ‖(shiftedFamily hq hq_top a b w : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F))‖ ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1)) {θ x : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b κ t : ℝ) :
    ‖stripGaussian 1 θ (x + (t : ℂ) * I) • (shiftedFamily hq hq_top a b ((t : ℂ) * I * κ) :
      H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F))‖ ≤ Real.exp 1 * (C * ((1 + |κ|) ^ (finrank ℝ E / 2 + 1) *
        ((finrank ℝ E / 2 + 1).factorial / (1 / 2 : ℝ) ^ (finrank ℝ E / 2 + 1) * Real.exp 1))) := by
  set N := finrank ℝ E / 2 + 1
  have hz : (x + (t : ℂ) * I) ∈ verticalClosedStrip 0 1 := by
    simpa [verticalClosedStrip] using hx
  have hn : ‖(t : ℂ) * I * κ‖ = |κ| * |t| := by
    simp [Complex.norm_real, mul_comm]
  rw [norm_smul]
  have h1 := norm_stripGaussian_one_le hθ hz
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h1
  have h2 := hC a b ((t : ℂ) * I * κ) (by simp)
  rw [hn] at h2
  have h3 := one_add_pow_mul_exp_neg_mul_sq_le one_pos N (r := |t|)
  rw [sq_abs, neg_one_mul] at h3
  have h4 : (1 + |κ| * |t|) ^ N ≤ (1 + |κ|) ^ N * (1 + |t|) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg κ, abs_nonneg t]) N
  calc ‖stripGaussian 1 θ (x + (t : ℂ) * I)‖ * ‖shiftedFamily hq hq_top a b ((t : ℂ) * I * κ)‖
      ≤ Real.exp 1 * Real.exp (-t ^ 2) * (C * ((1 + |κ|) ^ N * (1 + |t|) ^ N)) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = Real.exp 1 * (C * ((1 + |κ|) ^ N * ((1 + |t|) ^ N * Real.exp (-t ^ 2)))) := by ring
    _ ≤ _ := by gcongr

/-- The boundary operator `exp ((x + i t - θ)²) J^{-b} J^{i t κ} J^a : H^{a,q} → H^{b,q}`. -/
private def boundaryOp {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞)
    (a b κ x θ t : ℝ) : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F) :=
  stripGaussian 1 θ ((x : ℝ) + (t : ℂ) * I) • shiftedFamily hq hq_top a b ((t : ℂ) * I * κ)

/-- The boundary operators are strongly continuous in `t`. -/
private theorem continuous_boundaryOp_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) (a b κ x θ : ℝ) (v : H^{a, q}(E, F)) :
    Continuous fun t ↦ boundaryOp hq hq_top a b κ x θ t v := by
  simp only [boundaryOp, smul_apply]
  exact ((differentiable_stripGaussian 1 θ).continuous.comp
    (by fun_prop : Continuous fun t : ℝ ↦ (x : ℂ) + (t : ℂ) * I)).smul
    ((continuousOn_shiftedFamily_apply hq hq_top a b v).comp_continuous
      (by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ) * I * κ) fun t ↦ by simp)

/-- The base case of `exists_besselPotentialSpace_complexMethod_map_aux`: the strip function
`Ψ` of an elementary admissible function `exp (δ z² + ω z) x` is a bounded-boundary strip function
whose traces `g` are the boundary operators applied to those of `exp (δ z² + ω z) x`. -/
private theorem exists_isBoundedStripFunction_expGaussianTrace {p₀ p₁ : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁)
    (hp₁_top : p₁ ≠ ∞) {a₀ a₁ b₀ b₁ : ℝ} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) {δ : ℝ} (hδ : 0 < δ) (ω : ℝ)
    {Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace}
    (hdc : DiffContOnCl ℂ Ψ (verticalStrip 0 1))
    (hbd : Bornology.IsBounded (Ψ '' verticalClosedStrip 0 1))
    (hΨ : ∀ z ∈ verticalClosedStrip 0 1,
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ z) =
      stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
        fourierMultiplierCLM F (japaneseBracketCpow (a₀ + z * ((a₁ - b₁) - (a₀ - b₀) : ℝ) - b₀))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr)
    (g : (ℝ →ᵇ H^{b₀, p₀}(E, F)) × (ℝ →ᵇ H^{b₁, p₁}(E, F)))
    (hg₀ : ∀ t, g.1 t = boundaryOp hp₀ hp₀_top a₀ b₀ ((a₁ - b₁) - (a₀ - b₀)) 0 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t))
    (hg₁ : ∀ t, g.2 t = boundaryOp hp₁ hp₁_top a₁ b₁ ((a₁ - b₁) - (a₀ - b₀)) 1 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t)) :
    (besselPotentialSpace E F b₀ p₀ b₁ p₁).IsBoundedStripFunction Ψ g ∧
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ θ) =
        besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).sumSpaceEmbed
            ((besselPotentialSpace E F a₀ p₀ a₁ p₁).stripEval θ
              ((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x))) := by
  -- The goal depends on `x`, so `set` alone would add a new `x` of the abbreviated type and
  -- shadow the one the goal mentions; reverting `x` and the hypotheses about it first lets `set`
  -- abstract the couples in the goal as well.
  revert x hΨ hg₀ hg₁
  set X := besselPotentialSpace E F a₀ p₀ a₁ p₁
  set Y := besselPotentialSpace E F b₀ p₀ b₁ p₁
  intro x hΨ hg₀ hg₁
  set κ : ℝ := (a₁ - b₁) - (a₀ - b₀) with hκ_def
  set x₀ := X.interFst x
  have hx : (X.interSnd x).toDistr = x₀.toDistr := by
    simpa [X, x₀] using (X.embed₀_interFst x).symm
  refine ⟨⟨hdc, hbd, fun t ↦ ?_, fun t ↦ ?_⟩, ?_⟩
  · -- On `re z = 0` both sides are `exp ((i t - θ)²) exp (δ (i t)² + ω i t) J^{λ₀ + i t κ} x`.
    refine Y.sumSpace_ext ?_
    rw [hΨ _ (by simp [verticalClosedStrip]), sumSpaceEmbed_fstToSum, hg₀]
    simp only [Y, besselPotentialSpace_embed₀_apply, expGaussianTrace_apply_fst, boundaryOp,
      map_smul, smul_apply, Complex.ofReal_zero, zero_add,
      toDistr_shiftedFamily (le_of_eq (by simp : ((t : ℂ) * I * κ).re = 0))]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  · -- On `re z = 1` both sides are `J^{λ₁ + i t κ} x` with the corresponding factors.
    refine Y.sumSpace_ext ?_
    rw [hΨ _ (by simp [verticalClosedStrip]), sumSpaceEmbed_sndToSum, hg₁]
    simp only [Y, besselPotentialSpace_embed₁_apply, expGaussianTrace_apply_snd, boundaryOp,
      map_smul, smul_apply, Complex.ofReal_one,
      toDistr_shiftedFamily (le_of_eq (by simp : ((t : ℂ) * I * κ).re = 0))]
    rw [hx, smul_smul, smul_smul]
    congr 1
    · ring
    · congr 3
      rw [hκ_def]
      push_cast
      ring
  · -- At `θ` the strip function is `exp (δ θ² + ω θ) J^{λ_θ} x`.
    rw [hΨ _ (by simpa [verticalClosedStrip] using hθ), X.stripEval_expGaussianTrace hδ ω x
      (by simpa [verticalClosedStrip] using hθ), map_smul, map_smul, sumSpaceEmbed_fstToSum]
    simp only [X, besselPotentialSpace_embed₀_apply,
      besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow, stripGaussian_self, one_smul]
    congr 3
    rw [hκ_def]
    push_cast
    ring_nf

/-- Every elementary admissible function `G` of `(H^{a₀,p₀}, H^{a₁,p₁})` is matched by a
bounded-boundary strip function whose traces are the boundary operators applied to those of `G`
and whose value at `θ` is `J^{λ_θ} (G θ)`, given such strip functions for the generators
`exp (δ z² + ω z) x` and operators `B₀`, `B₁` applying the boundary operators pointwise. -/
private theorem exists_isBoundedStripFunction_of_mem_elementaryStripTraces {p₀ p₁ : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁)
    (hp₁_top : p₁ ≠ ∞) {a₀ a₁ b₀ b₁ : ℝ} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) {δ : ℝ} (_ : 0 < δ) (ω : ℝ),
      ∃ Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace,
        DiffContOnCl ℂ Ψ (verticalStrip 0 1) ∧ Bornology.IsBounded (Ψ '' verticalClosedStrip 0 1) ∧
        ∀ z ∈ verticalClosedStrip 0 1, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ z) =
          stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
            fourierMultiplierCLM F (japaneseBracketCpow (a₀ + z * ((a₁ - b₁) - (a₀ - b₀) : ℝ) - b₀))
              ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr)
    (B₀ : C₀(ℝ, H^{a₀, p₀}(E, F)) →L[ℂ] C₀(ℝ, H^{b₀, p₀}(E, F)))
    (B₁ : C₀(ℝ, H^{a₁, p₁}(E, F)) →L[ℂ] C₀(ℝ, H^{b₁, p₁}(E, F)))
    (hB₀ : ∀ f t, B₀ f t = boundaryOp hp₀ hp₀_top a₀ b₀ ((a₁ - b₁) - (a₀ - b₀)) 0 θ t (f t))
    (hB₁ : ∀ f t, B₁ f t = boundaryOp hp₁ hp₁_top a₁ b₁ ((a₁ - b₁) - (a₀ - b₀)) 1 θ t (f t))
    {G : (besselPotentialSpace E F a₀ p₀ a₁ p₁).stripTraces}
    (hG : G ∈ (besselPotentialSpace E F a₀ p₀ a₁ p₁).elementaryStripTraces) :
    ∃ (Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace)
      (g : (ℝ →ᵇ H^{b₀, p₀}(E, F)) × (ℝ →ᵇ H^{b₁, p₁}(E, F))),
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).IsBoundedStripFunction Ψ g ∧
      g.1 = (B₀ (G : C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1).toBCF ∧
      g.2 = (B₁ (G : C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2).toBCF ∧
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ θ) =
        besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).sumSpaceEmbed
            ((besselPotentialSpace E F a₀ p₀ a₁ p₁).stripEval θ G)) := by
  induction hG using elementaryStripTraces_induction with
  | @expGaussian δ hδ ω x =>
    obtain ⟨Ψ, hdc, hbd, hΨ⟩ := hstrip x hδ ω
    obtain ⟨hΨg, hθG⟩ := exists_isBoundedStripFunction_expGaussianTrace hp₀ hp₀_top hp₁
      hp₁_top hθ x hδ ω hdc hbd hΨ ((B₀ _).toBCF, (B₁ _).toBCF) (hB₀ _) (hB₁ _)
    exact ⟨Ψ, _, hΨg, rfl, rfl, hθG⟩
  | zero => exact ⟨0, 0, .zero, by ext; simp, by ext; simp, by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨Ψ, g, hΨ, hg₀, hg₁, hθG⟩ := hG
    obtain ⟨Φ, h, hΦ, hh₀, hh₁, hθH⟩ := hH
    exact ⟨Ψ + Φ, g + h, hΨ.add hΦ, by ext; simp [hg₀, hh₀], by ext; simp [hg₁, hh₁],
      by simp [hθG, hθH]⟩
  | smul c G _ hG =>
    obtain ⟨Ψ, g, hΨ, hg₀, hg₁, hθG⟩ := hG
    exact ⟨c • Ψ, c • g, hΨ.const_smul c, by ext; simp [hg₀], by ext; simp [hg₁],
      by simp [hθG]⟩

/-- Stein interpolation of the Bessel potentials `J^{λ(z)}`, `λ(z) = (1 - z) λ₀ + z λ₁` with
`λⱼ = aⱼ - bⱼ`, given the strip functions `z ↦ exp ((z - θ)²) exp (δ z² + ω z) J^{λ(z)} x` for
`x ∈ H^{a₀,p₀} ∩ H^{a₁,p₁}`. On the boundary lines they are `exp ((j + i t - θ)²) J^{λⱼ + i t κ}`,
`κ = λ₁ - λ₀`, applied to the traces of `exp (δ z² + ω z) x`. -/
private theorem exists_besselPotentialSpace_complexMethod_map_aux {p₀ p₁ : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁)
    (hp₁_top : p₁ ≠ ∞) {a₀ a₁ b₀ b₁ : ℝ} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) {δ : ℝ} (_ : 0 < δ) (ω : ℝ),
      ∃ Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace,
        DiffContOnCl ℂ Ψ (verticalStrip 0 1) ∧ Bornology.IsBounded (Ψ '' verticalClosedStrip 0 1) ∧
        ∀ z ∈ verticalClosedStrip 0 1, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ z) =
          stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
            fourierMultiplierCLM F (japaneseBracketCpow (a₀ + z * ((a₁ - b₁) - (a₀ - b₀) : ℝ) - b₀))
              ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr) :
    ∃ T : (besselPotentialSpace E F a₀ p₀ a₁ p₁).ComplexMethodSpace θ →L[ℂ]
        (besselPotentialSpace E F b₀ p₀ b₁ p₁).ComplexMethodSpace θ,
      ∀ u, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum (T u)) =
        besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u)) := by
  set X := besselPotentialSpace E F a₀ p₀ a₁ p₁
  set Y := besselPotentialSpace E F b₀ p₀ b₁ p₁
  set κ : ℝ := (a₁ - b₁) - (a₀ - b₀)
  obtain ⟨C₀, hC₀⟩ := exists_norm_shiftedFamily_le (E := E) (F := F) hp₀ hp₀_top
  obtain ⟨C₁, hC₁⟩ := exists_norm_shiftedFamily_le (E := E) (F := F) hp₁ hp₁_top
  set N := finrank ℝ E / 2 + 1
  set K : ℝ := Real.exp 1 * ((C₀ + C₁) * ((1 + |κ|) ^ N *
    (N.factorial / (1 / 2 : ℝ) ^ N * Real.exp 1)))
  have hK : 0 ≤ K := by positivity
  -- The boundary operators `T₀ t : H^{a₀,p₀} → H^{b₀,p₀}` and `T₁ t : H^{a₁,p₁} → H^{b₁,p₁}`.
  set T₀ := boundaryOp (E := E) (F := F) hp₀ hp₀_top a₀ b₀ κ 0 θ
  set T₁ := boundaryOp (E := E) (F := F) hp₁ hp₁_top a₁ b₁ κ 1 θ
  have hT₀ (t : ℝ) : ‖T₀ t‖ ≤ K :=
    (norm_exp_smul_shiftedFamily_le hp₀ hp₀_top hC₀ hθ ⟨le_rfl, zero_le_one⟩ a₀ b₀ κ t).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right C₁.coe_nonneg) (by positivity)) (by positivity))
  have hT₁ (t : ℝ) : ‖T₁ t‖ ≤ K :=
    (norm_exp_smul_shiftedFamily_le hp₁ hp₁_top hC₁ hθ ⟨zero_le_one, le_rfl⟩ a₁ b₁ κ t).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left C₀.coe_nonneg) (by positivity)) (by positivity))
  have hK₀ (t : ℝ) (v : H^{a₀, p₀}(E, F)) : ‖T₀ t v‖ ≤ K * ‖v‖ := (T₀ t).le_of_opNorm_le (hT₀ t) v
  have hK₁ (t : ℝ) (v : H^{a₁, p₁}(E, F)) : ‖T₁ t v‖ ≤ K * ‖v‖ := (T₁ t).le_of_opNorm_le (hT₁ t) v
  -- Their pointwise action on boundary traces.
  set B₀ := ZeroAtInftyContinuousMap.compLeftFamily T₀
    (continuous_boundaryOp_apply hp₀ hp₀_top a₀ b₀ κ 0 θ) ⟨K, hK₀⟩
  set B₁ := ZeroAtInftyContinuousMap.compLeftFamily T₁
    (continuous_boundaryOp_apply hp₁ hp₁_top a₁ b₁ κ 1 θ) ⟨K, hK₁⟩
  obtain ⟨T, -, hT⟩ := ComplexMethodSpace.exists_map_of_forall_elementaryStripTraces hθ
    (besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))) hK fun G hG ↦ by
      obtain ⟨Ψ, g, hΨ, h₀, h₁, hθG⟩ :=
        exists_isBoundedStripFunction_of_mem_elementaryStripTraces hp₀ hp₀_top hp₁ hp₁_top hθ
          hstrip B₀ B₁ (ZeroAtInftyContinuousMap.compLeftFamily_apply _ _ _)
          (ZeroAtInftyContinuousMap.compLeftFamily_apply _ _ _) hG
      refine ⟨Ψ, g, hΨ, hθG, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
      · rw [h₀, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact (ZeroAtInftyContinuousMap.norm_compLeftFamily_apply_le _ _ _ hK₀ _).trans
          (mul_le_mul_of_nonneg_left (norm_fst_le _) hK)
      · rw [h₁, ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
        exact (ZeroAtInftyContinuousMap.norm_compLeftFamily_apply_le _ _ _ hK₁ _).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le _) hK)
  exact ⟨T, hT⟩

/-- The strip function of `exists_besselPotentialSpace_complexMethod_map`, computed from the
component `u ∈ H^{a,q}` of `x ∈ H^{a₀,p₀} ∩ H^{a₁,p₁}` on the boundary line `re z = c`, when
`(re z - c) κ ≤ 0` on the strip. It is
`z ↦ exp ((z - θ)²) exp (δ z² + ω z) ι (J^{-b} J^{(z - c) κ} J^a u)`, where
`ι : H^{b,q} → H^{b₀,p₀} + H^{b₁,p₁}` is the inclusion of the matching component. -/
private theorem exists_strip_of_component {p₀ p₁ q : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
    [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) {a₀ a₁ b₀ b₁ a b c κ θ : ℝ}
    (hθ : θ ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) (hcl : ∀ y ∈ Icc (0 : ℝ) 1, (y - c) * κ ≤ 0)
    (hop : κ = 0 ∨ ∀ y ∈ Ioo (0 : ℝ) 1, (y - c) * κ < 0) (hab : a - b - c * κ = a₀ - b₀)
    (ι : H^{b, q}(E, F) →L[ℂ] (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace)
    (hι : ∀ v, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (ι v) = v.toDistr)
    (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) (u : H^{a, q}(E, F))
    (hu : u.toDistr = ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr) {δ : ℝ}
    (hδ : 0 < δ) (ω : ℝ) :
    ∃ Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace,
      DiffContOnCl ℂ Ψ (verticalStrip 0 1) ∧ Bornology.IsBounded (Ψ '' verticalClosedStrip 0 1) ∧
      ∀ z ∈ verticalClosedStrip 0 1, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ z) =
        stripGaussian 1 θ z • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
          fourierMultiplierCLM F (japaneseBracketCpow (a₀ + z * κ - b₀))
            ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr := by
  obtain ⟨hdc, hbd⟩ := diffContOnCl_and_isBounded_aux hq hq_top ι hc hcl hop u hδ ω hθ
  refine ⟨_, hdc, hbd, fun z hz ↦ ?_⟩
  have hre : ((z - c) * κ).re ≤ 0 := by simpa using hcl z.re hz
  have hab' : (a : ℂ) - b - c * κ = a₀ - b₀ := mod_cast hab
  simp only [map_smul, hι]
  rw [toDistr_shiftedFamily hre, hu,
    show (a : ℂ) + (z - c) * κ - b = a₀ + z * κ - b₀ by linear_combination hab']

/-- **Stein interpolation of the Bessel potentials between Bessel-potential couples.** Let
`1 < p₀, p₁ < ∞`, `0 ≤ θ ≤ 1` and real orders `a₀, a₁, b₀, b₁`. The Bessel potential
`J^{λ_θ}`, `λ_θ = (1 - θ) (a₀ - b₀) + θ (a₁ - b₁)`, restricts to a bounded operator
`[H^{a₀,p₀}, H^{a₁,p₁}]_θ → [H^{b₀,p₀}, H^{b₁,p₁}]_θ`. This interpolates the analytic family
`J^{λ(z)}`, `λ(z) = (1 - z) (a₀ - b₀) + z (a₁ - b₁)`, which maps `H^{aⱼ,pⱼ}` to `H^{bⱼ,pⱼ}` on
the boundary lines `re z = j` with norm growing polynomially in `im z`. -/
theorem exists_besselPotentialSpace_complexMethod_map {p₀ p₁ : ℝ≥0∞} [Fact (1 ≤ p₀)]
    [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞)
    (a₀ a₁ b₀ b₁ : ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ∃ T : (besselPotentialSpace E F a₀ p₀ a₁ p₁).ComplexMethodSpace θ →L[ℂ]
        (besselPotentialSpace E F b₀ p₀ b₁ p₁).ComplexMethodSpace θ,
      ∀ u, (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum (T u)) =
        besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u)) := by
  set κ : ℝ := (a₁ - b₁) - (a₀ - b₀) with hκ_def
  set X := besselPotentialSpace E F a₀ p₀ a₁ p₁
  set Y := besselPotentialSpace E F b₀ p₀ b₁ p₁
  refine exists_besselPotentialSpace_complexMethod_map_aux hp₀ hp₀_top hp₁ hp₁_top hθ ?_
  intro x δ hδ ω
  rcases le_total 0 κ with hκ | hκ
  · -- `λ₀ ≤ λ₁`: compute `J^{λ(z)} x` from the component of `x` in `H^{a₁,p₁}`.
    exact exists_strip_of_component hp₁ hp₁_top hθ ⟨zero_le_one, le_rfl⟩
      (fun y hy ↦ mul_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) hκ)
      (hκ.eq_or_lt.imp Eq.symm fun h y hy ↦ mul_neg_of_neg_of_pos (by linarith [hy.2]) h)
      (by rw [hκ_def]; ring) Y.sndToSum (fun v ↦ by simp [Y]) x (X.interSnd x)
      (by simpa [X] using (X.embed₀_interFst x).symm) hδ ω
  · -- `λ₀ ≥ λ₁`: compute `J^{λ(z)} x` from the component of `x` in `H^{a₀,p₀}`.
    exact exists_strip_of_component hp₀ hp₀_top hθ ⟨le_rfl, zero_le_one⟩
      (fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos (by linarith [hy.1]) hκ)
      (hκ.eq_or_lt.imp id fun h y hy ↦ mul_neg_of_pos_of_neg (by linarith [hy.1]) h)
      (by ring) Y.fstToSum (fun v ↦ by simp [Y]) x (X.interFst x) rfl hδ ω

end Stein

/-! ### The identification `[H^{s₀,p₀}, H^{s₁,p₁}]_θ = H^{s_θ,p_θ}` -/

section Identification

variable {s₀ s₁ : ℝ} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] {θ : ℝ}

variable (E F s₀ s₁ p₀ p₁) in
/-- **Complex interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorem 6.4.5 (7)). For
`1 < p₀, p₁ < ∞`, `0 < θ < 1`, real orders `s₀, s₁` and the interpolated parameters
`s_θ = (1 - θ) s₀ + θ s₁` and `1 / p = (1 - θ) / p₀ + θ / p₁`, Calderón's complex interpolation
space `[H^{s₀,p₀}, H^{s₁,p₁}]_θ` is isomorphic to `H^{s_θ,p}`, by an isomorphism that keeps the
underlying tempered distribution. -/
private theorem exists_besselPotentialSpace_complexMethod_continuousLinearEquiv (hp₀ : 1 < p₀)
    (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    ∃ e : (besselPotentialSpace E F s₀ p₀ s₁ p₁).ComplexMethodSpace θ ≃L[ℂ]
        H^{(1 - θ) * s₀ + θ * s₁, p}(E, F),
      ∀ u, (e u).toDistr =
        (besselPotentialSpace E F s₀ p₀ s₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
  set C := besselPotentialSpace E F s₀ p₀ s₁ p₁
  set D := besselPotentialSpace E F 0 p₀ 0 p₁
  set sθ := (1 - θ) * s₀ + θ * s₁
  have hp_top : p ≠ ∞ := fun h ↦ hp₀_top ((eq_top_iff_of_inv_eq hθ hp).1 h).1
  set eD := besselPotentialSpaceOfOrderComplexMethodEquiv E F 0 p₀ p₁ hθ hp hp_top
  -- `J^{s_θ}` maps `[H^{s₀,p₀}, H^{s₁,p₁}]_θ` to `[L^{p₀}, L^{p₁}]_θ`, and `J^{-s_θ}` back.
  obtain ⟨TB, hTB⟩ := exists_besselPotentialSpace_complexMethod_map (E := E) (F := F) hp₀
    hp₀_top hp₁ hp₁_top s₀ s₁ 0 0 (Ioo_subset_Icc_self hθ)
  obtain ⟨TA, hTA⟩ := exists_besselPotentialSpace_complexMethod_map (E := E) (F := F) hp₀
    hp₀_top hp₁ hp₁_top 0 0 s₀ s₁ (Ioo_subset_Icc_self hθ)
  have hB : (1 - θ) * (s₀ - 0) + θ * (s₁ - 0) = sθ := by ring
  have hA : (1 - θ) * (0 - s₀) + θ * (0 - s₁) = -sθ := by ring
  rw [hB] at hTB
  rw [hA] at hTA
  set f : C.ComplexMethodSpace θ →L[ℂ] H^{sθ, p}(E, F) :=
    ((toOrderZeroₗᵢ E F sθ p).symm.toContinuousLinearEquiv : H^{0, p}(E, F) →L[ℂ] _) ∘L
      (eD.toContinuousLinearEquiv : D.ComplexMethodSpace θ →L[ℂ] _) ∘L TB
  set g : H^{sθ, p}(E, F) →L[ℂ] C.ComplexMethodSpace θ :=
    TA ∘L (eD.symm.toContinuousLinearEquiv : H^{0, p}(E, F) →L[ℂ] _) ∘L
      ((toOrderZeroₗᵢ E F sθ p).toContinuousLinearEquiv : H^{sθ, p}(E, F) →L[ℂ] _)
  have hf (u : C.ComplexMethodSpace θ) :
      (f u).toDistr = C.sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
    simp only [f, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [toDistr_toOrderZeroₗᵢ_symm, toDistr_besselPotentialSpaceOfOrderComplexMethodEquiv_apply,
      hTB, besselPotential_besselPotential_apply, add_neg_cancel, besselPotential_zero,
      ContinuousLinearMap.id_apply]
  have hg (v : H^{sθ, p}(E, F)) :
      C.sumSpaceEmbed (ComplexMethodSpace.toSum (g v)) = v.toDistr := by
    simp only [g, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [hTA, sumSpaceEmbed_toSum_besselPotentialSpaceOfOrderComplexMethodEquiv_symm_apply,
      toDistr_toOrderZeroₗᵢ, besselPotential_besselPotential_apply, add_neg_cancel,
      besselPotential_zero, ContinuousLinearMap.id_apply]
  refine ⟨ContinuousLinearEquiv.ofContinuousLinearMap f g (ContinuousLinearMap.ext fun v ↦ ?_)
    (ContinuousLinearMap.ext fun u ↦ ?_), hf⟩
  · exact BesselPotentialSpace.ext (by simp [hf, hg])
  · exact ComplexMethodSpace.toSum_injective (C.sumSpaceEmbed_injective (by simp [hg, hf]))

variable (E F s₀ s₁ p₀ p₁) in
/-- **Complex interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorem 6.4.5 (7)): the
isomorphism `[H^{s₀,p₀}, H^{s₁,p₁}]_θ ≃L[ℂ] H^{s_θ,p}` for `1 < p₀, p₁ < ∞`, `0 < θ < 1`,
`s_θ = (1 - θ) s₀ + θ s₁` and `1 / p = (1 - θ) / p₀ + θ / p₁`. It keeps the underlying
tempered distribution
(`TauCeti.CompatibleCouple.toDistr_besselPotentialSpaceComplexMethodContinuousLinearEquiv_apply`),
which determines it. -/
def besselPotentialSpaceComplexMethodContinuousLinearEquiv (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞)
    (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    (besselPotentialSpace E F s₀ p₀ s₁ p₁).ComplexMethodSpace θ ≃L[ℂ]
      H^{(1 - θ) * s₀ + θ * s₁, p}(E, F) :=
  (exists_besselPotentialSpace_complexMethod_continuousLinearEquiv E F s₀ s₁ p₀ p₁ hp₀ hp₀_top
    hp₁ hp₁_top hθ hp).choose

/-- `besselPotentialSpaceComplexMethodContinuousLinearEquiv` keeps the underlying tempered
distribution: an element of `[H^{s₀,p₀}, H^{s₁,p₁}]_θ` is sent to the element of `H^{s_θ,p}` with
the same distribution. -/
@[simp]
theorem toDistr_besselPotentialSpaceComplexMethodContinuousLinearEquiv_apply (hp₀ : 1 < p₀)
    (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (u : (besselPotentialSpace E F s₀ p₀ s₁ p₁).ComplexMethodSpace θ) :
    (besselPotentialSpaceComplexMethodContinuousLinearEquiv E F s₀ s₁ p₀ p₁ hp₀ hp₀_top hp₁
      hp₁_top hθ hp u).toDistr =
        (besselPotentialSpace E F s₀ p₀ s₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) :=
  (exists_besselPotentialSpace_complexMethod_continuousLinearEquiv E F s₀ s₁ p₀ p₁ hp₀ hp₀_top
    hp₁ hp₁_top hθ hp).choose_spec u

/-- The inverse of `besselPotentialSpaceComplexMethodContinuousLinearEquiv` sends `v ∈ H^{s_θ,p}`
to the element of `[H^{s₀,p₀}, H^{s₁,p₁}]_θ` with the same tempered distribution. -/
@[simp]
theorem sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodContinuousLinearEquiv_symm_apply
    (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (v : H^{(1 - θ) * s₀ + θ * s₁, p}(E, F)) :
    (besselPotentialSpace E F s₀ p₀ s₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum
      ((besselPotentialSpaceComplexMethodContinuousLinearEquiv E F s₀ s₁ p₀ p₁ hp₀ hp₀_top hp₁
        hp₁_top hθ hp).symm v)) = v.toDistr := by
  rw [← toDistr_besselPotentialSpaceComplexMethodContinuousLinearEquiv_apply hp₀ hp₀_top hp₁
    hp₁_top hθ hp, ContinuousLinearEquiv.apply_symm_apply]

end Identification

end CompatibleCouple

end TauCeti

namespace TemperedDistribution

open TauCeti TauCeti.CompatibleCouple

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  {s₀ s₁ t₀ t₁ θ : ℝ} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]

/-- **Interpolation of Bessel-potential regularity.** Let `1 < p₀, p₁ < ∞`, `0 < θ < 1`,
`s_θ = (1 - θ) s₀ + θ s₁`, `t_θ = (1 - θ) t₀ + θ t₁` and `1 / p = (1 - θ) / p₀ + θ / p₁`. A
continuous linear map `A` of tempered distributions that maps `H^{s₀,p₀}` into `H^{t₀,p₀}` and
`H^{s₁,p₁}` into `H^{t₁,p₁}` also maps `H^{s_θ,p}` into `H^{t_θ,p}`. The orders may shift, as for
a differential operator of order `m` with `tⱼ = sⱼ - m`. -/
theorem MemSobolev.map_of_memSobolev_of_memSobolev (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞)
    (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G)) (h₀ : ∀ u, MemSobolev s₀ p₀ u → MemSobolev t₀ p₀ (A u))
    (h₁ : ∀ u, MemSobolev s₁ p₁ u → MemSobolev t₁ p₁ (A u)) {u : 𝓢'(E, F)}
    (hu : MemSobolev ((1 - θ) * s₀ + θ * s₁) p u) :
    MemSobolev ((1 - θ) * t₀ + θ * t₁) p (A u) := by
  set C := besselPotentialSpace E F s₀ p₀ s₁ p₁
  set D := besselPotentialSpace E G t₀ p₀ t₁ p₁
  -- `A` restricts to the two endpoint spaces, compatibly on their intersection.
  set T₀ := BesselPotentialSpace.mapCLM A fun v : H^{s₀, p₀}(E, F) ↦ h₀ _ v.memSobolev_toDistr
  set T₁ := BesselPotentialSpace.mapCLM A fun v : H^{s₁, p₁}(E, F) ↦ h₁ _ v.memSobolev_toDistr
  have hT (x : C.inter) : D.fstToSum (T₀ (C.interFst x)) = D.sndToSum (T₁ (C.interSnd x)) :=
    D.sumSpaceEmbed_injective (by simpa [T₀, T₁, C, D] using congr_arg A (C.embed₀_interFst x))
  set eC := besselPotentialSpaceComplexMethodContinuousLinearEquiv E F s₀ s₁ p₀ p₁ hp₀ hp₀_top
    hp₁ hp₁_top hθ hp
  set eD := besselPotentialSpaceComplexMethodContinuousLinearEquiv E G t₀ t₁ p₀ p₁ hp₀ hp₀_top
    hp₁ hp₁_top hθ hp
  -- The interpolated map sends `u` to `A u`: split `u = x₀ + x₁` with `xⱼ ∈ H^{sⱼ,pⱼ}`.
  have h := (eD (ComplexMethodSpace.map θ T₀ T₁ hT (eC.symm hu.toBesselPotentialSpace)))
    |>.memSobolev_toDistr
  have hu' := sumSpaceEmbed_toSum_besselPotentialSpaceComplexMethodContinuousLinearEquiv_symm_apply
    hp₀ hp₀_top hp₁ hp₁_top hθ hp hu.toBesselPotentialSpace
  rw [toDistr_besselPotentialSpaceComplexMethodContinuousLinearEquiv_apply,
    ComplexMethodSpace.toSum_map] at h
  rw [MemSobolev.toBesselPotentialSpace_toDistr] at hu'
  obtain ⟨x₀, x₁, hx⟩ := C.exists_fstToSum_add_sndToSum_eq
    (ComplexMethodSpace.toSum (eC.symm hu.toBesselPotentialSpace))
  rw [← hx, map_add, C.sumLift_fstToSum (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) hT,
    C.sumLift_sndToSum (D.fstToSum.comp T₀) (D.sndToSum.comp T₁) hT] at h
  rw [← hx] at hu'
  simpa [← hu', T₀, T₁, C, D] using h

/-- **Real orders from integer orders.** Let `1 < p < ∞`. A continuous linear map `A` of tempered
distributions that preserves `H^{k,p}` for every integer `k` with `|k| ≤ ⌈|s|⌉` also preserves
`H^{s,p}`. For non-integer `s`, interpolate between the integer orders `⌊s⌋` and `⌊s⌋ + 1`. -/
theorem MemSobolev.map_of_forall_intCast (hp : 1 < p) (hp_top : p ≠ ∞) {s : ℝ}
    (A : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G))
    (hA : ∀ k : ℤ, k.natAbs ≤ ⌈|s|⌉₊ → ∀ u, MemSobolev k p u → MemSobolev k p (A u))
    {u : 𝓢'(E, F)} (hu : MemSobolev s p u) : MemSobolev s p (A u) := by
  have h₀ := Int.natAbs_floor_le_natCeil_abs s
  rcases eq_or_ne (Int.fract s) 0 with hs | hs
  · -- An integer order `s = ⌊s⌋`.
    have hk : (⌊s⌋ : ℝ) = s := (sub_eq_zero.1 ((Int.self_sub_floor s).trans hs)).symm
    rw [← hk] at hu ⊢
    exact hA _ h₀ _ hu
  have hθ : s = (1 - Int.fract s) * ((⌊s⌋ : ℤ) : ℝ) + Int.fract s * ((⌊s⌋ + 1 : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor]
    push_cast
    ring
  have hθ' : Int.fract s ∈ Ioo (0 : ℝ) 1 :=
    ⟨(Int.fract_nonneg s).lt_of_ne' hs, Int.fract_lt_one s⟩
  have hp' :
      p⁻¹ = ENNReal.ofReal (1 - Int.fract s) * p⁻¹ + ENNReal.ofReal (Int.fract s) * p⁻¹ := by
    rw [← add_mul, ← ENNReal.ofReal_add (by linarith [hθ'.2]) hθ'.1.le, sub_add_cancel,
      ENNReal.ofReal_one, one_mul]
  rw [hθ] at hu ⊢
  exact map_of_memSobolev_of_memSobolev hp hp_top hp hp_top hθ' hp' A (hA _ h₀)
    (hA _ (Int.natAbs_floor_add_one_le_natCeil_abs hs)) hu

end TemperedDistribution
