/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
public import TauCeti.Analysis.Sobolev.BesselPotential.AnalyticFamily
public import TauCeti.Analysis.Sobolev.BesselPotential.ExponentInterpolation
import TauCeti.Analysis.Complex.VerticalStrip.Basic

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
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace BoundedContinuousFunction ZeroAtInfty

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace TauCeti

namespace CompatibleCouple

open BesselPotentialSpace

/-! ### Preliminaries -/

section Preliminaries

omit [CompleteSpace F] in
/-- The Fourier multiplier with symbol `⟨ξ⟩ ^ 0 = 1` is the identity. -/
private theorem fourierMultiplierCLM_japaneseBracketCpow_zero (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (japaneseBracketCpow (0 : ℂ)) u = u := by
  have h1 : japaneseBracketCpow (0 : ℂ) = fun _ : E ↦ (1 : ℂ) := funext japaneseBracketCpow_zero
  rw [h1, fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]

omit [CompleteSpace F] in
/-- `J^{-s} J^s u = u`. -/
private theorem fourierMultiplierCLM_japaneseBracketCpow_neg_besselPotential (s : ℝ)
    (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (japaneseBracketCpow (-s : ℂ)) (besselPotential E F s u) = u := by
  rw [besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow,
    add_neg_cancel, fourierMultiplierCLM_japaneseBracketCpow_zero]

variable (E F) in
/-- The isometry `J^s : H^{s,p} ≃ H^{0,p}`. -/
private def toOrderZero (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : H^{s, p}(E, F) ≃ₗᵢ[ℂ] H^{0, p}(E, F) :=
  (toLpₗᵢ E F s p).trans (toLpₗᵢ E F 0 p).symm

private theorem toDistr_toOrderZero {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) :
    (toOrderZero E F s p u).toDistr = fourierMultiplierCLM F (japaneseBracketCpow (s : ℂ))
      u.toDistr := by
  have h : (toOrderZero E F s p u).toDistr = besselPotential E F (-0) u.toLp := by
    simp [toOrderZero]
  rw [h, neg_zero, besselPotential_zero, ContinuousLinearMap.id_apply,
    ← u.bessel_toDistr_eq_toLp, besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow]

private theorem toDistr_toOrderZero_symm {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{0, p}(E, F)) :
    ((toOrderZero E F s p).symm u).toDistr =
      fourierMultiplierCLM F (japaneseBracketCpow (-s : ℂ)) u.toDistr := by
  have h := toDistr_toOrderZero (s := s) ((toOrderZero E F s p).symm u)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  rw [h, fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow,
    add_neg_cancel, fourierMultiplierCLM_japaneseBracketCpow_zero]

/-- The operator `J^{-b} J^w J^a : H^{a,q} → H^{b,q}` for `re w ≤ 0`, used both on the boundary
lines and inside the strip. Its distribution is `J^{a - b + w} u`. -/
private def shiftedFamily {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞) (a b : ℝ)
    (w : ℂ) : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F) :=
  ((toOrderZero E F b q).symm.toContinuousLinearEquiv : H^{0, q}(E, F) →L[ℂ] H^{b, q}(E, F)) ∘L
    besselPotentialNonposCLM hq hq_top w ∘L
      ((toOrderZero E F a q).toContinuousLinearEquiv : H^{a, q}(E, F) →L[ℂ] H^{0, q}(E, F))

private theorem toDistr_shiftedFamily {q : ℝ≥0∞} [Fact (1 ≤ q)] {hq : 1 < q} {hq_top : q ≠ ∞}
    {a b : ℝ} {w : ℂ} (hw : w.re ≤ 0) (u : H^{a, q}(E, F)) :
    (shiftedFamily hq hq_top a b w u).toDistr =
      fourierMultiplierCLM F (japaneseBracketCpow (a + w - b)) u.toDistr := by
  simp only [shiftedFamily, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [toDistr_toOrderZero_symm, toDistr_besselPotentialNonposCLM hw, toDistr_toOrderZero,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow,
    fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow]
  congr 3
  ring

/-- `(b + a |t|) ^ N exp (-t²) ≤ (b + a) ^ N exp (N² / 4)` for `a, b ≥ 0`: the Gaussian beats
polynomial growth. -/
private theorem add_mul_abs_pow_mul_exp_neg_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (N : ℕ)
    (t : ℝ) : (b + a * |t|) ^ N * Real.exp (-t ^ 2) ≤ (b + a) ^ N * Real.exp (N ^ 2 / 4) := by
  have h1 : b + a * |t| ≤ (b + a) * Real.exp |t| := by
    have := Real.add_one_le_exp |t|
    nlinarith [abs_nonneg t]
  have h2 : (b + a * |t|) ^ N ≤ (b + a) ^ N * Real.exp (N * |t|) := by
    rw [Real.exp_natCast_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 N
  calc (b + a * |t|) ^ N * Real.exp (-t ^ 2) ≤ (b + a) ^ N * Real.exp (N * |t|) *
        Real.exp (-t ^ 2) := by gcongr
    _ = (b + a) ^ N * Real.exp (N * |t| - t ^ 2) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ (b + a) ^ N * Real.exp (N ^ 2 / 4) := by
        gcongr
        nlinarith [sq_nonneg (|t| - N / 2), sq_abs t]


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
  ((toOrderZero E F b q).symm.continuous.comp_continuousOn
    (continuousOn_besselPotentialNonposCLM_apply _))

private theorem differentiableOn_shiftedFamily_apply {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) (a b : ℝ) (u : H^{a, q}(E, F)) :
    DifferentiableOn ℂ (fun w ↦ shiftedFamily hq hq_top a b w u) {w | w.re < 0} :=
  ((toOrderZero E F b q).symm.toContinuousLinearEquiv : H^{0, q}(E, F) →L[ℂ] H^{b, q}(E, F)
    ).differentiable.comp_differentiableOn (differentiableOn_besselPotentialNonposCLM_apply _)

/-- On the closed unit strip, `‖exp ((z - θ)²)‖ ≤ e exp (-(im z)²)` for `0 ≤ θ ≤ 1`. -/
private theorem norm_exp_sub_sq_le {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖cexp ((z - θ) ^ 2)‖ ≤ Real.exp 1 * Real.exp (-z.im ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
  simp only [sq, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, sub_zero]
  nlinarith [hz'.1, hz'.2, hθ.1, hθ.2]

/-- On the closed unit strip, `‖exp (δ z² + ω z)‖ ≤ exp (δ + |ω|)`. -/
private theorem norm_exp_mul_sq_add_mul_le {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z)‖ ≤ Real.exp (δ + |ω|) := by
  rw [Complex.norm_exp, Real.exp_le_exp]
  have hz' : z.re ∈ Icc (0 : ℝ) 1 := hz
  simp only [sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hω : ω * z.re ≤ |ω| := by
    calc ω * z.re ≤ |ω * z.re| := le_abs_self _
      _ = |ω| * z.re := by rw [abs_mul, abs_of_nonneg hz'.1]
      _ ≤ |ω| := mul_le_of_le_one_right (abs_nonneg ω) hz'.2
  have h1 : z.re * z.re ≤ 1 := by nlinarith [hz'.1, hz'.2]
  have h2 : δ * (z.re * z.re - z.im * z.im) ≤ δ := by
    nlinarith [mul_nonneg hδ.le (mul_self_nonneg z.im)]
  linarith

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
    Bornology.IsBounded ((fun z ↦ cexp ((z - θ) ^ 2) • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
      ι (shiftedFamily hq hq_top a b ((z - c) * κ) u)) '' verticalClosedStrip 0 1) := by
  set ν : ℂ → ℂ := fun z ↦ (z - c) * κ
  have hre (z : ℂ) : (ν z).re = (z.re - c) * κ := by simp [ν]
  set f : ℂ → W₀ := fun z ↦ ι (shiftedFamily hq hq_top a b (ν z) u)
  -- The Gaussian factor beats the polynomial growth of the family on the strip.
  obtain ⟨C, hC⟩ := exists_norm_shiftedFamily_le (E := E) (F := F) hq hq_top
  set N := finrank ℝ E / 2 + 1
  refine isBounded_iff_forall_norm_le.2 ⟨Real.exp 1 * Real.exp (δ + |ω|) * (‖ι‖ * (C *
    ((1 + |κ| + |κ|) ^ N * Real.exp (N ^ 2 / 4)) * ‖u‖)), ?_⟩
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
  have hf : ‖f z‖ ≤ ‖ι‖ * (C * ((1 + |κ| + |κ| * |z.im|) ^ N) * ‖u‖) := by
    refine (ι.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine ((shiftedFamily hq hq_top a b (ν z)).le_opNorm u).trans ?_
    gcongr
    refine (hC a b (ν z) ((hre z).trans_le (hcl _ hz))).trans ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) C.coe_nonneg
    nlinarith [abs_nonneg κ, abs_nonneg z.im]
  rw [norm_smul, norm_smul]
  have hg := add_mul_abs_pow_mul_exp_neg_sq_le (abs_nonneg κ) (by positivity : 0 ≤ 1 + |κ|) N z.im
  calc ‖cexp ((z - θ) ^ 2)‖ * (‖cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z)‖ * ‖f z‖)
      ≤ Real.exp 1 * Real.exp (-z.im ^ 2) * (Real.exp (δ + |ω|) *
          (‖ι‖ * (C * ((1 + |κ| + |κ| * |z.im|) ^ N) * ‖u‖))) := by
        gcongr
        · exact norm_exp_sub_sq_le hθ hz
        · exact norm_exp_mul_sq_add_mul_le hδ ω hz
    _ = Real.exp 1 * Real.exp (δ + |ω|) * (‖ι‖ * (C * ((1 + |κ| + |κ| * |z.im|) ^ N *
          Real.exp (-z.im ^ 2)) * ‖u‖)) := by ring
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
    DiffContOnCl ℂ (fun z ↦ cexp ((z - θ) ^ 2) • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
        ι (shiftedFamily hq hq_top a b ((z - c) * κ) u)) (verticalStrip 0 1) ∧
      Bornology.IsBounded ((fun z ↦ cexp ((z - θ) ^ 2) • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
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
  have he₁ : Differentiable ℂ fun z : ℂ ↦ cexp ((z - θ) ^ 2) := by fun_prop
  have he₂ : Differentiable ℂ fun z : ℂ ↦ cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) := by fun_prop
  exact ⟨he₁.diffContOnCl.smul (he₂.diffContOnCl.smul hdc),
    isBounded_aux hq hq_top ι hc hcl u hδ ω hθ⟩

/-- `‖T t‖ ≤ K` for the boundary operators `T t = exp ((x + i t - θ)²) J^{-b} J^{i t κ} J^a`. -/
private theorem norm_exp_smul_shiftedFamily_le {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) {C : ℝ≥0} (hC : ∀ (a b : ℝ) (w : ℂ), w.re ≤ 0 →
      ‖(shiftedFamily hq hq_top a b w : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F))‖ ≤
        C * (1 + ‖w‖) ^ (finrank ℝ E / 2 + 1)) {θ x : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b κ t : ℝ) :
    ‖cexp ((x + (t : ℂ) * I - θ) ^ 2) • (shiftedFamily hq hq_top a b ((t : ℂ) * I * κ) :
      H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F))‖ ≤ Real.exp 1 * (C * ((1 + |κ|) ^ (finrank ℝ E / 2 + 1) *
        Real.exp ((finrank ℝ E / 2 + 1 : ℕ) ^ 2 / 4))) := by
  set N := finrank ℝ E / 2 + 1
  have hz : (x + (t : ℂ) * I) ∈ verticalClosedStrip 0 1 := by
    simpa [verticalClosedStrip] using hx
  have hn : ‖(t : ℂ) * I * κ‖ = |κ| * |t| := by
    simp [Complex.norm_real, mul_comm]
  rw [norm_smul]
  have h1 := norm_exp_sub_sq_le hθ hz
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_add, add_zero] at h1
  have h2 := hC a b ((t : ℂ) * I * κ) (by simp)
  rw [hn] at h2
  have h3 := add_mul_abs_pow_mul_exp_neg_sq_le (abs_nonneg κ) zero_le_one N t
  calc ‖cexp ((x + (t : ℂ) * I - θ) ^ 2)‖ * ‖shiftedFamily hq hq_top a b ((t : ℂ) * I * κ)‖
      ≤ Real.exp 1 * Real.exp (-t ^ 2) * (C * (1 + |κ| * |t|) ^ N) := by gcongr
    _ = Real.exp 1 * (C * ((1 + |κ| * |t|) ^ N * Real.exp (-t ^ 2))) := by ring
    _ ≤ _ := by gcongr

/-- The boundary operator `exp ((x + i t - θ)²) J^{-b} J^{i t κ} J^a : H^{a,q} → H^{b,q}`. -/
private def boundaryOp {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q) (hq_top : q ≠ ∞)
    (a b κ x θ t : ℝ) : H^{a, q}(E, F) →L[ℂ] H^{b, q}(E, F) :=
  cexp (((x : ℝ) + (t : ℂ) * I - θ) ^ 2) • shiftedFamily hq hq_top a b ((t : ℂ) * I * κ)

/-- Boundary traces given by uniformly bounded operator families `T₀ t`, `T₁ t` applied to the
traces of `G` have norm at most the bound times the norm of `G`. -/
private theorem norm_le_mul_norm_of_forall_apply_eq {X₀ X₁ Y₀ Y₁ : Type*}
    [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁]
    {K : ℝ} (hK : 0 ≤ K) (G : C₀(ℝ, X₀) × C₀(ℝ, X₁)) (g : (ℝ →ᵇ Y₀) × (ℝ →ᵇ Y₁))
    (T₀ : ℝ → X₀ →L[ℂ] Y₀) (T₁ : ℝ → X₁ →L[ℂ] Y₁) (hT₀ : ∀ t, ‖T₀ t‖ ≤ K)
    (hT₁ : ∀ t, ‖T₁ t‖ ≤ K) (hg₀ : ∀ t, g.1 t = T₀ t (G.1 t)) (hg₁ : ∀ t, g.2 t = T₁ t (G.2 t)) :
    ‖g‖ ≤ K * ‖G‖ := by
  refine norm_prod_le_iff.2 ⟨(BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_,
    (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_⟩
  · rw [hg₀]
    refine ((T₀ t).le_opNorm _).trans (mul_le_mul (hT₀ t) ?_ (norm_nonneg _) hK)
    exact (G.1.toBCF.norm_coe_le_norm t).trans
      (by rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; exact norm_fst_le _)
  · rw [hg₁]
    refine ((T₁ t).le_opNorm _).trans (mul_le_mul (hT₁ t) ?_ (norm_nonneg _) hK)
    exact (G.2.toBCF.norm_coe_le_norm t).trans
      (by rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; exact norm_snd_le _)

/-- The boundary operators applied to a continuously varying multiple of a fixed vector form a
continuous function of `t`. -/
private theorem continuous_boundaryOp_apply_smul {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 1 < q)
    (hq_top : q ≠ ∞) (a b κ x θ : ℝ) {c : ℝ → ℂ} (hc : Continuous c) (v : H^{a, q}(E, F)) :
    Continuous fun t ↦ boundaryOp hq hq_top a b κ x θ t (c t • v) := by
  simp only [boundaryOp, smul_apply, map_smul]
  exact hc.smul ((by fun_prop : Continuous fun t : ℝ ↦ cexp (((x : ℝ) + (t : ℂ) * I - θ) ^ 2)).smul
    ((continuousOn_shiftedFamily_apply hq hq_top a b v).comp_continuous
      (by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ) * I * κ) fun t ↦ by simp))

/-- A bounded operator applied to `exp (δ z² + ω z) v`, `z` in the closed unit strip. -/
private theorem norm_apply_exp_smul_le {X₀ Y₀ : Type*} [NormedAddCommGroup X₀] [NormedSpace ℂ X₀]
    [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] {T : X₀ →L[ℂ] Y₀} {K : ℝ} (hT : ‖T‖ ≤ K)
    (hK : 0 ≤ K) {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1)
    (v : X₀) : ‖T (cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) • v)‖ ≤
      K * (Real.exp (δ + |ω|) * ‖v‖) := by
  refine (T.le_opNorm _).trans (mul_le_mul hT ?_ (norm_nonneg _) hK)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_exp_mul_sq_add_mul_le hδ ω hz) (norm_nonneg _)

/-- The boundary traces of the strip function of `exp (δ z² + ω z) x`: the boundary operators
applied to the traces of `exp (δ z² + ω z) x` are bounded continuous functions. -/
private theorem exists_traces_expGaussianTrace {p₀ p₁ : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁)
    (hp₁_top : p₁ ≠ ∞) {a₀ a₁ b₀ b₁ κ θ : ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hT₀ : ∀ t, ‖(boundaryOp hp₀ hp₀_top a₀ b₀ κ 0 θ t :
      H^{a₀, p₀}(E, F) →L[ℂ] H^{b₀, p₀}(E, F))‖ ≤ K)
    (hT₁ : ∀ t, ‖(boundaryOp hp₁ hp₁_top a₁ b₁ κ 1 θ t :
      H^{a₁, p₁}(E, F) →L[ℂ] H^{b₁, p₁}(E, F))‖ ≤ K)
    (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) {δ : ℝ} (hδ : 0 < δ) (ω : ℝ) :
    ∃ g : (ℝ →ᵇ H^{b₀, p₀}(E, F)) × (ℝ →ᵇ H^{b₁, p₁}(E, F)),
      (∀ t, g.1 t = boundaryOp hp₀ hp₀_top a₀ b₀ κ 0 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t)) ∧
      (∀ t, g.2 t = boundaryOp hp₁ hp₁_top a₁ b₁ κ 1 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t)) := by
  revert x
  set X := besselPotentialSpace E F a₀ p₀ a₁ p₁
  intro x
  set x₀ := X.interFst x
  set x₁ := X.interSnd x
  set T₀ := boundaryOp (E := E) (F := F) hp₀ hp₀_top a₀ b₀ κ 0 θ
  set T₁ := boundaryOp (E := E) (F := F) hp₁ hp₁_top a₁ b₁ κ 1 θ
  have hstrip₀ (t : ℝ) : (t : ℂ) * I ∈ verticalClosedStrip 0 1 := by
    simp [verticalClosedStrip]
  have hstrip₁ (t : ℝ) : 1 + (t : ℂ) * I ∈ verticalClosedStrip 0 1 := by
    simp [verticalClosedStrip]
  have hcont₀ : Continuous fun t : ℝ ↦ T₀ t ((X.expGaussianTrace hδ ω x :
      C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t) := by
    simpa [x₀] using continuous_boundaryOp_apply_smul hp₀ hp₀_top a₀ b₀ κ 0 θ
      (c := fun t : ℝ ↦ cexp ((δ : ℂ) * (t * I) ^ 2 + (ω : ℂ) * (t * I))) (by fun_prop) x₀
  have hcont₁ : Continuous fun t : ℝ ↦ T₁ t ((X.expGaussianTrace hδ ω x :
      C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t) := by
    simpa [x₁] using continuous_boundaryOp_apply_smul hp₁ hp₁_top a₁ b₁ κ 1 θ
      (c := fun t : ℝ ↦ cexp ((δ : ℂ) * (1 + t * I) ^ 2 + (ω : ℂ) * (1 + t * I))) (by fun_prop) x₁
  have hb₀ (t : ℝ) : ‖T₀ t ((X.expGaussianTrace hδ ω x :
      C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t)‖ ≤
        K * (Real.exp (δ + |ω|) * ‖x₀‖) := by
    rw [X.expGaussianTrace_apply_fst]
    exact norm_apply_exp_smul_le (hT₀ t) hK hδ ω (hstrip₀ t) x₀
  have hb₁ (t : ℝ) : ‖T₁ t ((X.expGaussianTrace hδ ω x :
      C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t)‖ ≤
        K * (Real.exp (δ + |ω|) * ‖x₁‖) := by
    rw [X.expGaussianTrace_apply_snd]
    exact norm_apply_exp_smul_le (hT₁ t) hK hδ ω (hstrip₁ t) x₁
  set g₀ := BoundedContinuousFunction.ofNormedAddCommGroup _ hcont₀ _ hb₀
  set g₁ := BoundedContinuousFunction.ofNormedAddCommGroup _ hcont₁ _ hb₁
  exact ⟨(g₀, g₁), fun t ↦ rfl, fun t ↦ rfl⟩

/-- The base case of `exists_besselPotentialSpace_complexMethod_map_aux`: the strip function
`Ψ` of an elementary admissible function `exp (δ z² + ω z) x` is a bounded-boundary strip function
whose traces are the boundary operators applied to those of `exp (δ z² + ω z) x`. -/
private theorem exists_isBoundedStripFunction_expGaussianTrace {p₀ p₁ : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] (hp₀ : 1 < p₀) (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁)
    (hp₁_top : p₁ ≠ ∞) {a₀ a₁ b₀ b₁ : ℝ} {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {K : ℝ} (hK : 0 ≤ K)
    (hT₀ : ∀ t, ‖(boundaryOp hp₀ hp₀_top a₀ b₀ ((a₁ - b₁) - (a₀ - b₀)) 0 θ t :
      H^{a₀, p₀}(E, F) →L[ℂ] H^{b₀, p₀}(E, F))‖ ≤ K)
    (hT₁ : ∀ t, ‖(boundaryOp hp₁ hp₁_top a₁ b₁ ((a₁ - b₁) - (a₀ - b₀)) 1 θ t :
      H^{a₁, p₁}(E, F) →L[ℂ] H^{b₁, p₁}(E, F))‖ ≤ K)
    (x : (besselPotentialSpace E F a₀ p₀ a₁ p₁).inter) {δ : ℝ} (hδ : 0 < δ) (ω : ℝ)
    {Ψ : ℂ → (besselPotentialSpace E F b₀ p₀ b₁ p₁).SumSpace}
    (hdc : DiffContOnCl ℂ Ψ (verticalStrip 0 1))
    (hbd : Bornology.IsBounded (Ψ '' verticalClosedStrip 0 1))
    (hΨ : ∀ z ∈ verticalClosedStrip 0 1,
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ z) =
      cexp ((z - θ) ^ 2) • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
        fourierMultiplierCLM F (japaneseBracketCpow (a₀ + z * ((a₁ - b₁) - (a₀ - b₀) : ℝ) - b₀))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).interFst x).toDistr) :
    ∃ g : (ℝ →ᵇ H^{b₀, p₀}(E, F)) × (ℝ →ᵇ H^{b₁, p₁}(E, F)),
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).IsBoundedStripFunction Ψ g ∧
      (∀ t, g.1 t = boundaryOp hp₀ hp₀_top a₀ b₀ ((a₁ - b₁) - (a₀ - b₀)) 0 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t)) ∧
      (∀ t, g.2 t = boundaryOp hp₁ hp₁_top a₁ b₁ ((a₁ - b₁) - (a₀ - b₀)) 1 θ t
        (((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x :
          C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t)) ∧
      (besselPotentialSpace E F b₀ p₀ b₁ p₁).sumSpaceEmbed (Ψ θ) =
        besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
          ((besselPotentialSpace E F a₀ p₀ a₁ p₁).sumSpaceEmbed
            ((besselPotentialSpace E F a₀ p₀ a₁ p₁).stripEval θ
              ((besselPotentialSpace E F a₀ p₀ a₁ p₁).expGaussianTrace hδ ω x))) := by
  revert x hΨ
  set X := besselPotentialSpace E F a₀ p₀ a₁ p₁
  set Y := besselPotentialSpace E F b₀ p₀ b₁ p₁
  intro x hΨ
  set κ : ℝ := (a₁ - b₁) - (a₀ - b₀) with hκ_def
  set x₀ := X.interFst x
  have hx : (X.interSnd x).toDistr = x₀.toDistr := by
    simpa [X, x₀] using (X.embed₀_interFst x).symm
  obtain ⟨g, hg₀, hg₁⟩ := exists_traces_expGaussianTrace hp₀ hp₀_top hp₁ hp₁_top (θ := θ)
    (b₀ := b₀) (b₁ := b₁) hK hT₀ hT₁ x hδ ω
  refine ⟨g, ⟨hdc, hbd, fun t ↦ ?_, fun t ↦ ?_⟩, hg₀, hg₁, ?_⟩
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
      besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow, sub_self, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.exp_zero, one_smul]
    congr 3
    rw [hκ_def]
    push_cast
    ring_nf

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
          cexp ((z - θ) ^ 2) • cexp ((δ : ℂ) * z ^ 2 + (ω : ℂ) * z) •
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
  set K : ℝ := Real.exp 1 * ((C₀ + C₁) * ((1 + |κ|) ^ N * Real.exp (N ^ 2 / 4)))
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
  set L := besselPotential E F ((1 - θ) * (a₀ - b₀) + θ * (a₁ - b₁))
  -- Every elementary admissible function `G` has a matching strip function with traces `T G`.
  have key : ∀ G ∈ X.elementaryStripTraces, ∃ (Ψ : ℂ → Y.SumSpace)
      (g : (ℝ →ᵇ H^{b₀, p₀}(E, F)) × (ℝ →ᵇ H^{b₁, p₁}(E, F))), Y.IsBoundedStripFunction Ψ g ∧
        (∀ t, g.1 t = T₀ t ((G : C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).1 t)) ∧
        (∀ t, g.2 t = T₁ t ((G : C₀(ℝ, H^{a₀, p₀}(E, F)) × C₀(ℝ, H^{a₁, p₁}(E, F))).2 t)) ∧
        Y.sumSpaceEmbed (Ψ θ) = L (X.sumSpaceEmbed (X.stripEval θ G)) := by
    intro G hG
    induction hG using elementaryStripTraces_induction with
    | @expGaussian δ hδ ω x =>
      obtain ⟨Ψ, hdc, hbd, hΨ⟩ := hstrip x hδ ω
      obtain ⟨g, hg⟩ := exists_isBoundedStripFunction_expGaussianTrace hp₀ hp₀_top hp₁ hp₁_top hθ
        hK hT₀ hT₁ x hδ ω hdc hbd hΨ
      exact ⟨Ψ, g, hg⟩
    | zero => exact ⟨0, 0, .zero, fun t ↦ by simp, fun t ↦ by simp, by simp⟩
    | add G H _ _ hG hH =>
      obtain ⟨Ψ, g, hΨ, hg₀, hg₁, hθG⟩ := hG
      obtain ⟨Φ, h, hΦ, hh₀, hh₁, hθH⟩ := hH
      exact ⟨Ψ + Φ, g + h, hΨ.add hΦ, fun t ↦ by simp [hg₀, hh₀],
        fun t ↦ by simp [hg₁, hh₁], by simp [hθG, hθH]⟩
    | smul c G _ hG =>
      obtain ⟨Ψ, g, hΨ, hg₀, hg₁, hθG⟩ := hG
      exact ⟨c • Ψ, c • g, hΨ.const_smul c, fun t ↦ by simp [hg₀],
        fun t ↦ by simp [hg₁], by simp [hθG]⟩
  obtain ⟨T, -, hT⟩ := ComplexMethodSpace.exists_map_of_forall_elementaryStripTraces hθ L hK
    fun G hG ↦ by
      obtain ⟨Ψ, g, hΨ, hg₀, hg₁, hθG⟩ := key G hG
      exact ⟨Ψ, g, hΨ, hθG, norm_le_mul_norm_of_forall_apply_eq hK _ g T₀ T₁ hT₀ hT₁ hg₀ hg₁⟩
  exact ⟨T, hT⟩

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
    have hx : (X.interSnd x).toDistr = (X.interFst x).toDistr := by
      simpa [X] using (X.embed₀_interFst x).symm
    obtain ⟨hdc, hbd⟩ := diffContOnCl_and_isBounded_aux hp₁ hp₁_top Y.sndToSum
      (c := 1) (κ := κ) ⟨zero_le_one, le_rfl⟩
      (fun y hy ↦ mul_nonpos_of_nonpos_of_nonneg (by linarith [hy.2]) hκ)
      (hκ.eq_or_lt.imp Eq.symm fun h y hy ↦ mul_neg_of_neg_of_pos (by linarith [hy.2]) h)
      (X.interSnd x) hδ ω hθ
    refine ⟨_, hdc, hbd, fun z hz ↦ ?_⟩
    have hre : ((z - (1 : ℝ)) * κ).re ≤ 0 := by
      have : z.re ≤ 1 := hz.2
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    simp only [map_smul, sumSpaceEmbed_sndToSum, Y, besselPotentialSpace_embed₁_apply]
    rw [toDistr_shiftedFamily hre, hx]
    congr 4
    rw [hκ_def]
    push_cast
    ring_nf
  · -- `λ₀ ≥ λ₁`: compute `J^{λ(z)} x` from the component of `x` in `H^{a₀,p₀}`.
    obtain ⟨hdc, hbd⟩ := diffContOnCl_and_isBounded_aux hp₀ hp₀_top Y.fstToSum
      (c := 0) (κ := κ) ⟨le_rfl, zero_le_one⟩
      (fun y hy ↦ mul_nonpos_of_nonneg_of_nonpos (by linarith [hy.1]) hκ)
      (hκ.eq_or_lt.imp id fun h y hy ↦ mul_neg_of_pos_of_neg (by linarith [hy.1]) h)
      (X.interFst x) hδ ω hθ
    refine ⟨_, hdc, hbd, fun z hz ↦ ?_⟩
    have hre : ((z - (0 : ℝ)) * κ).re ≤ 0 := by
      have : 0 ≤ z.re := hz.1
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
        Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    simp only [map_smul, sumSpaceEmbed_fstToSum, Y, besselPotentialSpace_embed₀_apply]
    rw [toDistr_shiftedFamily hre]
    congr 4
    rw [hκ_def]
    push_cast
    ring_nf

end Stein

/-! ### The identification `[H^{s₀,p₀}, H^{s₁,p₁}]_θ = H^{s_θ,p_θ}` -/

section Identification

variable {s₀ s₁ : ℝ} {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] {θ : ℝ}

omit [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)] in
/-- The interpolated exponent `1 / p = (1 - θ) / p₀ + θ / p₁` of finite exponents is finite. -/
private theorem ne_top_of_inv_eq (hθ : θ ∈ Ioo (0 : ℝ) 1) (hp₀_top : p₀ ≠ ∞)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) : p ≠ ∞ := by
  intro h
  rw [h, ENNReal.inv_top, eq_comm, add_eq_zero, mul_eq_zero, ENNReal.ofReal_eq_zero,
    ENNReal.inv_eq_zero] at hp
  rcases hp.1 with h₁ | h₁
  · linarith [hθ.2]
  · exact hp₀_top h₁

variable (E F s₀ s₁ p₀ p₁) in
/-- **Complex interpolation of Bessel-potential spaces** (Bergh–Löfström, Theorem 6.4.5 (7)). For
`1 < p₀, p₁ < ∞`, `0 < θ < 1`, real orders `s₀, s₁` and the interpolated parameters
`s_θ = (1 - θ) s₀ + θ s₁` and `1 / p = (1 - θ) / p₀ + θ / p₁`, Calderón's complex interpolation
space `[H^{s₀,p₀}, H^{s₁,p₁}]_θ` is isomorphic to `H^{s_θ,p}`, by an isomorphism that keeps the
underlying tempered distribution. -/
theorem exists_besselPotentialSpace_complexMethod_continuousLinearEquiv (hp₀ : 1 < p₀)
    (hp₀_top : p₀ ≠ ∞) (hp₁ : 1 < p₁) (hp₁_top : p₁ ≠ ∞) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    ∃ e : (besselPotentialSpace E F s₀ p₀ s₁ p₁).ComplexMethodSpace θ ≃L[ℂ]
        H^{(1 - θ) * s₀ + θ * s₁, p}(E, F),
      ∀ u, (e u).toDistr =
        (besselPotentialSpace E F s₀ p₀ s₁ p₁).sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
  set C := besselPotentialSpace E F s₀ p₀ s₁ p₁
  set D := besselPotentialSpace E F 0 p₀ 0 p₁
  set sθ := (1 - θ) * s₀ + θ * s₁
  have hp_top := ne_top_of_inv_eq hθ hp₀_top hp
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
    ((toOrderZero E F sθ p).symm.toContinuousLinearEquiv : H^{0, p}(E, F) →L[ℂ] _) ∘L
      (eD.toContinuousLinearEquiv : D.ComplexMethodSpace θ →L[ℂ] _) ∘L TB
  set g : H^{sθ, p}(E, F) →L[ℂ] C.ComplexMethodSpace θ :=
    TA ∘L (eD.symm.toContinuousLinearEquiv : H^{0, p}(E, F) →L[ℂ] _) ∘L
      ((toOrderZero E F sθ p).toContinuousLinearEquiv : H^{sθ, p}(E, F) →L[ℂ] _)
  have hJ := fourierMultiplierCLM_japaneseBracketCpow_neg_besselPotential (E := E) (F := F) sθ
  have hf (u : C.ComplexMethodSpace θ) :
      (f u).toDistr = C.sumSpaceEmbed (ComplexMethodSpace.toSum u) := by
    simp only [f, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [toDistr_toOrderZero_symm, toDistr_besselPotentialSpaceOfOrderComplexMethodEquiv_apply,
      hTB, hJ]
  have hg (v : H^{sθ, p}(E, F)) :
      C.sumSpaceEmbed (ComplexMethodSpace.toSum (g v)) = v.toDistr := by
    simp only [g, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [hTA, sumSpaceEmbed_toSum_besselPotentialSpaceOfOrderComplexMethodEquiv_symm_apply,
      toDistr_toOrderZero, besselPotential_eq_fourierMultiplierCLM_japaneseBracketCpow,
      fourierMultiplierCLM_japaneseBracketCpow_fourierMultiplierCLM_japaneseBracketCpow]
    push_cast
    rw [add_neg_cancel, fourierMultiplierCLM_japaneseBracketCpow_zero]
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
