/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.Pseudodifferential.Recovery
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# Positive operators have positive principal symbols

A pseudodifferential operator `Op(a)` with a classical symbol `a` of order `m` is tested on
high-frequency wave packets

`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v`, `t → ∞`,

with a fixed amplitude `φ`, frequency direction `ξ ≠ 0` and vector `v`. Removing the phase,
`t ^ (-m) exp(-i ⟪x, t ξ⟫) Op(a) u_t (x) → σ(a)(x, ξ) (φ(x) v)`, where `σ(a)` is the principal
symbol (`TauCeti.ClassicalSymbol.tendsto_quantizeSchwartzValue_cutoffExponential_atTop`). Hence
for a compactly supported amplitude the rescaled pairings converge,

`t ^ (-m) ∫ ⟪Op(a) u_t (x), u_t (x)⟫ dx → ∫ |φ(x)|² ⟪σ(a)(x, ξ) v, v⟫ dx`

(`TauCeti.ClassicalSymbol.tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential`).

If `Op(a)` is positive on the compactly supported Schwartz functions supported in an open set
`U`, that is `0 ≤ ∫ ⟪Op(a) u, u⟫` there (a complex number that is real and nonnegative), then
these limits are nonnegative for every amplitude supported in `U`. Concentrating the amplitude
near a point shows that the principal symbol is a positive operator on the fibre at every
position of `U` and every frequency
(`TauCeti.ClassicalSymbol.isPositive_coefficient_principal`). If `a` is moreover elliptic, then
at nonzero frequencies the principal symbol is invertible, hence strictly positive
(`TauCeti.ClassicalSymbol.isStrictlyPositive_coefficient_principal`). This is the positivity
under which the powers `σ(a)(x, ξ) ^ z` of the principal symbol of a positive elliptic operator
are defined by the continuous functional calculus.

The phase-free form of the wave packet quantization is the exact identity
`exp(-i ⟪x, ζ⟫) Op(a) (y ↦ exp(i ⟪y, ζ⟫) φ(y) v) (x) = ∫ exp(2πi ⟪η, x⟫) a(x, ζ + 2πη) (𝓕 φ η) v dη`
(`TauCeti.exp_smul_quantizeSchwartzValue_cutoffExponential_one`). After the rescaling by
`t ^ (-m)` with `ζ = t ξ`, the integrand converges by
`TauCeti.ClassicalSymbol.tendsto_rpow_neg_smul_coefficient_smul`, and Peetre's inequality
dominates it uniformly for `t ≥ 1` and positions in a compact set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators acting on rapidly oscillating functions `exp(i t ⟪y, ξ⟫) φ(y)`).
-/

public section

open scoped FourierTransform SchwartzMap InnerProductSpace RealInnerProductSpace ComplexOrder
  ContDiff
open MeasureTheory Real FourierTransform Filter Topology

noncomputable section

namespace TauCeti

section WavePacket

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Quantization of a wave packet.** For the wave packet `y ↦ exp(i ⟪y, ζ⟫) φ(y) v`, the
quantization with the phase `exp(i ⟪x, ζ⟫)` removed is the integral
`∫ exp(2πi ⟪η, x⟫) a(x, ζ + 2πη) (𝓕 φ η) v dη`. -/
theorem exp_smul_quantizeSchwartzValue_cutoffExponential_one [CompleteSpace V]
    (a : E × E → V →L[ℂ] W) (φ : 𝓢(E, ℂ)) (ζ : E) (v : V) (x : E) :
    Complex.exp (-(⟪x, ζ⟫ * Complex.I)) • quantizeSchwartzValue a (φ.cutoffExponential 1 ζ v) x =
      ∫ η, 𝐞 ⟪η, x⟫ • a (x, ζ + (2 * π) • η) (𝓕 φ η • v) := by
  have hphase : Complex.exp (-(⟪x, ζ⟫ * Complex.I)) * 𝐞 ⟪(2 * π)⁻¹ • ζ, x⟫ = 1 := by
    rw [real_inner_comm x, ← exp_inner_mul_I_eq_fourierChar, ← Complex.exp_add]
    simp
  rw [quantizeSchwartzValue_cutoffExponential a φ one_ne_zero, ← integral_smul]
  congr 1 with η
  rw [one_smul, mul_one, inner_add_left, AddChar.map_add_eq_mul, Circle.smul_def,
    Circle.smul_def, smul_smul, Circle.coe_mul, ← mul_assoc, hphase, one_mul]

end WavePacket

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- At a nonzero frequency `ξ` and positions in a compact set, `t ^ (-m) ‖a(y, t ξ + 2πη)‖` is
at most a multiple of `⟨2πη⟩ ^ |m|` for all `t ≥ 1`. -/
private lemma exists_norm_rpow_neg_smul_coefficient_le (a : Symbol n V W m)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    ∃ B, ∀ y ∈ K, ∀ t : ℝ, 1 ≤ t → ∀ η : CoordinateSpace n,
      ‖t ^ (-m) • a.coefficient (y, t • ξ + (2 * π) • η)‖ ≤
        B * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) := by
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le K hK
  have hr : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set M := max ((‖ξ‖ ^ 2) ^ (m / 2)) ((1 + ‖ξ‖ ^ 2) ^ (m / 2))
  refine ⟨C * 2 ^ (|m| / 2) * M, fun y hy t ht η ↦ ?_⟩
  have ht0 : 0 < t := one_pos.trans_le ht
  have htξ : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
  have hbr : (1 + ‖t • ξ‖ ^ 2) ^ (m / 2) ≤ M * t ^ m :=
    one_add_norm_sq_rpow_half_le (by positivity) ht0
      ⟨by rw [htξ]; nlinarith, by rw [htξ]; nlinarith⟩ m
  have hle := hC y hy (t • ξ + (2 * π) • η)
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hle) (by positivity)
  have htm : t ^ (-m) * t ^ m = 1 := by rw [← Real.rpow_add ht0]; simp
  calc ‖t ^ (-m) • a.coefficient (y, t • ξ + (2 * π) • η)‖
      = t ^ (-m) * ‖a.coefficient (y, t • ξ + (2 * π) • η)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ t ^ (-m) * (C * (2 ^ (|m| / 2) * (M * t ^ m) *
          (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2))) := by
        gcongr
        refine hle.trans (mul_le_mul_of_nonneg_left ?_ hC0)
        refine (one_add_norm_add_sq_rpow_le_mul m _ _).trans ?_
        gcongr
    _ = C * 2 ^ (|m| / 2) * M * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) := by
        linear_combination (C * 2 ^ (|m| / 2) * M * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2)) * htm

/-- The rescaled phase-free quantization of the wave packet of frequency `t ξ` is the integral of
`exp(2πi ⟪η, x⟫) t ^ (-m) a(x, t ξ + 2πη) (𝓕 φ η) v`. -/
private lemma rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential [CompleteSpace V]
    (a : Symbol n V W m) (x ξ : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ))
    (v : V) (t : ℝ) :
    t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.coefficient (φ.cutoffExponential 1 (t • ξ) v) x =
      ∫ η, 𝐞 ⟪η, x⟫ • (t ^ (-m) • a.coefficient (x, t • ξ + (2 * π) • η))
        (𝓕 φ η • v) := by
  rw [exp_smul_quantizeSchwartzValue_cutoffExponential_one, ← integral_smul]
  congr 1 with η
  rw [smul_apply, smul_comm]

/-- The integrand of `rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential` is
dominated by `B ‖v‖ ⟨2πη⟩ ^ |m| ‖𝓕 φ η‖` for `t ≥ 1`. -/
private lemma norm_integrand_le {a : Symbol n V W m} {K : Set (CoordinateSpace n)}
    {ξ : CoordinateSpace n} {B : ℝ}
    (hB : ∀ y ∈ K, ∀ t : ℝ, 1 ≤ t → ∀ η : CoordinateSpace n,
      ‖t ^ (-m) • a.coefficient (y, t • ξ + (2 * π) • η)‖ ≤
        B * (1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2))
    {x : CoordinateSpace n} (hx : x ∈ K) {t : ℝ} (ht : 1 ≤ t) (φ : 𝓢(CoordinateSpace n, ℂ))
    (v : V) (η : CoordinateSpace n) :
    ‖𝐞 ⟪η, x⟫ • (t ^ (-m) • a.coefficient (x, t • ξ + (2 * π) • η)) (𝓕 φ η • v)‖ ≤
      B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖) := by
  rw [Circle.norm_smul]
  refine ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (hB x hx t ht η) (norm_nonneg _))).trans_eq ?_
  rw [norm_smul (𝓕 φ η) v]
  ring

/-- **The principal symbol from high-frequency wave packets.** For a classical symbol `a` of order
`m`, a nonzero frequency `ξ`, a Schwartz amplitude `φ` and `v ∈ V`, the wave packets
`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` satisfy

`t ^ (-m) exp(-i ⟪x, t ξ⟫) Op(a) u_t (x) → σ(a)(x, ξ) (φ(x) v)` as `t → ∞`. -/
theorem tendsto_quantizeSchwartzValue_cutoffExponential_atTop [CompleteSpace V] [CompleteSpace W]
    (a : ClassicalSymbol n V W m) (x : CoordinateSpace n) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0)
    (φ : 𝓢(CoordinateSpace n, ℂ)) (v : V) :
    Tendsto (fun t : ℝ ↦ t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.toSymbol.coefficient (φ.cutoffExponential 1 (t • ξ) v) x)
      atTop (𝓝 (a.principal.coefficient (x, ξ) (φ x • v))) := by
  obtain ⟨B, hB⟩ := exists_norm_rpow_neg_smul_coefficient_le a.toSymbol isCompact_singleton hξ
  set σ := a.principal.coefficient (x, ξ)
  -- Fourier inversion evaluates the limit integral.
  have hlim : ∫ η, 𝐞 ⟪η, x⟫ • σ (𝓕 φ η • v) = σ (φ x • v) := by
    have hF : ∫ η, 𝐞 ⟪η, x⟫ • 𝓕 φ η = φ x := by
      rw [← Real.fourierInv_eq, ← SchwartzMap.fourierInv_coe, fourierInv_fourier_eq]
    have hint : Integrable fun η ↦ (𝐞 ⟪η, x⟫ • 𝓕 φ η) • v :=
      ((𝓕 φ).integrable.norm.mono' ((Real.continuous_fourierChar.comp
        (continuous_id.inner continuous_const)).smul (𝓕 φ).continuous).aestronglyMeasurable
          (.of_forall fun η ↦ (Circle.norm_smul _ _).le)).smul_const v
    calc ∫ η, 𝐞 ⟪η, x⟫ • σ (𝓕 φ η • v) = ∫ η, σ ((𝐞 ⟪η, x⟫ • 𝓕 φ η) • v) := by
          congr 1 with η
          rw [Circle.smul_def, Circle.smul_def, ← map_smul, smul_smul, smul_eq_mul]
      _ = σ (φ x • v) := by rw [σ.integral_comp_comm hint, integral_smul_const, hF]
  rw [← hlim]
  simp_rw [rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun η ↦ B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖))
    (.of_forall fun t ↦ ?_) ((eventually_ge_atTop 1).mono fun t ht ↦
      .of_forall (norm_integrand_le hB rfl ht φ v))
    (((𝓕 φ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|).const_mul _)
    (.of_forall fun η ↦ ?_)
  · have ha : Continuous fun η : CoordinateSpace n ↦
        t ^ (-m) • a.toSymbol.coefficient (x, t • ξ + (2 * π) • η) :=
      (a.toSymbol.contDiff_coefficient.continuous.comp'
        (by fun_prop : Continuous fun η : CoordinateSpace n ↦ (x, t • ξ + (2 * π) • η))).const_smul
          (t ^ (-m))
    exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (ha.clm_apply ((𝓕 φ).continuous.smul continuous_const))).aestronglyMeasurable
  -- Pointwise, `t ^ (-m) a(x, t (ξ + t⁻¹ 2πη)) → σ(a)(x, ξ)`.
  have hξη : Tendsto (fun t : ℝ ↦ ξ + t⁻¹ • ((2 * π) • η)) atTop (𝓝 ξ) := by
    have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).smul_const ((2 * π) • η)).const_add ξ
    rwa [zero_smul, add_zero] at h
  have ha : Tendsto (fun t : ℝ ↦ t ^ (-m) • a.toSymbol.coefficient (x, t • ξ + (2 * π) • η))
      atTop (𝓝 σ) := by
    refine ((a.tendsto_rpow_neg_smul_coefficient_smul hξ).comp
      (tendsto_id.prodMk (tendsto_const_nhds.prodMk_nhds hξη))).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp [smul_add, smul_smul, ht.ne']
  exact ((((ContinuousLinearMap.apply ℂ W (𝓕 φ η • v)).continuous.tendsto _).comp ha).const_smul
    (𝐞 ⟪η, x⟫))

/-- For positions in a compact set and `t ≥ 1`, the rescaled phase-free quantizations of the
wave packets of frequency `t ξ` are uniformly bounded. -/
private lemma exists_norm_rpow_neg_smul_exp_smul_quantizeSchwartzValue_le [CompleteSpace V]
    (a : Symbol n V W m) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) (φ : 𝓢(CoordinateSpace n, ℂ)) (v : V) :
    ∃ B, ∀ x ∈ K, ∀ t : ℝ, 1 ≤ t →
      ‖t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
        quantizeSchwartzValue a.coefficient (φ.cutoffExponential 1 (t • ξ) v) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_rpow_neg_smul_coefficient_le a hK hξ
  refine ⟨∫ η, B * ‖v‖ * ((1 + ‖(2 * π) • η‖ ^ 2) ^ (|m| / 2) * ‖𝓕 φ η‖), fun x hx t ht ↦ ?_⟩
  rw [rpow_neg_smul_exp_smul_quantizeSchwartzValue_cutoffExponential]
  exact norm_integral_le_of_norm_le
    (((𝓕 φ).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|).const_mul _)
    (.of_forall (norm_integrand_le hB hx ht φ v))

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Pairings with high-frequency wave packets.** For a classical symbol `a` of order `m`, a
nonzero frequency `ξ`, a compactly supported Schwartz amplitude `φ` and `v ∈ H`, the wave packets
`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v` satisfy

`t ^ (-m) ∫ ⟪Op(a) u_t (x), u_t (x)⟫ dx → ∫ |φ(x)|² ⟪σ(a)(x, ξ) v, v⟫ dx` as `t → ∞`. -/
theorem tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential
    (a : ClassicalSymbol n H H m) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0)
    {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : HasCompactSupport φ) (v : H) :
    Tendsto (fun t : ℝ ↦ t ^ (-m) • ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient
        (φ.cutoffExponential 1 (t • ξ) v) x, φ.cutoffExponential 1 (t • ξ) v x⟫_ℂ) atTop
      (𝓝 (∫ x, ‖φ x‖ ^ 2 • ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ)) := by
  set G : ℝ → CoordinateSpace n → H := fun t x ↦
    t ^ (-m) • Complex.exp (-(⟪x, t • ξ⟫ * Complex.I)) •
      quantizeSchwartzValue a.toSymbol.coefficient (φ.cutoffExponential 1 (t • ξ) v) x
  -- The phase of the wave packet cancels in the pairing.
  have hpair : ∀ t x, t ^ (-m) • ⟪quantizeSchwartzValue a.toSymbol.coefficient
      (φ.cutoffExponential 1 (t • ξ) v) x, φ.cutoffExponential 1 (t • ξ) v x⟫_ℂ =
        φ x * ⟪G t x, v⟫_ℂ := by
    intro t x
    simp only [G, SchwartzMap.cutoffExponential_apply φ one_ne_zero, one_smul, inner_smul_right,
      ← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
      map_mul, Complex.conj_I, mul_neg, neg_neg]
    ring
  have hlim : ∀ x, φ x * ⟪a.principal.coefficient (x, ξ) (φ x • v), v⟫_ℂ =
      ‖φ x‖ ^ 2 • ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ := by
    intro x
    rw [map_smul, inner_smul_left, ← mul_assoc, Complex.mul_conj', Complex.real_smul,
      Complex.ofReal_pow]
  simp_rw [← integral_smul, hpair, ← hlim]
  obtain ⟨B, hB⟩ := exists_norm_rpow_neg_smul_exp_smul_quantizeSchwartzValue_le a.toSymbol hφ hξ φ v
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖φ x‖ * (B * ‖v‖))
    (.of_forall fun t ↦ ?_) ((eventually_ge_atTop 1).mono fun t ht ↦ .of_forall fun x ↦ ?_)
    (φ.integrable.norm.mul_const _) (.of_forall fun x ↦ ?_)
  · have hG : Continuous (G t) :=
      ((Complex.continuous_exp.comp (by fun_prop)).smul
        (a.toSymbol.continuous_quantizeSchwartzValue_coefficient _)).const_smul _
    exact (φ.continuous.mul (hG.inner continuous_const)).aestronglyMeasurable
  · by_cases hx : x ∈ tsupport φ
    · rw [norm_mul]
      gcongr
      exact (norm_inner_le_norm _ _).trans (by gcongr; exact hB x hx t ht)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero]
      exact le_rfl
  · exact ((a.tendsto_quantizeSchwartzValue_cutoffExponential_atTop x hξ φ v).inner
      tendsto_const_nhds).const_mul (φ x)

/-- **A positive operator has a positive principal symbol.** Let `a` be a classical symbol of
order `m` with values in the endomorphisms of a complex Hilbert space `H`, and `U` an open set of
positions. If `Op(a)` is positive on the compactly supported Schwartz functions supported in `U`,
`0 ≤ ∫ ⟪Op(a) u (x), u (x)⟫ dx` (a real nonnegative number), then its principal symbol
`σ(a)(x, ξ)` is a positive operator on `H` at every `x ∈ U` and every frequency `ξ`. -/
theorem isPositive_coefficient_principal (a : ClassicalSymbol n H H m)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) (ξ : CoordinateSpace n) :
    (a.principal.coefficient (x, ξ)).IsPositive := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [a.principal.zero_covector]
    exact ContinuousLinearMap.isPositive_zero
  refine (ContinuousLinearMap.isPositive_iff_complex _).2 fun v ↦ ?_
  suffices h : 0 ≤ ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ from
    ⟨(Complex.eq_re_of_ofReal_le (r := 0) (by simpa using h)).symm, (Complex.nonneg_iff.1 h).1⟩
  have hσ : Continuous fun y ↦ a.principal.coefficient (y, ξ) :=
    a.principal.contDiffOn_coefficient.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun _ ↦ hξ
  refine nonneg_of_forall_integral_sq_smul_nonneg (μ := volume) hU
    ((hσ.clm_apply continuous_const).inner continuous_const) (fun ψ hψ hψc hψU ↦ ?_) hx
  -- Test on wave packets with the amplitude `ψ`, viewed as a complex Schwartz function.
  have hφ : HasCompactSupport (fun y ↦ (ψ y : ℂ)) := hψc.comp_left Complex.ofReal_zero
  set φ : 𝓢(CoordinateSpace n, ℂ) := hφ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)
  have hφφ : ⇑φ = fun y ↦ (ψ y : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hφc : HasCompactSupport φ := hφφ ▸ hφ
  have hφU : tsupport φ ⊆ U := hφφ ▸ (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψU
  have hlim := a.tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential hξ hφc v
  have hφψ : ∀ y, ‖φ y‖ ^ 2 = ψ y ^ 2 := fun y ↦ by simp [hφφ, sq_abs]
  simp_rw [hφψ] at hlim
  refine ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht ↦ ?_)
  -- The wave packet `y ↦ exp(i ⟪y, t ξ⟫) φ(y) v` is supported where `φ` is.
  have hsupp : Function.support (φ.cutoffExponential 1 (t • ξ) v) ⊆ Function.support φ :=
    fun y hy h0 ↦ hy (by simp [SchwartzMap.cutoffExponential_apply φ one_ne_zero, h0])
  rw [Complex.real_smul]
  exact mul_nonneg (Complex.zero_le_real.2 (Real.rpow_pos_of_pos ht _).le)
    (ha _ (hφc.mono hsupp) ((closure_mono hsupp).trans hφU))

/-- **A positive elliptic operator has a strictly positive principal symbol.** If moreover `a` is
elliptic, then at every position of `U` and every nonzero frequency the principal symbol is
invertible, hence strictly positive. -/
theorem isStrictlyPositive_coefficient_principal (a : ClassicalSymbol n H H m)
    (he : a.IsElliptic) {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    IsStrictlyPositive (a.principal.coefficient (x, ξ)) := by
  obtain ⟨e, he⟩ := isElliptic_iff.1 he x ξ hξ
  refine IsUnit.isStrictlyPositive ?_ (ContinuousLinearMap.nonneg_iff_isPositive.2
    (a.isPositive_coefficient_principal hU ha hx ξ))
  rw [← he]
  exact isUnit_iff_exists.2 ⟨e.symm, by ext; simp [ContinuousLinearMap.mul_def],
    by ext; simp [ContinuousLinearMap.mul_def]⟩

end Inner

end ClassicalSymbol

end TauCeti
