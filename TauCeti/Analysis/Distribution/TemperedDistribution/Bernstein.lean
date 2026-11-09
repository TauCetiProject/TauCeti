/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.MeasureTheory.Function.Lp.Dilation

/-!
# Bernstein's inequalities

Let `E` be a finite-dimensional real inner product space of dimension `n`, and let `f ∈ Lᵖ(E)`
have its Fourier transform supported in the closed ball of radius `R`, in the sense that the
tempered distribution `𝓕 f` vanishes on the complement of that ball
(`Distribution.IsVanishingOn`). **Bernstein's inequality** says that for `1 ≤ p ≤ q ≤ ∞` and
directions `m₀, …, m_{k-1}`, the derivative `∂^{m} f = ∂_{m₀} ⋯ ∂_{m_{k-1}} f` lies in `L^q` with

`‖∂^{m} f‖_q ≤ C R ^ (k + n (1/p - 1/q)) ‖f‖_p`,

where `C` depends on `p`, `q` and the directions `m`, but not on `R` or `f`
(`TemperedDistribution.exists_iteratedLineDerivOp_eq_and_norm_le`). For `k = 0` it says that a
band-limited `Lᵖ` function lies in every `L^q`, `q ≥ p`, with
`‖f‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p`
(`TemperedDistribution.exists_toTemperedDistribution_eq_and_norm_le`). These are the estimates on
the Littlewood–Paley blocks of a function on which Besov spaces, paraproducts and Strichartz
estimates rest.

The exponent of `R` is forced by scaling. Fix a smooth cutoff `χ` equal to `1` on the ball of
radius `2`. On functions whose Fourier transform lives in the ball of radius `R`, the derivative
`∂^{m}` agrees with the Fourier multiplier whose symbol is the compactly supported smooth function

`σ_R(ξ) = ∏ᵢ 2πi ⟪ξ, mᵢ⟫ · χ(ξ / R)`

(`TemperedDistribution.iteratedLineDerivOp_eq_fourierMultiplierCLM` and
`TemperedDistribution.fourierMultiplierCLM_eq_self_of_isVanishingOn`). Since
`σ_R(ξ) = R ^ k σ_1(ξ / R)`, its kernel is `𝓕⁻ σ_R (x) = R ^ (k + n) 𝓕⁻ σ_1 (R x)`, whose `Lʳ`
norm is `R ^ (k + n (1 - 1/r))` times that of `𝓕⁻ σ_1`. Young's inequality with
`1/p + 1/r = 1 + 1/q`
(`TemperedDistribution.exists_fourierMultiplierCLM_eq_and_norm_le_of_inv_add_inv_eq`) bounds the
multiplier from `Lᵖ` to `L^q` by this norm, and `1 - 1/r = 1/p - 1/q`.

The reverse inequality for functions whose Fourier transform lives in an annulus,
`‖f‖_p ≤ C R ^ (-k) max_{|α| = k} ‖∂^α f‖_p`, is not proved here.

## Main declarations

* `TemperedDistribution.exists_iteratedLineDerivOp_eq_and_norm_le`: Bernstein's inequality for
  derivatives.
* `TemperedDistribution.exists_toTemperedDistribution_eq_and_norm_le`: the case of no
  derivatives, the `Lᵖ → L^q` improvement for band-limited functions.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Lemma 2.1.
-/

public section

noncomputable section

namespace TemperedDistribution

open MeasureTheory Module LineDeriv Real Metric
open scoped ENNReal SchwartzMap FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

variable (E) in
/-- The cutoff `χ`, equal to `1` on the closed ball of radius `2` and supported in the ball of
radius `3`. -/
private def bernsteinCutoff : ContDiffBump (0 : E) := ⟨2, 3, two_pos, by norm_num⟩

/-- The cutoff `χ (R⁻¹ •)` at radius `R ≠ 0`, as a Schwartz function. -/
private def cutoffAt {R : ℝ} (hR : R ≠ 0) : 𝓢(E, ℂ) :=
  (((bernsteinCutoff E).hasCompactSupport.comp_smul (inv_ne_zero hR)).comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp ((bernsteinCutoff E).contDiff.comp (contDiff_const_smul _)))

omit [MeasurableSpace E] [BorelSpace E] in
private theorem cutoffAt_apply {R : ℝ} (hR : R ≠ 0) (ξ : E) :
    cutoffAt hR ξ = (bernsteinCutoff E (R⁻¹ • ξ) : ℂ) :=
  HasCompactSupport.toSchwartzMap_toFun _ _ ξ

omit [MeasurableSpace E] [BorelSpace E] in
/-- Off the closed ball of radius `R > 0` lies everything where `χ (R⁻¹ •)` differs from `1`. -/
private theorem tsupport_one_sub_cutoffAt_subset {R : ℝ} (hR : 0 < R) :
    tsupport (1 - ⇑(cutoffAt (E := E) hR.ne')) ⊆ (closedBall 0 R)ᶜ := by
  have hsupp : Function.support (1 - ⇑(cutoffAt (E := E) hR.ne')) ⊆ {ξ | 2 * R ≤ ‖ξ‖} := by
    intro ξ hξ
    by_contra hlt
    refine hξ ?_
    have hmem : R⁻¹ • ξ ∈ closedBall (0 : E) (bernsteinCutoff E).rIn := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le,
        inv_mul_le_iff₀ hR]
      exact (not_le.1 hlt).le.trans_eq (by simp [bernsteinCutoff, mul_comm])
    simp [cutoffAt_apply, (bernsteinCutoff E).one_of_mem_closedBall hmem]
  refine (closure_minimal hsupp (isClosed_le continuous_const continuous_norm)).trans ?_
  intro ξ hξ hball
  rw [mem_closedBall_zero_iff] at hball
  have hξ' : 2 * R ≤ ‖ξ‖ := hξ
  linarith

/-- The polynomial symbol `ξ ↦ ∏ᵢ 2πi ⟪ξ, mᵢ⟫` of `∂^{m}`. -/
private def derivSymbol {k : ℕ} (m : Fin k → E) (ξ : E) : ℂ :=
  ∏ i, 2 * π * Complex.I * (inner ℝ ξ (m i) : ℂ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem hasTemperateGrowth_derivSymbol {k : ℕ} (m : Fin k → E) :
    (derivSymbol m).HasTemperateGrowth :=
  Function.HasTemperateGrowth.prod fun i _ ↦ by fun_prop

/-- The symbol `σ_R = ∏ᵢ 2πi ⟪·, mᵢ⟫ · χ (R⁻¹ •)` of `∂^{m}` cut off at frequency radius `2R`,
as a Schwartz function. -/
private def symbol {k : ℕ} (m : Fin k → E) {R : ℝ} (hR : R ≠ 0) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (derivSymbol m) (cutoffAt hR)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem symbol_apply {k : ℕ} (m : Fin k → E) {R : ℝ} (hR : R ≠ 0) (ξ : E) :
    symbol m hR ξ = derivSymbol m ξ * (bernsteinCutoff E (R⁻¹ • ξ) : ℂ) := by
  rw [symbol, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_derivSymbol m),
    cutoffAt_apply, smul_eq_mul]

omit [CompleteSpace F] in
/-- On a tempered distribution whose Fourier transform vanishes off the closed ball of radius
`R > 0`, the derivative `∂^{m}` is the multiplier with the Schwartz symbol `σ_R`. -/
private theorem iteratedLineDerivOp_eq_fourierMultiplierCLM_symbol {k : ℕ} (m : Fin k → E)
    {R : ℝ} (hR : 0 < R) {u : 𝓢'(E, F)}
    (hu : Distribution.IsVanishingOn ⇑(𝓕 u : 𝓢'(E, F)) (closedBall 0 R)ᶜ) :
    ∂^{m} u = fourierMultiplierCLM F (symbol m hR.ne') u := by
  have hχ := (cutoffAt (E := E) hR.ne').hasTemperateGrowth
  calc ∂^{m} u = fourierMultiplierCLM F (derivSymbol m) u :=
        iteratedLineDerivOp_eq_fourierMultiplierCLM m u
    _ = fourierMultiplierCLM F (derivSymbol m)
          (fourierMultiplierCLM F (cutoffAt hR.ne') u) := by
        rw [fourierMultiplierCLM_eq_self_of_isVanishingOn hχ hu
          (tsupport_one_sub_cutoffAt_subset hR)]
    _ = fourierMultiplierCLM F (symbol m hR.ne') u := by
        have h : ⇑(cutoffAt hR.ne') * derivSymbol m = ⇑(symbol m hR.ne') := by
          funext ξ
          rw [Pi.mul_apply, symbol_apply, cutoffAt_apply, mul_comm]
        rw [fourierMultiplierCLM_fourierMultiplierCLM_apply hχ
          (hasTemperateGrowth_derivSymbol m), h]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The symbol at radius `R` is the dilate of the symbol at radius `1`:
`σ_R(ξ) = R ^ k σ_1(R⁻¹ ξ)`. -/
private theorem symbol_apply_eq {k : ℕ} (m : Fin k → E) {R : ℝ} (hR : R ≠ 0) (ξ : E) :
    symbol m hR ξ = ((R : ℂ) ^ k • symbol m one_ne_zero) (R⁻¹ • ξ) := by
  have h (i : Fin k) : 2 * π * Complex.I * (inner ℝ (R⁻¹ • ξ) (m i) : ℂ) =
      (R : ℂ)⁻¹ * (2 * π * Complex.I * (inner ℝ ξ (m i) : ℂ)) := by
    rw [real_inner_smul_left]
    push_cast
    ring
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR
  simp only [smul_apply, symbol_apply, derivSymbol, inv_one, one_smul, h,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [inv_pow]
  field_simp

/-- **Scaling of the kernel.** For `R > 0`, the `Lʳ` norm of the kernel `𝓕⁻ σ_R` is
`R ^ (k + n - n/r)` times that of `𝓕⁻ σ_1`. -/
private theorem toReal_eLpNorm_fourierInv_symbol {k : ℕ} (m : Fin k → E) {R : ℝ} (hR : 0 < R)
    (r : ℝ≥0∞) :
    (eLpNorm (𝓕⁻ ⇑(symbol m hR.ne')) r volume).toReal =
      R ^ (k + finrank ℝ E - finrank ℝ E * r.toReal⁻¹ : ℝ) *
        (eLpNorm (𝓕⁻ ⇑(symbol m (one_ne_zero (α := ℝ)))) r volume).toReal := by
  set σ : 𝓢(E, ℂ) := (R : ℂ) ^ k • symbol m one_ne_zero
  have hK : 𝓕⁻ ⇑(symbol m hR.ne') =
      |(R⁻¹ ^ finrank ℝ E)|⁻¹ • fun y ↦ 𝓕⁻ ⇑σ (R⁻¹⁻¹ • y) := by
    funext y
    have hσ : ⇑(symbol m hR.ne') = fun ξ ↦ σ (R⁻¹ • ξ) := funext (symbol_apply_eq m hR.ne')
    rw [hσ, TauCeti.fourierInv_comp_smul (⇑σ) (inv_ne_zero hR.ne'), Pi.smul_apply]
  have hσK : 𝓕⁻ ⇑σ = (R : ℂ) ^ k • 𝓕⁻ ⇑(symbol m (one_ne_zero (α := ℝ))) := by
    rw [← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourierInv_coe,
      FourierInvSMul.fourierInv_smul]
    rfl
  rw [hK, eLpNorm_const_smul, Measure.eLpNorm_comp_inv_smul volume _ (inv_ne_zero hR.ne'), hσK,
    eLpNorm_const_smul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), toReal_enorm, toReal_enorm, ← mul_assoc, ← mul_assoc]
  congr 1
  set n := finrank ℝ E
  have h1 : ‖|R⁻¹ ^ n|⁻¹‖ = R ^ (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_inv, abs_abs, abs_of_pos (by positivity), inv_pow, inv_inv,
      Real.rpow_natCast]
  have h2 : |R⁻¹| ^ ((n : ℝ) / r.toReal) = R ^ (-(n * r.toReal⁻¹)) := by
    rw [abs_of_pos (inv_pos.2 hR), Real.inv_rpow hR.le, ← Real.rpow_neg hR.le, div_eq_mul_inv]
  have h3 : ‖(R : ℂ) ^ k‖ = R ^ (k : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le, Real.rpow_natCast]
  rw [h1, h2, h3, ← Real.rpow_add hR, ← Real.rpow_add hR]
  congr 1
  ring

/-- **Bernstein's inequality.** Let `1 ≤ p ≤ q ≤ ∞` and let `m₀, …, m_{k-1}` be directions in `E`,
a space of dimension `n`. There is a constant `C` such that for every `R > 0` and every `f ∈ Lᵖ`
whose Fourier transform vanishes off the closed ball of radius `R`, the derivative
`∂^{m} f = ∂_{m₀} ⋯ ∂_{m_{k-1}} f` is a function `g ∈ L^q` with
`‖g‖_q ≤ C R ^ (k + n (1/p - 1/q)) ‖f‖_p`. -/
theorem exists_iteratedLineDerivOp_eq_and_norm_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) {k : ℕ} (m : Fin k → E) :
    ∃ C : ℝ, ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      Distribution.IsVanishingOn ⇑(𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), ∂^{m} (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ (k + finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖f‖ := by
  have hp : 1 ≤ p := Fact.out
  have hq : 1 ≤ q := Fact.out
  -- The exponent `r` of Young's inequality, with `1/r = 1 + 1/q - 1/p`.
  set r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hp_le : p⁻¹ ≤ 1 + q⁻¹ := (ENNReal.inv_le_one.2 hp).trans le_self_add
  have hpqr : p⁻¹ + r⁻¹ = 1 + q⁻¹ := by rw [inv_inv, add_tsub_cancel_of_le hp_le]
  have hr : 1 ≤ r := by
    refine ENNReal.one_le_inv.2 (tsub_le_iff_right.2 ?_)
    gcongr
  clear_value r
  have hreal : r.toReal⁻¹ = 1 + q.toReal⁻¹ - p.toReal⁻¹ := by
    have h := congrArg ENNReal.toReal hpqr
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp).ne')
        (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hr).ne'),
      ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hq).ne'),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at h
    linarith
  refine ⟨(eLpNorm (𝓕⁻ ⇑(symbol m (one_ne_zero (α := ℝ)))) r volume).toReal,
    fun {R} hR f hf ↦ ?_⟩
  obtain ⟨g, hg, hgf⟩ :=
    exists_fourierMultiplierCLM_eq_and_norm_le_of_inv_add_inv_eq hr hpqr (symbol m hR.ne') f
  refine ⟨g, (iteratedLineDerivOp_eq_fourierMultiplierCLM_symbol m hR hf).trans hg,
    hgf.trans_eq ?_⟩
  rw [toReal_eLpNorm_fourierInv_symbol m hR, hreal, mul_comm (R ^ _)]
  congr 3
  ring

/-- **Bernstein's inequality without derivatives.** Let `1 ≤ p ≤ q ≤ ∞` and let `E` have dimension
`n`. There is a constant `C` such that for every `R > 0`, every `f ∈ Lᵖ` whose Fourier transform
vanishes off the closed ball of radius `R` lies in `L^q`, with
`‖f‖_q ≤ C R ^ (n (1/p - 1/q)) ‖f‖_p`. -/
theorem exists_toTemperedDistribution_eq_and_norm_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) :
    ∃ C : ℝ, ∀ {R : ℝ}, 0 < R → ∀ f : Lp F p (volume : Measure E),
      Distribution.IsVanishingOn ⇑(𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 R)ᶜ →
      ∃ g : Lp F q (volume : Measure E), (f : 𝓢'(E, F)) = g ∧
        ‖g‖ ≤ C * R ^ (finrank ℝ E * (p.toReal⁻¹ - q.toReal⁻¹)) * ‖f‖ := by
  obtain ⟨C, hC⟩ :=
    exists_iteratedLineDerivOp_eq_and_norm_le (F := F) hpq (Fin.elim0 : Fin 0 → E)
  exact ⟨C, fun hR f hf ↦ by simpa using hC hR f hf⟩

end TemperedDistribution
