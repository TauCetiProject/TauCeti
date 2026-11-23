/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Decay
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# The weighted Fourier–Schur estimate for coefficients with position regularity

Let `p(x, ξ)` be a continuous coefficient on `ℝⁿ × ℝⁿ` with values in `V →L[ℂ] W` that vanishes
for positions `x` outside a compact set `K`, and let `Op(p) u (x) = ∫ exp(2πi ⟪ζ, x⟫) p(x, 2πζ)
(𝓕 u ζ) dζ` be its left quantization on Schwartz functions (`TauCeti.quantizeSchwartzValue`). This
file proves the Sobolev estimate

`‖Op(p) u‖_{H^{s - m}} ≤ C A ‖u‖_{H^s}`

on the Fourier side, under bounds `‖∂ₓ^α p(x, ξ)‖ ≤ A ⟨ξ⟩ ^ m` on the position derivatives of order
at most `N = ⌈|s - m|⌉₊ + n + 1` only
(`TauCeti.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_norm_iteratedFDeriv_le`). The
constant `C` depends on `n`, `m`, `s` and `K`, not on `p`. No derivative of `p` in the frequency
enters, and the position slices need only be `C^N`, so `p` need not be a symbol: for instance
`q(x, ξ) χ(y)` on `ℝ^k × ℝ^l`, for a symbol `q` of order `m ≥ 0` on `ℝ^k` vanishing for positions
`x` outside a compact set and a compactly supported smooth `χ`, vanishes for positions outside a
compact set and satisfies these bounds with the weight `⟨(ξ, η)⟩ ^ m`, while its frequency
derivatives of order larger than `m` do not decay in the frequency `η` of the second factor.
Estimates for such coefficients, linear in `A`, are what give operator-norm bounds `C ε` for
differences of quantizations whose position derivatives are `O(ε ⟨ξ⟩ ^ m)`.

## The argument

Taking the Fourier transform of `Op(p) u` in `x` gives
`𝓕 (Op(p) u) ξ = ∫ p̂(ξ - ζ, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.fourier_quantizeSchwartzValue`), where
`p̂(η, ξ)` is the Fourier transform of the position slice `x ↦ p(x, ξ)` at `η`. Integrating by parts
`N` times in the position gives the decay `(1 + ‖η‖) ^ N ‖p̂(η, ξ)‖ ≤ 2 ^ N A vol(K) ⟨ξ⟩ ^ m`
(`TauCeti.one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset`). Peetre's inequality
`⟨ξ⟩ ^ (s - m) ≤ 2 ^ (|s - m| / 2) ⟨ξ - ζ⟩ ^ |s - m| ⟨ζ⟩ ^ (s - m)` then bounds
`⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(p) u) ξ‖` by the integral of the convolution kernel
`k(ξ - ζ) = (1 + ‖ξ - ζ‖) ^ (|s - m| - N)`, which is integrable since `N > n + |s - m|`, against
`⟨ζ⟩ ^ s ‖𝓕 u ζ‖`. Schur's test (`TauCeti.eLpNorm_lintegral_mul_le`) bounds this in `L²` by
`‖k‖₁` times the `L²` norm of `⟨ζ⟩ ^ s 𝓕 u`, which is the `H^s` norm of `u`. The step from a
decay bound on `p̂` to the estimate is
`TauCeti.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay`; for symbols it gives
the Sobolev mapping theorem `TauCeti.Symbol.quantizeSobolev`.

## Main results

* `TauCeti.fourier_integral_fourierChar_smul_apply`: the Fourier transform of
  `x ↦ ∫ exp(2πi ⟪ζ, x⟫) p(x, g ζ) (𝓕 u ζ) dζ` is `ξ ↦ ∫ p̂(ξ - ζ, g ζ) (𝓕 u ζ) dζ`, for a
  continuous frequency map `g`.
* `TauCeti.fourier_quantizeSchwartzValue`: `𝓕 (Op(p) u) ξ = ∫ p̂(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`.
* `TauCeti.rpow_mul_norm_fourier_apply_le`: the pointwise kernel bound
  `⟨ξ⟩ ^ (s - m) ‖p̂(ξ - ζ, 2πζ) v‖ ≤ B k(ξ - ζ) ⟨ζ⟩ ^ s ‖v‖` from a decay bound on `p̂`.
* `TauCeti.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay`: the Sobolev estimate
  with a constant linear in a decay constant of `p̂`.
* `TauCeti.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_norm_iteratedFDeriv_le`: the
  Sobolev estimate with a constant linear in bounds on finitely many position derivatives of `p`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  Theorem 6.18 (Schur's test).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ENNReal SchwartzMap RealInnerProductSpace ContDiff

namespace TauCeti

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {p : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W} {K : Set (CoordinateSpace n)}

/-! ### The Fourier transform of the quantization -/

section Fourier

/-- The integrand of the double integral giving the Fourier transform of
`x ↦ ∫ exp(2πi ⟪ζ, x⟫) p(x, g ζ) (𝓕 u ζ) dζ` is integrable in the position and the frequency: it is
dominated by the indicator of `K` times the integrable function `C ⟨g ζ⟩ ^ m ‖𝓕 u ζ‖` of the
frequency. -/
private theorem integrable_fourierChar_smul_apply (hp : Continuous p) (hK : IsCompact K)
    {C : ℝ} (hC : ∀ x ∈ K, ∀ ξ, ‖p (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hKp : ∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) (u : 𝓢(CoordinateSpace n, V))
    {g : CoordinateSpace n → CoordinateSpace n} (hg : Continuous g)
    (hgu : Integrable fun ζ ↦ (1 + ‖g ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) (ξ : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪q.1, ξ - q.2⟫) • p (q.1, g q.2) (𝓕 u q.2)) (volume.prod volume) := by
  have hFcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪q.1, ξ - q.2⟫) • p (q.1, g q.2) (𝓕 u q.2) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((hp.comp (by fun_prop)).clm_apply ((𝓕 u).continuous.comp continuous_snd))
  have hK1 : Integrable (K.indicator fun _ ↦ (1 : ℝ)) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  refine (hK1.mul_prod (hgu.const_mul C)).mono' hFcont.aestronglyMeasurable
    (.of_forall fun q ↦ ?_)
  by_cases hx : q.1 ∈ K
  · rw [Set.indicator_of_mem hx, one_mul, Circle.norm_smul, ← mul_assoc]
    exact ((p _).le_opNorm _).trans (by gcongr; exact hC _ hx _)
  · rw [Set.indicator_of_notMem hx, zero_mul]
    simp [hKp q.1 hx]

/-- **The Fourier transform of a quantization integral.** For a continuous coefficient `p` that
vanishes at positions outside a compact set `K`, with `‖p(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` on `K`, and a
continuous frequency map `g` such that `⟨g ζ⟩ ^ m ‖𝓕 u ζ‖` is integrable, the Fourier transform of
`x ↦ ∫ exp(2πi ⟪ζ, x⟫) p(x, g ζ) (𝓕 u ζ) dζ` is `ξ ↦ ∫ p̂(ξ - ζ, g ζ) (𝓕 u ζ) dζ`, where
`p̂(η, ξ)` is the Fourier transform of the position slice `x ↦ p(x, ξ)` at `η`. For `g ζ = 2πζ`
this is the Fourier transform of the quantization (`TauCeti.fourier_quantizeSchwartzValue`). -/
theorem fourier_integral_fourierChar_smul_apply (hp : Continuous p) (hK : IsCompact K)
    {C : ℝ} (hC : ∀ x ∈ K, ∀ ξ, ‖p (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hKp : ∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) (u : 𝓢(CoordinateSpace n, V))
    {g : CoordinateSpace n → CoordinateSpace n} (hg : Continuous g)
    (hgu : Integrable fun ζ ↦ (1 + ‖g ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) (ξ : CoordinateSpace n) :
    𝓕 (fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • p (x, g ζ) (𝓕 u ζ)) ξ =
      ∫ ζ, 𝓕 (fun x ↦ p (x, g ζ)) (ξ - ζ) (𝓕 u ζ) := by
  set F : CoordinateSpace n × CoordinateSpace n → W := fun q ↦
    𝐞 (-⟪q.1, ξ - q.2⟫) • p (q.1, g q.2) (𝓕 u q.2) with hF
  have hFint : Integrable F (volume.prod volume) :=
    integrable_fourierChar_smul_apply hp hK hC hKp u hg hgu ξ
  calc 𝓕 (fun x ↦ ∫ ζ, 𝐞 ⟪ζ, x⟫ • p (x, g ζ) (𝓕 u ζ)) ξ = ∫ x, ∫ ζ, F (x, ζ) := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hF]
        rw [Circle.smul_def, ← integral_smul]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3
        rw [inner_sub_right, real_inner_comm ζ x]
        ring
    _ = ∫ ζ, ∫ x, F (x, ζ) := integral_integral_swap hFint
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        have hint : Integrable fun x ↦ 𝐞 (-⟪x, ξ - ζ⟫) • p (x, g ζ) :=
          ((Real.continuous_fourierChar.comp (by fun_prop)).smul
            (hp.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
              (HasCompactSupport.intro hK fun x hx ↦ by simp [hKp x hx, Circle.smul_def])
        dsimp only
        rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint]
        simp only [hF, Circle.smul_def, smul_apply]

/-- **The Fourier transform of the quantization.** For a continuous coefficient `p` that vanishes
at positions outside a compact set `K`, with `‖p(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` on `K`,
`𝓕 (Op(p) u) ξ = ∫ p̂(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`, where `p̂(η, ξ)` is the Fourier transform of the
position slice `x ↦ p(x, ξ)` at `η`. -/
theorem fourier_quantizeSchwartzValue (hp : Continuous p) (hK : IsCompact K)
    {C : ℝ} (hC : ∀ x ∈ K, ∀ ξ, ‖p (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hKp : ∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    𝓕 (quantizeSchwartzValue p u) ξ =
      ∫ ζ, 𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ) := by
  have hcont : Continuous fun ζ : CoordinateSpace n ↦
      (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ :=
    ((by fun_prop : Continuous fun ζ : CoordinateSpace n ↦ 1 + ‖(2 * π) • ζ‖ ^ 2).rpow_const
      fun _ ↦ Or.inl (by positivity)).mul (𝓕 u).continuous.norm
  have hgu : Integrable fun ζ : CoordinateSpace n ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ :=
    (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul ((2 * π) ^ |m|)).mono'
      hcont.aestronglyMeasurable (.of_forall fun ζ ↦ by
        rw [Real.norm_of_nonneg (by positivity), ← mul_assoc]
        gcongr
        exact one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m ζ)
  rw [funext (quantizeSchwartzValue_def p u)]
  exact fourier_integral_fourierChar_smul_apply hp hK hC hKp u (continuous_const_smul _) hgu ξ

end Fourier

/-! ### The Sobolev estimate -/

section Estimate

/-- A decay constant of `p̂` is nonnegative. -/
private theorem nonneg_of_decay {C₀ : ℝ} {N : ℕ}
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ p (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) : 0 ≤ C₀ :=
  (mul_nonneg_iff_of_pos_right (by positivity)).1
    ((mul_nonneg (by positivity) (norm_nonneg _)).trans (hdecay 0 0))

/-- **The pointwise kernel bound** behind the Sobolev estimate: Peetre's inequality and a decay
bound `(1 + ‖η‖) ^ N ‖p̂(η, ξ)‖ ≤ C₀ ⟨ξ⟩ ^ m` give
`⟨ξ⟩ ^ (s - m) ‖p̂(ξ - ζ, 2πζ) v‖ ≤ B k(ξ - ζ) ⟨ζ⟩ ^ s ‖v‖` with
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)` and `B = 2 ^ (|s - m| / 2) C₀ (2π) ^ |m|`. -/
theorem rpow_mul_norm_fourier_apply_le {s C₀ : ℝ} {N : ℕ}
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ p (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ξ ζ : CoordinateSpace n) (v : V) :
    (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
      2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|)) *
        ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) := by
  have hC₀ := nonneg_of_decay hdecay
  set A := 𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ)
  set t := 1 + ‖ξ - ζ‖
  have ht : 0 < t := by positivity
  have hA : ‖A‖ ≤ C₀ * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * (t ^ N)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]
    exact hdecay _ _
  have hscale := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m ζ
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub (s - m) ξ ζ
  -- The bracket `⟨η⟩ ^ |s - m|` is at most `(1 + ‖η‖) ^ |s - m|`.
  have hbr : (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) ≤ t ^ |s - m| :=
    one_add_norm_sq_rpow_le_one_add_norm_rpow _ (abs_nonneg _)
  have hk : t ^ |s - m| * (t ^ N)⁻¹ = t ^ (-((N : ℝ) - |s - m|)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    ring_nf
  have hw : (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2) = (1 + ‖ζ‖ ^ 2) ^ (s / 2) := by
    rw [← one_add_norm_sq_rpow_add, sub_add_cancel]
  calc (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖A v‖
      ≤ (2 ^ (|s - m| / 2) * (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by
        gcongr
        refine (A.le_opNorm v).trans ?_
        gcongr
        exact hA.trans (by gcongr)
    _ ≤ (2 ^ (|s - m| / 2) * t ^ |s - m| * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by gcongr
    _ = 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (t ^ |s - m| * (t ^ N)⁻¹) *
          (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * ‖v‖) := by ring
    _ = _ := by rw [hk, hw]

/-- The pointwise form of the Sobolev estimate: `⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(p) u) ξ‖` is bounded by the
integral of the kernel `B k(ξ - ζ)` of `rpow_mul_norm_fourier_apply_le` against
`⟨ζ⟩ ^ s ‖𝓕 u ζ‖`. -/
private theorem enorm_smul_fourier_quantizeSchwartzValue_le (hp : Continuous p) (hK : IsCompact K)
    {C : ℝ} (hC : ∀ x ∈ K, ∀ ξ, ‖p (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hKp : ∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) {s C₀ : ℝ} {N : ℕ}
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ p (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) • 𝓕 (quantizeSchwartzValue p u) ξ‖ₑ ≤
      ∫⁻ ζ, ENNReal.ofReal (2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| *
          (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|))) *
        ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ := by
  have hC₀ := nonneg_of_decay hdecay
  rw [fourier_quantizeSchwartzValue hp hK hC hKp, eNorm_smul]
  calc ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ‖∫ ζ, 𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ
      ≤ ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ∫⁻ ζ, ‖𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ := by
        gcongr
        exact eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ ζ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) *
          ‖𝓕 (fun x ↦ p (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖) := by
        rw [← lintegral_const_mul' _ _ eNorm_ne_top]
        refine lintegral_congr fun ζ ↦ ?_
        rw [ENNReal.ofReal_mul (by positivity), ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := by
        refine lintegral_mono fun ζ ↦ ?_
        rw [eNorm_smul, ← ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (rpow_mul_norm_fourier_apply_le hdecay ξ ζ (𝓕 u ζ))

/-- **The Sobolev estimate from the decay of `p̂`.** For every real `s` there is a constant `C`
such that every continuous coefficient `p` vanishing at positions outside a compact set, with a
growth bound `‖p(x, ξ)‖ ≤ C' ⟨ξ⟩ ^ m` there, whose position Fourier transform satisfies
`(1 + ‖η‖) ^ N ‖p̂(η, ξ)‖ ≤ C₀ ⟨ξ⟩ ^ m` with `N = ⌈|s - m|⌉₊ + n + 1`, has
`‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(p) u)‖_{L²} ≤ C C₀ ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}` for every Schwartz function `u`,
that is, `‖Op(p) u‖_{H^{s-m}} ≤ C C₀ ‖u‖_{H^s}`. The constant `C` depends only on `n`, `m` and
`s`. -/
theorem exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay (n : ℕ) (m s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (p : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W)
      (K : Set (CoordinateSpace n)) (C' C₀ : ℝ), Continuous p → IsCompact K →
      (∀ x ∈ K, ∀ ξ, ‖p (x, ξ)‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) →
      (∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) →
      (∀ η ξ : CoordinateSpace n, (1 + ‖η‖) ^ (⌈|s - m|⌉₊ + n + 1) *
        ‖𝓕 (fun x ↦ p (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) →
      ∀ u : 𝓢(CoordinateSpace n, V),
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
            𝓕 (quantizeSchwartzValue p u) ξ) 2 volume ≤
          ENNReal.ofReal (C * C₀) *
            eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  set N : ℕ := ⌈|s - m|⌉₊ + n + 1
  set k : CoordinateSpace n → ℝ := fun η ↦ (1 + ‖η‖) ^ (-((N : ℝ) - |s - m|))
  have hk_int : Integrable k := integrable_one_add_norm (by
    have := Nat.le_ceil |s - m|
    push_cast [N, finrank_euclideanSpace_fin]
    linarith)
  have hkcont : Continuous k :=
    (continuous_const.add continuous_norm).rpow_const fun x ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)).ne'
  refine ⟨2 ^ (|s - m| / 2) * (2 * π) ^ |m| * ∫ η, k η,
    mul_nonneg (by positivity) (integral_nonneg fun η ↦ by positivity),
    fun p K C' C₀ hp hK hC hKp hdecay u ↦ ?_⟩
  have hC₀ := nonneg_of_decay hdecay
  set B := 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m|
  set A := ENNReal.ofReal (∫ η, B * k η)
  have hA : 2 ^ (|s - m| / 2) * (2 * π) ^ |m| * (∫ η, k η) * C₀ = ∫ η, B * k η := by
    rw [integral_const_mul]
    simp only [B]
    ring
  rw [hA]
  -- The pointwise bound by the kernel `B k(ξ - ζ)` acting on `⟨ζ⟩ ^ s ‖𝓕 u ζ‖`.
  have hpt := enorm_smul_fourier_quantizeSchwartzValue_le (s := s) hp hK hC hKp hdecay u
  -- Schur's test for the kernel `B k(ξ - ζ)`, whose row and column integrals are `A`.
  have hk : Integrable fun η ↦ B * k η := hk_int.const_mul B
  have hk0 : 0 ≤ᵐ[volume] fun η ↦ B * k η := .of_forall fun _ ↦ by positivity
  have hkmeas : AEMeasurable (Function.uncurry fun x y : CoordinateSpace n ↦
      ENNReal.ofReal (B * k (x - y))) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (hkcont.comp (continuous_fst.sub continuous_snd)))).measurable.aemeasurable
  have hw (r : ℝ) : Continuous fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) :=
    (by fun_prop : (fun x : CoordinateSpace n ↦
      (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth).1.continuous
  have hgmeas : AEStronglyMeasurable
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ) :=
    ((hw s).smul (𝓕 u).continuous).aestronglyMeasurable
  have hschur := TauCeti.eLpNorm_lintegral_mul_le hkmeas hgmeas.eNorm
    (p := 2) one_le_two (A := A) (B := A)
    (.of_forall fun ξ ↦ (lintegral_ofReal_sub_left_eq_ofReal_integral hk hk0 ξ).le)
    (.of_forall fun ζ ↦ (lintegral_ofReal_sub_right_eq_ofReal_integral hk hk0 ζ).le)
  calc _ ≤ eLpNorm (fun ξ ↦ ∫⁻ ζ, ENNReal.ofReal (B * k (ξ - ζ)) *
          ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ) 2 volume :=
        eLpNorm_mono_eNorm ((hw (s - m)).smul
          (integrable_quantizeSchwartzValue hp hK hC hKp u).continuous_fourier).aestronglyMeasurable
          fun ξ ↦ by rw [eNorm_eq_self]; exact hpt ξ
    _ ≤ _ := hschur
    _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), eLpNorm_eNorm _ hgmeas,
          sub_add_cancel, ENNReal.rpow_one]

/-- **The weighted Fourier–Schur estimate.** Let `K` be compact, `m` and `s` real and
`N = ⌈|s - m|⌉₊ + n + 1`. There is a constant `C`, depending only on `n`, `m`, `s` and `K`, such
that every continuous coefficient `p` vanishing at positions outside `K`, whose position slices
`x ↦ p(x, ξ)` are `C^N` with `‖∂ₓ^l p(x, ξ)‖ ≤ A ⟨ξ⟩ ^ m` for `l ≤ N` and `x ∈ K`, satisfies
`‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(p) u)‖_{L²} ≤ C A ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}` for every Schwartz function `u`,
that is, `‖Op(p) u‖_{H^{s-m}} ≤ C A ‖u‖_{H^s}`. No derivative of `p` in the frequency is
assumed. -/
theorem exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_norm_iteratedFDeriv_le
    (hK : IsCompact K) (m s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (p : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W) (A : ℝ),
      Continuous p → (∀ ξ, ContDiff ℝ (⌈|s - m|⌉₊ + n + 1 : ℕ) fun x ↦ p (x, ξ)) →
      (∀ x ∉ K, ∀ ξ, p (x, ξ) = 0) →
      (∀ l ≤ ⌈|s - m|⌉₊ + n + 1, ∀ x ∈ K, ∀ ξ,
        ‖iteratedFDeriv ℝ l (fun y ↦ p (y, ξ)) x‖ ≤ A * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) →
      ∀ u : 𝓢(CoordinateSpace n, V),
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
            𝓕 (quantizeSchwartzValue p u) ξ) 2 volume ≤
          ENNReal.ofReal (C * A) *
            eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  set N : ℕ := ⌈|s - m|⌉₊ + n + 1
  obtain ⟨C, hC0, hC⟩ := exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay
    (V := V) (W := W) n m s
  refine ⟨C * 2 ^ N * volume.real K, by positivity, fun p A hp hsmooth hKp hA u ↦ ?_⟩
  -- For nonempty `K`, the bound at a point `x₀ ∈ K` gives `0 ≤ A`, which the bound on the
  -- derivatives off `K` needs.
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · -- For empty `K` the coefficient vanishes, and so does its quantization.
    have h0 : quantizeSchwartzValue p u = 0 := funext fun x ↦ by
      simp [quantizeSchwartzValue_def, hKp x (Set.notMem_empty x)]
    simp [h0, Real.fourier_eq]
  have hA0 : 0 ≤ A := (mul_nonneg_iff_of_pos_right (by positivity)).1
    ((norm_nonneg _).trans (hA 0 (Nat.zero_le _) x₀ hx₀ 0))
  -- The slices vanish outside `K`, so their derivatives vanish there and `tsupport ⊆ K`.
  have hts (ξ : CoordinateSpace n) : tsupport (fun x ↦ p (x, ξ)) ⊆ K :=
    closure_minimal (fun x hx ↦ by_contra fun h ↦ hx (hKp x h ξ)) hK.isClosed
  have hA' (ξ : CoordinateSpace n) (l : ℕ) (hl : l ≤ N) (x : CoordinateSpace n) :
      ‖iteratedFDeriv ℝ l (fun y ↦ p (y, ξ)) x‖ ≤ A * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    by_cases hx : x ∈ K
    · exact hA l hl x hx ξ
    · rw [Function.notMem_support.mp fun h ↦ hx (hts ξ (support_iteratedFDeriv_subset l h)),
        norm_zero]
      exact mul_nonneg hA0 (by positivity)
  -- Integration by parts `N` times in the position gives the decay of `p̂`.
  have hdecay (η ξ : CoordinateSpace n) : (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ p (x, ξ)) η‖ ≤
      2 ^ N * A * volume.real K * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    (one_add_norm_pow_mul_norm_fourier_le_of_tsupport_subset (hsmooth ξ) hK.measure_lt_top.ne
      (hts ξ) (hA' ξ) η).trans_eq (by ring)
  have hbound (x : CoordinateSpace n) (hx : x ∈ K) (ξ : CoordinateSpace n) :
      ‖p (x, ξ)‖ ≤ A * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
    simpa using hA 0 (Nat.zero_le _) x hx ξ
  refine (hC p K A _ hp hK hbound hKp hdecay u).trans_eq ?_
  congr 2
  ring

end Estimate

end TauCeti
