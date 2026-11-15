/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import TauCeti.Analysis.Calculus.CoordinateDeriv.ParametricIntegral
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convolution

/-!
# Cutting off the kernel of a pseudodifferential operator near the diagonal

Let `b` be a symbol of order `m` on `ℝⁿ`, whose quantization `Op(b)` has the distribution kernel
`K_b(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) b(x, ξ) dξ`. The support of `K_b` can be all of
`ℝⁿ × ℝⁿ`: then `Op(b)` does not preserve compact supports, and its output near `x` depends on the
input far from `x`. Multiplying the kernel by `χ(x - y)`, for a Schwartz function `χ`, gives the
operator `u ↦ Op(b)(χ(x - ·) u)(x)`. This file shows that it is again a quantization: of the
symbol of order `m`

`c(x, ξ) = ∫ 𝓕χ(θ) b(x, ξ - 2πθ) dθ`

(`TauCeti.Symbol.kernelCutoff χ b`), the convolution of the frequency slice of `b` with the Fourier
transform of `χ`. When `χ` has compact support, the kernel `χ(x - y) K_b(x, y)` of `Op(c)` vanishes
unless `x - y` lies in the support of `χ`: the operator `Op(c)` is properly supported. When `χ`
equals `1` near the origin, `c` differs from `b` by a smoothing symbol: the part of the kernel
removed, `(1 - χ(x - y)) K_b(x, y)`, vanishes near the diagonal, where all the singularity of
`K_b` lies.

So every pseudodifferential operator is a properly supported one, with kernel supported in any
prescribed neighbourhood of the diagonal, up to an operator with a smoothing symbol
(`TauCeti.Symbol.exists_isSmoothing_sub_and_quantizeSchwartzValue_eq_zero`). Properly supported
operators preserve compact supports, so they can be composed when the symbols have no compact
spatial support, and they are the pieces that are patched together on manifolds.

## Main declarations

* `TauCeti.Symbol.kernelCutoff χ b`: the symbol `c` above, with its derivatives
  `TauCeti.Symbol.spatialDeriv_kernelCutoff` and `TauCeti.Symbol.frequencyDeriv_kernelCutoff`;
  it keeps compact spatial support (`TauCeti.Symbol.HasCompactSpatialSupport.kernelCutoff`).
* `TauCeti.Symbol.quantizeSchwartzValue_kernelCutoff`: `Op(c) u (x) = Op(b)(χ(x - ·) u)(x)`.
* `TauCeti.Symbol.quantizeSchwartzValue_kernelCutoff_congr`: `Op(c) u (x)` only depends on `u`
  on the set of `y` with `χ(x - y) ≠ 0`.
* `TauCeti.Symbol.support_quantizeSchwartzValue_kernelCutoff_subset` and
  `TauCeti.Symbol.hasCompactSupport_quantizeSchwartzValue_kernelCutoff`: the support of
  `Op(c) u` lies in the sum of the supports of `u` and `χ`, so for compactly supported `χ` the
  operator `Op(c)` preserves compact supports.
* `TauCeti.Symbol.isSmoothing_kernelCutoff_sub`: if `χ = 1` near `0`, then `c - b` is smoothing.
* `TauCeti.Symbol.exists_isSmoothing_sub_and_quantizeSchwartzValue_eq_zero`: for every `ε > 0`,
  every symbol is, up to a smoothing symbol, a symbol `c` such that `Op(c) u (x) = 0` whenever `u`
  vanishes on the ball of radius `ε` about `x`.

## Proof outline

Peetre's inequality `⟨ξ - 2πθ⟩^m ≤ C ⟨ξ⟩^m ⟨θ⟩^|m|` and the rapid decay of `𝓕χ` bound the
integrand of `c` by an integrable function of `θ` times `⟨ξ⟩^m`, locally uniformly in `x`.
Differentiating under the integral sign, the derivatives of `c` in `x_j` and `ξ_j` are the
symbols built from `∂_{x_j} b` and `∂_{ξ_j} b`, which gives smoothness and the symbol estimates.

The quantization formula follows from the convolution formula for `𝓕(χ(x - ·) u)`, one use of
Fubini's theorem and a change of frequency.

For the smoothing statement, interpolate by `c_s(x, ξ) = ∫ 𝓕χ(θ) b(x, ξ - sθ) dθ`, `s ∈ [0, 2π]`.
By Fourier inversion `c_0 = χ(0) b`, and differentiating in `s`, using
`θⱼ 𝓕χ(θ) = (2πi)⁻¹ 𝓕(∂ⱼχ)(θ)`, the derivative of `c_s` is `-(2πi)⁻¹ ∑ⱼ` of the same
construction for `∂ⱼχ` and `∂_{ξ_j} b`, a symbol of order `m - 1`. If `χ` is constant near `0`,
then every `∂ⱼχ` vanishes near `0`, so it is again constant near `0`, with value `0` there. By
induction and the mean value inequality, `c_s - χ(0) b` has order `m - N` for every `N`, uniformly
in `s ∈ [0, 2π]`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Filter
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology Pointwise LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### The integrand -/

section Integrand

variable (χ : 𝓢(CoordinateSpace n, ℂ))

/-- The integrand `𝓕χ(θ) b(x, ξ - sθ)` of the kernel cutoff of `b`, with the frequency shift `2πθ`
scaled to `sθ`. The kernel cutoff is the case `s = 2π`; the cases `s ∈ [0, 2π]` interpolate between
`χ(0) b` and the kernel cutoff. -/
private def cutoffIntegrand (b : Symbol n V W m) (s : ℝ)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) : V →L[ℂ] W :=
  𝓕 χ θ • b.coefficient (p.1, p.2 - s • θ)

/-- The integrable function `⟨Rθ⟩ ^ |m| ‖𝓕χ(θ)‖` dominating the integrand. -/
private def cutoffWeight (m R : ℝ) (θ : CoordinateSpace n) : ℝ :=
  (1 + ‖R • θ‖ ^ 2) ^ (|m| / 2) * ‖𝓕 χ θ‖

private theorem integrable_cutoffWeight (m R : ℝ) : Integrable (cutoffWeight χ m R) :=
  (𝓕 χ).integrable_one_add_norm_smul_sq_rpow_mul_norm R |m|

private theorem continuous_cutoffIntegrand (b : Symbol n V W m) (s : ℝ)
    (p : CoordinateSpace n × CoordinateSpace n) : Continuous (cutoffIntegrand χ b s p) :=
  (𝓕 χ).continuous.smul (b.contDiff_coefficient.continuous.comp (by fun_prop))

/-- Peetre's inequality bounds the integrand by `C ⟨ξ⟩ ^ m ⟨Rθ⟩ ^ |m| ‖𝓕χ(θ)‖`, uniformly for
scales `|s| ≤ R` and positions in a compact set. -/
private theorem exists_norm_cutoffIntegrand_le (b : Symbol n V W m) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ∈ K, ∀ ξ θ, ‖cutoffIntegrand χ b s (x, ξ) θ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * cutoffWeight χ m R θ := by
  obtain ⟨C, hC0, hC⟩ := b.exists_bound_coefficient K hK
  refine ⟨C * 2 ^ (|m| / 2), by positivity, fun s hs x hx ξ θ ↦ ?_⟩
  have hsθ : ‖-(s • θ)‖ ≤ ‖R • θ‖ := by
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg
      ((abs_nonneg s).trans hs)]
    gcongr
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ξ (-(s • θ))
  rw [← sub_eq_add_neg] at hpeetre
  rw [cutoffIntegrand, norm_smul, cutoffWeight]
  calc ‖𝓕 χ θ‖ * ‖b.coefficient (x, ξ - s • θ)‖
      ≤ ‖𝓕 χ θ‖ * (C * (2 ^ (|m| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          (1 + ‖R • θ‖ ^ 2) ^ (|m| / 2))) := by
        gcongr
        exact (hC x hx _).trans (by gcongr; exact hpeetre.trans (by gcongr))
    _ = _ := by ring

private theorem integrable_cutoffIntegrand (b : Symbol n V W m) (s : ℝ)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (cutoffIntegrand χ b s p) := by
  obtain ⟨C, -, hC⟩ := exists_norm_cutoffIntegrand_le χ b (isCompact_singleton (x := p.1)) |s|
  exact ((integrable_cutoffWeight χ m |s|).const_mul (C * (1 + ‖p.2‖ ^ 2) ^ (m / 2))).mono'
    (continuous_cutoffIntegrand χ b s p).aestronglyMeasurable
    (.of_forall fun θ ↦ by simpa [mul_assoc] using hC s le_rfl p.1 rfl p.2 θ)

private theorem differentiableAt_cutoffIntegrand (b : Symbol n V W m) (s : ℝ)
    (θ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ cutoffIntegrand χ b s p θ) p := by
  unfold cutoffIntegrand
  exact ((b.contDiff_coefficient.differentiable (by simp) _).comp p
    (by fun_prop : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (p.1, p.2 - s • θ)) p)).const_smul (𝓕 χ θ)

/-- The derivative of the integrand in the position `x_j` is the integrand of `∂_{x_j} b`. -/
private theorem coordinateDeriv_fst_cutoffIntegrand (b : Symbol n V W m) (s : ℝ) (j : Fin n)
    (θ x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ cutoffIntegrand χ b s (x, ξ) θ) x =
      cutoffIntegrand χ (spatialDeriv j b) s (x, ξ) θ := by
  have h : (fun x ↦ cutoffIntegrand χ b s (x, ξ) θ) =
      𝓕 χ θ • fun x ↦ b.coefficient (x, ξ - s • θ) := rfl
  rw [h, coordinateDeriv_const_smul, Pi.smul_apply, cutoffIntegrand, coefficient_spatialDeriv]

/-- The derivative of the integrand in the frequency `ξ_j` is the integrand of `∂_{ξ_j} b`. -/
private theorem coordinateDeriv_snd_cutoffIntegrand (b : Symbol n V W m) (s : ℝ) (j : Fin n)
    (θ x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ cutoffIntegrand χ b s (x, ξ) θ) ξ =
      cutoffIntegrand χ (frequencyDeriv j b) s (x, ξ) θ := by
  have h : (fun ξ ↦ cutoffIntegrand χ b s (x, ξ) θ) =
      𝓕 χ θ • fun ξ ↦ b.coefficient (x, ξ - s • θ) := rfl
  rw [h, coordinateDeriv_const_smul, Pi.smul_apply, cutoffIntegrand, coefficient_frequencyDeriv]
  simp only [coordinateDeriv_cons, coordinateDeriv_nil]
  rw [fderiv_comp_sub (f := fun η ↦ b.coefficient (x, η))]

private theorem fderiv_cutoffIntegrand_apply (b : Symbol n V W m) (s : ℝ)
    (θ : CoordinateSpace n) (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ cutoffIntegrand χ b s p θ) p v =
      ∑ j, v.1 j • cutoffIntegrand χ (spatialDeriv j b) s p θ +
        ∑ j, v.2 j • cutoffIntegrand χ (frequencyDeriv j b) s p θ := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (differentiableAt_cutoffIntegrand χ b s θ p)]
  simp only [coordinateDeriv_fst_cutoffIntegrand, coordinateDeriv_snd_cutoffIntegrand]

end Integrand

/-! ### The coefficient -/

section Coefficient

variable (χ : 𝓢(CoordinateSpace n, ℂ))

/-- The coefficient `c_s(x, ξ) = ∫ 𝓕χ(θ) b(x, ξ - sθ) dθ`. -/
private def cutoffCoeff (b : Symbol n V W m) (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) :
    V →L[ℂ] W :=
  ∫ θ, cutoffIntegrand χ b s p θ

private theorem differentiableAt_cutoffCoeff_and_fderiv_apply (b : Symbol n V W m) (s : ℝ)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (cutoffCoeff χ b s) p₀ ∧ ∀ v, fderiv ℝ (cutoffCoeff χ b s) p₀ v =
      ∑ j, v.1 j • (∫ θ, cutoffIntegrand χ (spatialDeriv j b) s p₀ θ) +
        ∑ j, v.2 j • ∫ θ, cutoffIntegrand χ (frequencyDeriv j b) s p₀ θ := by
  have hK : IsCompact (Metric.closedBall p₀.1 1) := isCompact_closedBall _ _
  have hb : ∀ {k : ℝ} (d : Fin n → Symbol n V W k), ∃ C : Fin n → ℝ, ∀ j θ,
      ∀ p ∈ Metric.ball p₀ 1, ‖cutoffIntegrand χ (d j) s p θ‖ ≤
        C j * cutoffWeight χ k |s| θ := by
    intro k d
    have h := fun j ↦ exists_norm_cutoffIntegrand_le χ (d j) hK |s|
    choose C hC0 hC using h
    refine ⟨fun j ↦ C j * (2 ^ |k| * (1 + ‖p₀.2‖ ^ 2) ^ (k / 2)), fun j θ p hp ↦ ?_⟩
    have hp' : dist p p₀ < 1 := hp
    rw [Prod.dist_eq, max_lt_iff] at hp'
    have hw := one_add_norm_sq_rpow_le_of_norm_sub_le_one (dist_eq_norm p.2 p₀.2 ▸ hp'.2.le) k
    have hθ : 0 ≤ cutoffWeight χ k |s| θ := by unfold cutoffWeight; positivity
    calc ‖cutoffIntegrand χ (d j) s p θ‖
        ≤ C j * (1 + ‖p.2‖ ^ 2) ^ (k / 2) * cutoffWeight χ k |s| θ :=
          hC j s le_rfl p.1 (Metric.mem_closedBall.2 hp'.1.le) p.2 θ
      _ ≤ C j * (2 ^ |k| * (1 + ‖p₀.2‖ ^ 2) ^ (k / 2)) * cutoffWeight χ k |s| θ := by
          gcongr
          exact hC0 j
  obtain ⟨Cx, hCx⟩ := hb fun j ↦ spatialDeriv j b
  obtain ⟨Cξ, hCξ⟩ := hb fun j ↦ frequencyDeriv j b
  refine differentiableAt_integral_and_fderiv_apply_eq_sum (E := V →L[ℂ] W)
    (F := cutoffIntegrand χ b s)
    (A := fun j p θ ↦ cutoffIntegrand χ (spatialDeriv j b) s p θ)
    (B := fun j p θ ↦ cutoffIntegrand χ (frequencyDeriv j b) s p θ)
    (fun θ p ↦ differentiableAt_cutoffIntegrand χ b s θ p)
    (fun θ p v ↦ fderiv_cutoffIntegrand_apply χ b s θ p v)
    (integrable_cutoffIntegrand χ b s)
    (fun j p ↦ continuous_cutoffIntegrand χ _ s p)
    (fun j p ↦ continuous_cutoffIntegrand χ _ s p)
    (((integrable_cutoffWeight χ m |s|).const_mul (∑ j, Cx j)).add
      ((integrable_cutoffWeight χ (m - 1) |s|).const_mul (∑ j, Cξ j))) p₀ fun θ p hp ↦ ?_
  rw [Pi.add_apply, Finset.sum_mul, Finset.sum_mul]
  exact add_le_add (Finset.sum_le_sum fun j _ ↦ hCx j θ p hp)
    (Finset.sum_le_sum fun j _ ↦ hCξ j θ p hp)

/-- The derivative `∂_{x_j} c_s` is the coefficient built from `∂_{x_j} b`. -/
private theorem coordinateDeriv_fst_cutoffCoeff (b : Symbol n V W m) (s : ℝ) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ cutoffCoeff χ b s (x, ξ)) x =
      cutoffCoeff χ (spatialDeriv j b) s (x, ξ) := by
  obtain ⟨hd, hf⟩ := differentiableAt_cutoffCoeff_and_fderiv_apply χ b s (x, ξ)
  rw [coordinateDeriv_fst_eq_fderiv (f := cutoffCoeff χ b s) (p := (x, ξ)) hd, hf]
  simp only [PiLp.ofLp_single, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.zero_apply, Finset.sum_const_zero,
    add_zero]
  rfl

/-- The derivative `∂_{ξ_j} c_s` is the coefficient built from `∂_{ξ_j} b`. -/
private theorem coordinateDeriv_snd_cutoffCoeff (b : Symbol n V W m) (s : ℝ) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ cutoffCoeff χ b s (x, ξ)) ξ =
      cutoffCoeff χ (frequencyDeriv j b) s (x, ξ) := by
  obtain ⟨hd, hf⟩ := differentiableAt_cutoffCoeff_and_fderiv_apply χ b s (x, ξ)
  rw [coordinateDeriv_snd_eq_fderiv (f := cutoffCoeff χ b s) (p := (x, ξ)) hd, hf]
  simp only [PiLp.ofLp_single, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, PiLp.zero_apply, Finset.sum_const_zero,
    zero_add]
  rfl

private theorem contDiff_cutoffCoeff (s : ℝ) :
    ∀ (k : ℕ) {m : ℝ} (b : Symbol n V W m), ContDiff ℝ k (cutoffCoeff χ b s)
  | 0, _, b => contDiff_zero.2 <| continuous_iff_continuousAt.2 fun p ↦
      (differentiableAt_cutoffCoeff_and_fderiv_apply χ b s p).1.continuousAt
  | k + 1, _, b => by
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun p ↦ (differentiableAt_cutoffCoeff_and_fderiv_apply χ b s p).1, by simp,
      contDiff_clm_apply_iff.2 fun v ↦ ?_⟩
    have h : (fun p ↦ fderiv ℝ (cutoffCoeff χ b s) p v) = fun p ↦
        ∑ j, v.1 j • cutoffCoeff χ (spatialDeriv j b) s p +
          ∑ j, v.2 j • cutoffCoeff χ (frequencyDeriv j b) s p := funext fun p ↦ by
      rw [fderiv_apply_eq_sum_coordinateDeriv
        (differentiableAt_cutoffCoeff_and_fderiv_apply χ b s p).1]
      simp only [coordinateDeriv_fst_cutoffCoeff, coordinateDeriv_snd_cutoffCoeff]
    rw [h]
    exact (ContDiff.sum fun j _ ↦ (contDiff_cutoffCoeff s k _).const_smul _).add
      (ContDiff.sum fun j _ ↦ (contDiff_cutoffCoeff s k _).const_smul _)

/-- The coefficient `c_s` grows at most like `⟨ξ⟩ ^ m`, uniformly for scales `|s| ≤ R` and
positions in a compact set. -/
private theorem exists_norm_cutoffCoeff_le (b : Symbol n V W m) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ∈ K, ∀ ξ,
      ‖cutoffCoeff χ b s (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_cutoffIntegrand_le χ b hK R
  set I := ∫ θ, cutoffWeight χ m R θ
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by unfold cutoffWeight; positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun s hs x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_cutoffWeight χ m R).const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) (.of_forall fun θ ↦ hC s hs x hx ξ θ)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- Every mixed derivative `∂_x^α ∂_ξ^β` of `c_s` is the coefficient built from a symbol `b'` of
order `m - |β|`, and the same mixed derivative of `b` is `b'`. -/
private theorem exists_mixedDeriv_cutoffCoeff (s : ℝ) (α β : List (Fin n)) :
    ∀ {m : ℝ} (b : Symbol n V W m), ∃ (m' : ℝ) (b' : Symbol n V W m'), m' = m - β.length ∧
      (∀ x ξ, mixedDeriv α β (cutoffCoeff χ b s) x ξ = cutoffCoeff χ b' s (x, ξ)) ∧
      ∀ x ξ, mixedDeriv α β b.coefficient x ξ = b'.coefficient (x, ξ) := by
  induction β using List.reverseRecOn with
  | nil =>
    induction α using List.reverseRecOn with
    | nil => exact fun b ↦ ⟨_, b, by simp, fun x ξ ↦ by simp, fun x ξ ↦ by simp⟩
    | append_singleton js j ih =>
      intro m b
      obtain ⟨m', b', hm', hc, hb⟩ := ih (spatialDeriv j b)
      refine ⟨m', b', hm', fun x ξ ↦ ?_, fun x ξ ↦ ?_⟩
      · rw [← hc, mixedDeriv_def, mixedDeriv_def, coordinateDeriv_append]
        simp only [coordinateDeriv_nil]
        congr 1
        funext y
        exact coordinateDeriv_fst_cutoffCoeff χ b s j y ξ
      · rw [← hb, mixedDeriv_spatialDeriv]
  | append_singleton js j ih =>
    intro m b
    obtain ⟨m', b', hm', hc, hb⟩ := ih (frequencyDeriv j b)
    refine ⟨m', b', by rw [hm']; simp; ring, fun x ξ ↦ ?_, fun x ξ ↦ ?_⟩
    · rw [← hc, mixedDeriv_def, mixedDeriv_def]
      congr 1
      funext y
      rw [coordinateDeriv_append]
      congr 1
      funext η
      exact coordinateDeriv_snd_cutoffCoeff χ b s j y η
    · rw [← hb, mixedDeriv_frequencyDeriv]

end Coefficient

/-! ### The kernel cutoff -/

section KernelCutoff

variable (χ : 𝓢(CoordinateSpace n, ℂ))

/-- **The kernel cutoff of a symbol.** For a Schwartz function `χ` and a symbol `b` of order `m`,
the symbol of order `m`

`c(x, ξ) = ∫ 𝓕χ(θ) b(x, ξ - 2πθ) dθ`,

whose quantization `Op(c) u (x) = Op(b)(χ(x - ·) u)(x)` has the kernel `χ(x - y) K_b(x, y)`
(`TauCeti.Symbol.quantizeSchwartzValue_kernelCutoff`). For compactly supported `χ` this operator
is properly supported, and for `χ = 1` near `0` the difference `c - b` is smoothing
(`TauCeti.Symbol.isSmoothing_kernelCutoff_sub`). -/
def kernelCutoff (b : Symbol n V W m) : Symbol n V W m where
  coefficient := cutoffCoeff χ b (2 * π)
  contDiff_coefficient := contDiff_infty.2 fun k ↦ contDiff_cutoffCoeff χ (2 * π) k b
  exists_bound K hK α β := by
    obtain ⟨m', b', hm', hc, -⟩ := exists_mixedDeriv_cutoffCoeff χ (2 * π) α β b
    obtain ⟨C, hC0, hC⟩ := exists_norm_cutoffCoeff_le χ b' hK (2 * π)
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    rw [hc, ← hm']
    exact hC (2 * π) (abs_of_pos Real.two_pi_pos).le x hx ξ

@[simp]
theorem coefficient_kernelCutoff (b : Symbol n V W m) (x ξ : CoordinateSpace n) :
    (kernelCutoff χ b).coefficient (x, ξ) = ∫ θ, 𝓕 χ θ • b.coefficient (x, ξ - (2 * π) • θ) :=
  (rfl)

/-- Position derivatives commute with the kernel cutoff. -/
theorem spatialDeriv_kernelCutoff (j : Fin n) (b : Symbol n V W m) :
    spatialDeriv j (kernelCutoff χ b) = kernelCutoff χ (spatialDeriv j b) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv]
  exact coordinateDeriv_fst_cutoffCoeff χ b (2 * π) j x ξ

/-- Frequency derivatives commute with the kernel cutoff. -/
theorem frequencyDeriv_kernelCutoff (j : Fin n) (b : Symbol n V W m) :
    frequencyDeriv j (kernelCutoff χ b) = kernelCutoff χ (frequencyDeriv j b) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_frequencyDeriv]
  exact coordinateDeriv_snd_cutoffCoeff χ b (2 * π) j x ξ

/-- The kernel cutoff of a symbol vanishing at the positions outside a compact set vanishes there
too. -/
theorem HasCompactSpatialSupport.kernelCutoff {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) : (Symbol.kernelCutoff χ b).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hbK⟩ := hasCompactSpatialSupport_iff.1 hb
  refine hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ ↦ ?_⟩
  rw [coefficient_kernelCutoff]
  simp [hbK x hx]

end KernelCutoff

/-! ### The quantization of the kernel cutoff -/

section Quantization

variable (χ : 𝓢(CoordinateSpace n, ℂ))

/-- The Schwartz function `y ↦ χ(x - y)`. -/
private def reflectAt (x : CoordinateSpace n) : 𝓢(CoordinateSpace n, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ x
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) χ)

private theorem reflectAt_apply (x y : CoordinateSpace n) : reflectAt χ x y = χ (x - y) := by
  simp [reflectAt]

private theorem coe_reflectAt (x : CoordinateSpace n) : ⇑(reflectAt χ x) = fun y ↦ χ (x - y) :=
  funext (reflectAt_apply χ x)

/-- The Fourier transform of `y ↦ χ(x - y)` is `t ↦ exp(-2πi ⟪x, t⟫) 𝓕χ(-t)`. -/
private theorem fourier_reflectAt (x t : CoordinateSpace n) :
    𝓕 (reflectAt χ x) t = (𝐞 (-⟪x, t⟫) : ℂ) * 𝓕 χ (-t) := by
  rw [SchwartzMap.fourier_coe, coe_reflectAt, Real.fourier_eq, SchwartzMap.fourier_coe,
    Real.fourier_eq, ← integral_const_mul,
    ← integral_sub_left_eq_self (fun z ↦ (𝐞 (-⟪x, t⟫) : ℂ) * (𝐞 (-⟪z, -t⟫) • χ z)) volume x]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [Circle.smul_def, smul_eq_mul, inner_sub_left, inner_neg_right,
    neg_neg, ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  ring_nf

/-- The double integrand of the quantization of the kernel cutoff, after inserting the
convolution formula for `𝓕(χ(x - ·) u)`, is integrable in both frequencies. -/
private theorem integrable_cutoffQuantizeIntegrand (b : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.2, x⟫ : ℂ) •
      𝓕 χ (q.2 - q.1) • b.coefficient (x, (2 * π) • q.1) (𝓕 u q.2)) (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := b.exists_bound_coefficient_slice x
  set χ' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) (𝓕 χ)
  have hχ' : ∀ θ, χ' θ = 𝓕 χ (-θ) := fun θ ↦ rfl
  have hh : Integrable fun η : CoordinateSpace n ↦ (1 + ‖(2 * π) • η‖ ^ 2) ^ (m / 2) * ‖𝓕 u η‖ :=
    (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m
  have hk : Integrable fun θ : CoordinateSpace n ↦ (1 + ‖(2 * π) • θ‖ ^ 2) ^ (|m| / 2) * ‖χ' θ‖ :=
    χ'.integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) |m|
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 ⟪q.2, x⟫ : ℂ) •
      𝓕 χ (q.2 - q.1) • b.coefficient (x, (2 * π) • q.1) (𝓕 u q.2) := by
    refine (continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by fun_prop))).smul
      (((𝓕 χ).continuous.comp (by fun_prop)).smul
        ((b.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
          ((𝓕 u).continuous.comp continuous_snd)))
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk).const_mul
    (C * 2 ^ (|m| / 2))).mono' hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  have hξ : (2 * π) • q.1 = (2 * π) • q.2 + (2 * π) • (q.1 - q.2) := by
    rw [← smul_add, add_sub_cancel]
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m ((2 * π) • q.2) ((2 * π) • (q.1 - q.2))
  rw [← hξ] at hpeetre
  rw [ContinuousLinearMap.mul_apply', hχ', neg_sub, norm_smul, Circle.norm_coe, one_mul,
    norm_smul]
  calc ‖𝓕 χ (q.2 - q.1)‖ * ‖b.coefficient (x, (2 * π) • q.1) (𝓕 u q.2)‖
      ≤ ‖𝓕 χ (q.2 - q.1)‖ * (C * (1 + ‖(2 * π) • q.1‖ ^ 2) ^ (m / 2) * ‖𝓕 u q.2‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC _)
    _ ≤ ‖𝓕 χ (q.2 - q.1)‖ * (C * (2 ^ (|m| / 2) * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ (m / 2) *
          (1 + ‖(2 * π) • (q.1 - q.2)‖ ^ 2) ^ (|m| / 2)) * ‖𝓕 u q.2‖) := by gcongr
    _ = _ := by ring

variable [CompleteSpace V] [CompleteSpace W]

/-- **The quantization of the kernel cutoff.** For a Schwartz function `u`,

`Op(c) u (x) = Op(b)(χ(x - ·) u)(x)`, with `c = kernelCutoff χ b`:

the kernel of `Op(c)` is `χ(x - y) K_b(x, y)`. -/
theorem quantizeSchwartzValue_kernelCutoff (b : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (kernelCutoff χ b).coefficient u x =
      quantizeSchwartzValue b.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x := by
  set H : CoordinateSpace n → CoordinateSpace n → W := fun ζ η ↦ (𝐞 ⟪η, x⟫ : ℂ) •
    𝓕 χ (η - ζ) • b.coefficient (x, (2 * π) • ζ) (𝓕 u η) with hHdef
  have hH : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ H q.1 q.2)
      (volume.prod volume) := integrable_cutoffQuantizeIntegrand χ b u x
  -- Insert the convolution formula for `𝓕(χ(x - ·) u)` and change variables to `η = ζ - t`.
  have hR : quantizeSchwartzValue b.coefficient
      (SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u) x = ∫ ζ, ∫ η, H ζ η := by
    rw [quantizeSchwartzValue_def]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
    have hsl : SchwartzMap.smulLeftCLM V (fun y ↦ χ (x - y)) u =
        SchwartzMap.smulLeftCLM V (reflectAt χ x : CoordinateSpace n → ℂ) u := by
      rw [coe_reflectAt]
    have hint : Integrable fun η : CoordinateSpace n ↦
        ((𝐞 (-⟪x, ζ - η⟫) : ℂ) * 𝓕 χ (η - ζ)) • 𝓕 u η := by
      refine (((𝓕 u).integrable (μ := volume)).norm.const_mul
        (SchwartzMap.seminorm ℂ 0 0 (𝓕 χ))).mono' ?_ (.of_forall fun η ↦ ?_)
      · exact (((continuous_subtype_val.comp (Real.continuous_fourierChar.comp
          (by fun_prop))).mul ((𝓕 χ).continuous.comp (by fun_prop))).smul
            (𝓕 u).continuous).aestronglyMeasurable
      · rw [norm_smul, norm_mul, Circle.norm_coe, one_mul]
        gcongr
        exact (𝓕 χ).norm_le_seminorm ℂ _
    beta_reduce
    rw [hsl, SchwartzMap.fourier_smulLeftCLM_apply,
      ← integral_sub_left_eq_self (fun t ↦ 𝓕 (reflectAt χ x) t • 𝓕 u (ζ - t)) volume ζ]
    simp only [fourier_reflectAt, sub_sub_cancel, neg_sub]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint, Circle.smul_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun η ↦ ?_)
    simp only [hHdef, map_smul, smul_smul]
    congr 1
    have h : ⟪ζ, x⟫ + -⟪x, ζ - η⟫ = ⟪η, x⟫ := by
      rw [inner_sub_right, real_inner_comm x ζ, real_inner_comm x η]
      ring
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    simp only [h]
  -- Swap the integrals and change variables to `ζ = η - θ` in the inner one.
  rw [hR, integral_integral_swap hH, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  beta_reduce
  rw [← integral_sub_left_eq_self (fun ζ ↦ H ζ η) volume η, coefficient_kernelCutoff,
    ContinuousLinearMap.integral_apply
      (φ := fun θ ↦ 𝓕 χ θ • b.coefficient (x, (2 * π) • η - (2 * π) • θ))
      (integrable_cutoffIntegrand χ b (2 * π) (x, (2 * π) • η)),
    Circle.smul_def, ← integral_smul]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  simp only [hHdef, sub_sub_cancel, smul_sub, smul_apply]

private theorem hasTemperateGrowth_comp_sub (x : CoordinateSpace n) :
    (fun y ↦ χ (x - y)).HasTemperateGrowth := by
  rw [← coe_reflectAt]
  exact (reflectAt χ x).hasTemperateGrowth

/-- **Locality of the kernel cutoff.** `Op(c) u (x)` only depends on the values of `u` at the
points `y` with `χ(x - y) ≠ 0`. -/
theorem quantizeSchwartzValue_kernelCutoff_congr (b : Symbol n V W m)
    {u v : 𝓢(CoordinateSpace n, V)} {x : CoordinateSpace n}
    (h : ∀ y, χ (x - y) ≠ 0 → u y = v y) :
    quantizeSchwartzValue (kernelCutoff χ b).coefficient u x =
      quantizeSchwartzValue (kernelCutoff χ b).coefficient v x := by
  rw [quantizeSchwartzValue_kernelCutoff, quantizeSchwartzValue_kernelCutoff]
  congr 1
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_comp_sub χ x),
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_comp_sub χ x)]
  by_cases hy : χ (x - y) = 0
  · simp [hy]
  · rw [h y hy]

/-- `Op(c) u (x) = 0` if `u` vanishes at the points `y` with `χ(x - y) ≠ 0`. -/
theorem quantizeSchwartzValue_kernelCutoff_eq_zero (b : Symbol n V W m)
    {u : 𝓢(CoordinateSpace n, V)} {x : CoordinateSpace n} (h : ∀ y, χ (x - y) ≠ 0 → u y = 0) :
    quantizeSchwartzValue (kernelCutoff χ b).coefficient u x = 0 := by
  rw [quantizeSchwartzValue_kernelCutoff_congr χ b (v := 0) (by simpa using h),
    quantizeSchwartzValue_zero_right]

/-- The support of `Op(c) u` lies in the sum of the supports of `u` and `χ`. -/
theorem support_quantizeSchwartzValue_kernelCutoff_subset (b : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) :
    Function.support (quantizeSchwartzValue (kernelCutoff χ b).coefficient u) ⊆
      Function.support u + Function.support χ := by
  intro x hx
  by_contra hns
  refine hx (quantizeSchwartzValue_kernelCutoff_eq_zero χ b fun y hy ↦ ?_)
  by_contra hu
  exact hns ⟨y, hu, x - y, hy, add_sub_cancel y x⟩

/-- **Proper support.** For compactly supported `χ`, the operator `Op(c)` sends compactly supported
Schwartz functions to compactly supported ones. -/
theorem hasCompactSupport_quantizeSchwartzValue_kernelCutoff (hχ : HasCompactSupport χ)
    (b : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) :
    HasCompactSupport (quantizeSchwartzValue (kernelCutoff χ b).coefficient u) := by
  have hK := hu.isCompact.add hχ.isCompact
  refine HasCompactSupport.intro' hK hK.isClosed fun x hx ↦ ?_
  by_contra h
  exact hx (Set.add_subset_add (subset_tsupport _) (subset_tsupport _)
    (support_quantizeSchwartzValue_kernelCutoff_subset χ b u h))

end Quantization

/-! ### The kernel cutoff differs from the symbol by a smoothing symbol -/

section Smoothing

/-- The factor `-(2πi)⁻¹` with `θⱼ 𝓕ψ(θ) = -(-(2πi)⁻¹) 𝓕(∂ⱼψ)(θ)`. -/
private def scaleFactor : ℂ := -(2 * π * Complex.I)⁻¹

private theorem norm_scaleFactor : ‖scaleFactor‖ = (2 * π)⁻¹ := by
  simp [scaleFactor, norm_inv, abs_of_pos Real.pi_pos]

/-- The partial derivative `∂ⱼψ` of a Schwartz function. -/
private def schwartzPartial (ψ : 𝓢(CoordinateSpace n, ℂ)) (j : Fin n) : 𝓢(CoordinateSpace n, ℂ) :=
  ∂_{(EuclideanSpace.single j 1 : CoordinateSpace n)} ψ

/-- `𝓕(∂ⱼψ)(θ) = 2πi θⱼ 𝓕ψ(θ)`. -/
private theorem fourier_schwartzPartial (ψ : 𝓢(CoordinateSpace n, ℂ)) (j : Fin n)
    (θ : CoordinateSpace n) : 𝓕 (schwartzPartial ψ j) θ = 2 * π * Complex.I * θ j * 𝓕 ψ θ := by
  rw [schwartzPartial, SchwartzMap.fourier_lineDerivOp_apply, smul_eq_mul]
  simp [EuclideanSpace.inner_single_right]

/-- The derivative in the scale `s` of the integrand of `c_s`. -/
private theorem hasDerivAt_cutoffIntegrand (ψ : 𝓢(CoordinateSpace n, ℂ)) (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) (θ : CoordinateSpace n) (s : ℝ) :
    HasDerivAt (fun s ↦ cutoffIntegrand ψ b s p θ)
      (∑ j, scaleFactor • cutoffIntegrand (schwartzPartial ψ j)
        (frequencyDeriv j b) s p θ) s := by
  have hb : HasFDerivAt (fun η ↦ b.coefficient (p.1, η))
      (fderiv ℝ (fun η ↦ b.coefficient (p.1, η)) (p.2 - s • θ)) (p.2 - s • θ) :=
    ((b.contDiff_coefficient.comp (contDiff_prodMk_right p.1)).differentiable (by simp)
      _).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ ↦ p.2 - s • θ) (-θ) s := by
    simpa using ((hasDerivAt_id s).smul_const θ).const_sub p.2
  have h : HasDerivAt (fun s ↦ cutoffIntegrand ψ b s p θ)
      (𝓕 ψ θ • fderiv ℝ (fun η ↦ b.coefficient (p.1, η)) (p.2 - s • θ) (-θ)) s :=
    (hb.comp_hasDerivAt s hpath).const_smul (𝓕 ψ θ)
  refine h.congr_deriv ?_
  rw [map_neg, ContinuousLinearMap.apply_eq_sum_single, smul_neg, Finset.smul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [cutoffIntegrand, fourier_schwartzPartial, fderiv_coefficient_slice_single,
    ← Complex.coe_smul, smul_smul, smul_smul, ← neg_smul]
  congr 1
  simp only [scaleFactor]
  field_simp

/-- A Schwartz function that is constant near `0` has partial derivatives vanishing near `0`. -/
private theorem schwartzPartial_eventuallyEq_zero {ψ : 𝓢(CoordinateSpace n, ℂ)}
    (hψ : ⇑ψ =ᶠ[𝓝 0] fun _ ↦ ψ 0) (j : Fin n) :
    ⇑(schwartzPartial ψ j) =ᶠ[𝓝 0] fun _ ↦ 0 := by
  filter_upwards [hψ.eventually_nhds] with y hy
  rw [schwartzPartial, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    Filter.EventuallyEq.fderiv_eq (f := fun _ ↦ ψ 0) hy,
    fderiv_const_apply, zero_apply]

/-- The derivative in the scale `s` of `c_s` is `-(2πi)⁻¹ ∑ⱼ` of the coefficients built from
`∂ⱼψ` and `∂_{ξ_j} b`. -/
private theorem hasDerivAt_cutoffCoeff (ψ : 𝓢(CoordinateSpace n, ℂ)) (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ cutoffCoeff ψ b s p)
      (∑ j, scaleFactor • cutoffCoeff (schwartzPartial ψ j)
        (frequencyDeriv j b) s₀ p) s₀ := by
  set R := |s₀| + 1
  have hb : ∀ j, ∃ C, ∀ s : ℝ, |s| ≤ R → ∀ θ,
      ‖cutoffIntegrand (schwartzPartial ψ j) (frequencyDeriv j b) s p θ‖ ≤
        C * (1 + ‖p.2‖ ^ 2) ^ ((m - 1) / 2) *
          cutoffWeight (schwartzPartial ψ j) (m - 1) R θ := fun j ↦ by
    obtain ⟨C, -, hC⟩ := exists_norm_cutoffIntegrand_le (schwartzPartial ψ j)
      (frequencyDeriv j b) (isCompact_singleton (x := p.1)) R
    exact ⟨C, fun s hs θ ↦ hC s hs p.1 rfl p.2 θ⟩
  choose C hC using hb
  have hball : ∀ s ∈ Metric.ball s₀ 1, |s| ≤ R := fun s hs ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub s s₀
    simp only [R]
    linarith
  have hF'c : Continuous fun θ ↦ ∑ j, scaleFactor • cutoffIntegrand (schwartzPartial ψ j)
      (frequencyDeriv j b) s₀ p θ :=
    continuous_finsetSum Finset.univ fun j _ ↦
      (continuous_cutoffIntegrand (schwartzPartial ψ j) (frequencyDeriv j b) s₀ p).const_smul
        scaleFactor
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun s θ ↦ cutoffIntegrand ψ b s p θ)
    (F' := fun s θ ↦ ∑ j, scaleFactor • cutoffIntegrand (schwartzPartial ψ j)
      (frequencyDeriv j b) s p θ)
    (bound := fun θ ↦ ∑ j, ‖scaleFactor‖ * (C j * (1 + ‖p.2‖ ^ 2) ^ ((m - 1) / 2) *
      cutoffWeight (schwartzPartial ψ j) (m - 1) R θ))
    (Metric.ball_mem_nhds s₀ one_pos)
    (.of_forall fun s ↦ (continuous_cutoffIntegrand ψ b s p).aestronglyMeasurable)
    (integrable_cutoffIntegrand ψ b s₀ p)
    hF'c.aestronglyMeasurable
    (.of_forall fun θ s hs ↦ (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC j s (hball s hs) θ) (norm_nonneg _)))
    (integrable_finsetSum _ fun j _ ↦
      ((integrable_cutoffWeight _ (m - 1) R).const_mul _).const_mul _)
    (.of_forall fun θ s _ ↦ hasDerivAt_cutoffIntegrand ψ b p θ s)
  have h2 : HasDerivAt (fun s ↦ cutoffCoeff ψ b s p) _ s₀ := h.2
  refine h2.congr_deriv ?_
  rw [integral_finsetSum (f := fun j θ ↦ scaleFactor • cutoffIntegrand (schwartzPartial ψ j)
    (frequencyDeriv j b) s₀ p θ) Finset.univ fun j _ ↦
    (integrable_cutoffIntegrand (schwartzPartial ψ j) (frequencyDeriv j b) s₀ p).smul scaleFactor]
  simp only [integral_smul, cutoffCoeff]

/-- The case `N = 0` of the interpolation estimate: `c_s - ψ(0) b` has order `m`, uniformly for
`s ∈ [0, 2π]` and positions in a compact set. -/
private theorem exists_norm_cutoffCoeff_sub_le_zero (b : Symbol n V W m)
    (ψ : 𝓢(CoordinateSpace n, ℂ)) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 (2 * π), ∀ x ∈ K, ∀ ξ,
      ‖cutoffCoeff ψ b s (x, ξ) - ψ 0 • b.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_cutoffCoeff_le ψ b hK (2 * π)
  obtain ⟨C₂, hC₂0, hC₂⟩ := b.exists_bound_coefficient K hK
  refine ⟨C₁ + ‖ψ 0‖ * C₂, by positivity, fun s hs x hx ξ ↦ ?_⟩
  have hs' : |s| ≤ 2 * π := by rw [abs_of_nonneg hs.1]; exact hs.2
  calc ‖cutoffCoeff ψ b s (x, ξ) - ψ 0 • b.coefficient (x, ξ)‖
      ≤ ‖cutoffCoeff ψ b s (x, ξ)‖ + ‖ψ 0‖ * ‖b.coefficient (x, ξ)‖ :=
        (norm_sub_le _ _).trans_eq (by rw [norm_smul])
    _ ≤ C₁ * (1 + ‖ξ‖ ^ 2) ^ (m / 2) + ‖ψ 0‖ * (C₂ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
        gcongr
        · exact hC₁ s hs' x hx ξ
        · exact hC₂ x hx ξ
    _ = _ := by ring

variable [CompleteSpace W]

/-- At the scale `s = 0` the interpolating coefficient is `ψ(0) b`. -/
private theorem cutoffCoeff_zero (ψ : 𝓢(CoordinateSpace n, ℂ)) (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) : cutoffCoeff ψ b 0 p = ψ 0 • b.coefficient p := by
  simp only [cutoffCoeff, cutoffIntegrand, zero_smul, sub_zero, Prod.mk.eta]
  rw [integral_smul_const, SchwartzMap.integral_fourier_eq]

/-- **The interpolation estimate.** If `ψ` is constant near `0`, then `c_s - ψ(0) b` has order
`m - N` for every `N`, uniformly for `s ∈ [0, 2π]` and positions in a compact set. -/
private theorem exists_norm_cutoffCoeff_sub_le (N : ℕ) :
    ∀ {m : ℝ} (b : Symbol n V W m) (ψ : 𝓢(CoordinateSpace n, ℂ)),
      (⇑ψ =ᶠ[𝓝 0] fun _ ↦ ψ 0) → ∀ {K : Set (CoordinateSpace n)}, IsCompact K →
        ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.Icc 0 (2 * π), ∀ x ∈ K, ∀ ξ,
          ‖cutoffCoeff ψ b s (x, ξ) - ψ 0 • b.coefficient (x, ξ)‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  induction N with
  | zero =>
    intro m b ψ _ K hK
    simpa using exists_norm_cutoffCoeff_sub_le_zero b ψ hK
  | succ N ih =>
    -- The derivative in `s` involves `∂ⱼψ`, which vanishes near `0`, and `∂_{ξ_j} b`, of order
    -- `m - 1`; the induction hypothesis bounds it, and `c_0 - ψ(0) b = 0`.
    intro m b ψ hψ K hK
    have hψ' : ∀ j, ⇑(schwartzPartial ψ j) =ᶠ[𝓝 0]
        fun _ ↦ (schwartzPartial ψ j) 0 := fun j ↦ by
      have h := schwartzPartial_eventuallyEq_zero hψ j
      rwa [h.eq_of_nhds]
    have hψ0 : ∀ j, (schwartzPartial ψ j) 0 = 0 := fun j ↦
      (schwartzPartial_eventuallyEq_zero hψ j).eq_of_nhds
    choose C hC0 hC using fun j ↦ ih (frequencyDeriv j b) _ (hψ' j) hK
    refine ⟨2 * π * (‖scaleFactor‖ * ∑ j, C j), mul_nonneg Real.two_pi_pos.le
      (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ ↦ hC0 j)), fun s hs x hx ξ ↦ ?_⟩
    set w := (1 + ‖ξ‖ ^ 2) ^ ((m - ↑(N + 1)) / 2)
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - N) / 2) = w := by
      rw [show m - 1 - (N : ℝ) = m - ↑(N + 1) by push_cast; ring]
    have hderiv : ∀ t ∈ Set.Icc 0 (2 * π), HasDerivWithinAt
        (fun s ↦ cutoffCoeff ψ b s (x, ξ) - ψ 0 • b.coefficient (x, ξ))
        (∑ j, scaleFactor • cutoffCoeff (schwartzPartial ψ j)
          (frequencyDeriv j b) t (x, ξ)) (Set.Icc 0 (2 * π)) t := fun t _ ↦
      ((hasDerivAt_cutoffCoeff ψ b (x, ξ) t).sub_const _).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Ico 0 (2 * π),
        ‖∑ j, scaleFactor • cutoffCoeff (schwartzPartial ψ j)
          (frequencyDeriv j b) t (x, ξ)‖ ≤ ‖scaleFactor‖ * ∑ j, C j * w := fun t ht ↦ by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ ↦ ?_
      have h := hC j t (Set.Ico_subset_Icc_self ht) x hx ξ
      rw [hψ0 j, zero_smul, sub_zero, hw] at h
      rw [norm_smul]
      gcongr
    -- The mean value inequality on `[0, s]`.
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound s hs
    simp only [cutoffCoeff_zero, sub_self, sub_zero] at hmvt
    have hA : 0 ≤ ‖scaleFactor‖ * ∑ j, C j * w :=
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hC0 j) (by positivity))
    calc ‖cutoffCoeff ψ b s (x, ξ) - ψ 0 • b.coefficient (x, ξ)‖
        ≤ (‖scaleFactor‖ * ∑ j, C j * w) * s := by simpa using hmvt
      _ ≤ (‖scaleFactor‖ * ∑ j, C j * w) * (2 * π) := mul_le_mul_of_nonneg_left hs.2 hA
      _ = 2 * π * (‖scaleFactor‖ * ∑ j, C j) * w := by
          rw [← Finset.sum_mul]
          ring

variable (χ : 𝓢(CoordinateSpace n, ℂ))

/-- **The removed part of the kernel is smoothing.** If `χ = 1` near `0`, then the kernel cutoff
`c` of `b` differs from `b` by a smoothing symbol: `Op(b) - Op(c)`, whose kernel
`(1 - χ(x - y)) K_b(x, y)` vanishes near the diagonal, has a symbol of order `-∞`. -/
theorem isSmoothing_kernelCutoff_sub (hχ : ⇑χ =ᶠ[𝓝 0] 1) (b : Symbol n V W m) :
    (kernelCutoff χ b - b).IsSmoothing := by
  have h0 : χ 0 = 1 := hχ.eq_of_nhds
  have hP : ⇑χ =ᶠ[𝓝 0] fun _ ↦ χ 0 := by
    rw [h0]
    exact hχ
  refine isSmoothing_iff_forall_exists_bound.2 fun m' K hK α β ↦ ?_
  obtain ⟨m'', b', hm'', hc, hb⟩ := exists_mixedDeriv_cutoffCoeff χ (2 * π) α β b
  obtain ⟨C, hC0, hC⟩ := exists_norm_cutoffCoeff_sub_le ⌈m - m'⌉₊ b' χ hP hK
  refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
  have hd : mixedDeriv α β (kernelCutoff χ b - b).coefficient x ξ =
      cutoffCoeff χ b' (2 * π) (x, ξ) - b'.coefficient (x, ξ) := by
    rw [coefficient_sub, sub_eq_add_neg, mixedDeriv_add (a := (kernelCutoff χ b).coefficient)
      (b := -b.coefficient) (kernelCutoff χ b).contDiff_coefficient b.contDiff_coefficient.neg,
      mixedDeriv_neg, ← sub_eq_add_neg, ← hb, ← hc]
    rfl
  have h := hC (2 * π) ⟨Real.two_pi_pos.le, le_rfl⟩ x hx ξ
  rw [h0, one_smul] at h
  rw [hd]
  refine h.trans (mul_le_mul_of_nonneg_left (rpow_weight_le_rpow_weight ξ ?_) hC0)
  rw [hm'']
  linarith [Nat.le_ceil (m - m')]

/-- **Every pseudodifferential operator is properly supported up to a smoothing operator.** For
every `ε > 0`, every symbol `b` differs by a smoothing symbol from a symbol `c` whose
quantization has kernel supported within distance `ε` of the diagonal: `Op(c) u (x) = 0` whenever
`u` vanishes on the ball of radius `ε` about `x`. -/
theorem exists_isSmoothing_sub_and_quantizeSchwartzValue_eq_zero [CompleteSpace V]
    (b : Symbol n V W m) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Symbol n V W m, (c - b).IsSmoothing ∧ ∀ (u : 𝓢(CoordinateSpace n, V))
      (x : CoordinateSpace n), (∀ y ∈ Metric.ball x ε, u y = 0) →
        quantizeSchwartzValue c.coefficient u x = 0 := by
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have hsmooth : ContDiff ℝ ∞ fun y ↦ (φ y : ℂ) := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hsupp : HasCompactSupport fun y ↦ (φ y : ℂ) :=
    φ.hasCompactSupport.comp_left Complex.ofReal_zero
  set χ := hsupp.toSchwartzMap hsmooth
  have hχ : ∀ y, χ y = (φ y : ℂ) := fun y ↦ rfl
  refine ⟨kernelCutoff χ b, isSmoothing_kernelCutoff_sub χ ?_ b, fun u x hu ↦ ?_⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : CoordinateSpace n) (half_pos hε)] with y hy
    rw [hχ, φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), Complex.ofReal_one,
      Pi.one_apply]
  · refine quantizeSchwartzValue_kernelCutoff_eq_zero χ b fun y hy ↦ hu y ?_
    have hmem : x - y ∈ Function.support φ := fun h ↦ hy (by rw [hχ, h, Complex.ofReal_zero])
    rw [φ.support_eq, Metric.mem_ball, dist_zero_right] at hmem
    rwa [Metric.mem_ball, dist_eq_norm, ← norm_neg, neg_sub]

end Smoothing

end Symbol

end TauCeti
