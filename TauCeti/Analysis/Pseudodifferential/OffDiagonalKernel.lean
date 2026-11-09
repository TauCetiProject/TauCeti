/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The kernel of a pseudodifferential operator off the diagonal

The left quantization `Op(a)` of a symbol `a` of order `m` on `ℝⁿ`
(`TauCeti.quantizeSchwartzValue`) has the Schwartz kernel
`K(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`. For `m ≥ -n` this integral does not converge
and `K` is in general a distribution concentrated near the diagonal: for `a = 1` it is the delta
function of `x - y`. This file shows that off the diagonal `K` is a smooth function, which
represents `Op(a)` on inputs supported away from the output point.

The proof integrates by parts in the frequency, trading decay of the symbol for powers of the
displacement `x - y`.

* **Low order.** If `m < -n`, the kernel converges absolutely. In Mathlib's normalization it is
  `k_a(x, z) = ∫ exp(2πi ⟪ζ, z⟫) a(x, 2πζ) dζ`, the inverse Fourier transform `𝓕⁻` of the rescaled
  frequency slice, and `Op(a) u (x) = ∫ k_a(x, x - y) u(y) dy`
  (`TauCeti.quantizeSchwartzValue_eq_integral_fourierInv`). If `m + k < -n`, then `k_a` is jointly
  `C^k` in `(x, z)` (`TauCeti.Symbol.contDiff_fourierInv_coefficient`): a position derivative
  falls on the symbol, a displacement derivative multiplies it by the frequency.
* **Weights on the input.** Multiplying the input by `yⱼ - xⱼ` and evaluating at `x` amounts to
  replacing `a` by `-i ∂_{ξⱼ} a` (`TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub`), so
  `Op(a) (‖· - x‖^(2N) u) (x) = Op((-Δ_ξ)^N a) u (x)`
  (`TauCeti.Symbol.quantizeSchwartzValue_iterate_smulLeftCLM_norm_sub_sq`).
* **Weights on the kernel.** Dually, `k_{-Δ_ξ c}(x, z) = ‖z‖² k_c(x, z)` for `c` of order `< -n`
  (`TauCeti.Symbol.fourierInv_coefficient_neg_frequencyLaplacian`).

For any `N` with `m - 2N < -n`, the symbol `(-Δ_ξ)^N a` has order `m - 2N < -n`, and the
off-diagonal kernel is `K_a(x, y) = ‖x - y‖^(-2N) k_{(-Δ_ξ)^N a}(x, x - y)`
(`TauCeti.Symbol.offDiagonalKernel`).

## Main results

* `TauCeti.Symbol.offDiagonalKernel_eq`: `K_a` does not depend on the admissible `N`.
* `TauCeti.Symbol.contDiffOn_offDiagonalKernel`: `K_a` is smooth on `{(x, y) | x ≠ y}`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: for a compactly supported
  Schwartz function `u` with `x ∉ tsupport u`, `Op(a) u (x) = ∫ K_a(x, y) u(y) dy`.
* `TauCeti.Symbol.offDiagonalKernel_const`: a constant symbol, such as the symbol `1` of the
  identity, has no kernel off the diagonal.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace LineDeriv ContDiff
open MeasureTheory Real FourierTransform Module

noncomputable section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

section Weight

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The derivative along `v` of the Fourier transform of a Schwartz function, multiplied by the
phase `exp(2πi ⟪ζ, x⟫)`, is the Fourier transform of `-2πi ⟪y - x, v⟫ u(y)` times the phase. -/
private lemma hasLineDerivAt_fourierChar_smul_fourier (x v : E) (u : 𝓢(E, V)) (ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ) • 𝓕 u ζ)
      ((𝐞 ⟪ζ, x⟫ : ℂ) • (-(2 * π * Complex.I)) •
        𝓕 (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, v⟫) u) ζ) ζ v := by
  have hin : HasFDerivAt (fun ζ : E ↦ ⟪ζ, x⟫) (innerSL ℝ x) ζ := by
    simpa [real_inner_comm] using (innerSL ℝ x).hasFDerivAt (x := ζ)
  have he := (hasDerivAt_fourierChar ⟪ζ, x⟫).hasFDerivAt.comp ζ hin
  have hF : HasFDerivAt ⇑(𝓕 u : 𝓢(E, V)) (fderiv ℝ ⇑(𝓕 u : 𝓢(E, V)) ζ) ζ :=
    ((𝓕 u).differentiableAt).hasFDerivAt
  convert (he.smul hF).hasLineDerivAt v using 1
  · rfl
  have hl : fderiv ℝ ⇑(𝓕 u : 𝓢(E, V)) ζ v =
      (-(2 * π * Complex.I)) • 𝓕 (SchwartzMap.smulLeftCLM V (inner ℝ · v) u) ζ := by
    rw [← SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_fourier_eq,
      FourierTransform.fourier_smul, smul_apply]
  have hsub : SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, v⟫) u =
      SchwartzMap.smulLeftCLM V (inner ℝ · v) u + (-⟪x, v⟫) • u := by
    ext y
    have h1 : (fun y : E ↦ ⟪y - x, v⟫).HasTemperateGrowth := by fun_prop
    have h2 : (inner ℝ · v : E → ℝ).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.smulLeftCLM_apply_apply h1, add_apply, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply h2, inner_sub_left, sub_smul, neg_smul, sub_eq_add_neg]
  rw [hsub, FourierTransform.fourier_add, FourierTransform.fourier_smul, add_apply, smul_apply]
  simp only [add_apply, smul_apply, hl, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, Complex.real_smul, real_inner_comm v x]
  module

/-- **Multiplication by a coordinate centred at the output point.** If `ξ ↦ a(x, ξ)` is `C¹` and
both it and its derivative `∂_v a(x, ξ)` along `v` have polynomial growth, then quantizing
`y ↦ ⟪y - x, v⟫ u(y)` and evaluating at `x` gives `-i Op(∂_v a) u (x)`. On the Fourier side this
is an integration by parts in the frequency. -/
theorem quantizeSchwartzValue_smulLeftCLM_inner_sub {a : E × E → V →L[ℂ] W} {x : E}
    {C C' m m' : ℝ} (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ)) (v : E)
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, v⟫) u) x =
      -Complex.I • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x := by
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, v⟫) u
  set a' : E × E → V →L[ℂ] W := fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v
  have hmeas : AEStronglyMeasurable fun ξ ↦ a (x, ξ) := ha.continuous.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable fun ξ ↦ a' (x, ξ) :=
    ((ha.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable
  have hda (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ a (x, (2 * π) • ζ))
      ((2 * π : ℝ) • a' (x, (2 * π) • ζ)) ζ v := by
    have h := ((ha.differentiable one_ne_zero ((2 * π) • ζ)).hasFDerivAt.comp ζ
      ((hasFDerivAt_id ζ).const_smul (2 * π))).hasLineDerivAt v
    convert h using 1
    · rfl
    · simp [a']
  -- the bilinear pairing `(A, v) ↦ A v`, as a real bilinear map
  let B : (V →L[ℂ] W) →L[ℝ] V →L[ℝ] W := ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ
  have hB (A : V →L[ℂ] W) (y : V) : B A y = A y := rfl
  have e₁ : (fun ζ ↦ B ((2 * π : ℝ) • a' (x, (2 * π) • ζ)) ((𝐞 ⟪ζ, x⟫ : ℂ) • 𝓕 u ζ)) =
      fun ζ ↦ (2 * π : ℝ) • (𝐞 ⟪ζ, x⟫ • a' (x, (2 * π) • ζ) (𝓕 u ζ)) := by
    funext ζ
    simp [hB, Circle.smul_def]
  have e₂ : (fun ζ ↦ B (a (x, (2 * π) • ζ))
      ((𝐞 ⟪ζ, x⟫ : ℂ) • (-(2 * π * Complex.I)) • 𝓕 w ζ)) =
      fun ζ ↦ (-(2 * π * Complex.I)) • (𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 w ζ)) := by
    funext ζ
    simp only [hB, map_smul, Circle.smul_def]
    exact smul_comm _ _ _
  have e₃ : (fun ζ ↦ B (a (x, (2 * π) • ζ)) ((𝐞 ⟪ζ, x⟫ : ℂ) • 𝓕 u ζ)) =
      fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) := by
    funext ζ
    simp [hB, Circle.smul_def]
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := B) (v := v) (f := fun ζ ↦ a (x, (2 * π) • ζ))
    (f' := fun ζ ↦ (2 * π : ℝ) • a' (x, (2 * π) • ζ))
    (g := fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ) • 𝓕 u ζ)
    (g' := fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ) • (-(2 * π * Complex.I)) • 𝓕 w ζ)
    (by rw [e₁]; exact (integrable_quantizeSchwartzValue_integrand hmeas' hC' (𝓕 u)).smul _)
    (by rw [e₂]; exact (integrable_quantizeSchwartzValue_integrand hmeas hC (𝓕 w)).smul _)
    (by rw [e₃]; exact integrable_quantizeSchwartzValue_integrand hmeas hC (𝓕 u))
    (fun ζ _ ↦ hda ζ) (fun ζ _ ↦ hasLineDerivAt_fourierChar_smul_fourier x v u ζ)
  rw [e₁, e₂, integral_smul, integral_smul, ← quantizeSchwartzValue_def,
    ← quantizeSchwartzValue_def] at hibp
  have hne : (-(2 * π * Complex.I)) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [← inv_smul_smul₀ hne (quantizeSchwartzValue a w x), hibp, smul_neg, ← neg_smul,
    ← Complex.coe_smul, smul_smul]
  congr 1
  field_simp
  ring_nf
  simp [Complex.I_sq]

end Weight

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- The quantization at a point is additive over finite sums of symbols of the same order. -/
private lemma quantizeSchwartzValue_sum_left {ι : Type*} (s : Finset ι) (b : ι → Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (∑ i ∈ s, b i).coefficient u x =
      ∑ i ∈ s, quantizeSchwartzValue (b i).coefficient u x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨C, hC⟩ := (b i).exists_norm_coefficient_le {x} isCompact_singleton
    obtain ⟨D, hD⟩ := (∑ i ∈ s, b i).exists_norm_coefficient_le {x} isCompact_singleton
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefficient_add,
      quantizeSchwartzValue_add_left ((b i).continuous_coefficient_slice x).aestronglyMeasurable
        (hC x rfl) ((∑ i ∈ s, b i).continuous_coefficient_slice x).aestronglyMeasurable
        (hD x rfl), ih]

/-- The quantization of a symbol at a point is additive over finite sums of inputs. -/
private lemma quantizeSchwartzValue_sum_right (a : Symbol n V W m) {ι : Type*} (s : Finset ι)
    (u : ι → 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (∑ i ∈ s, u i) x =
      ∑ i ∈ s, quantizeSchwartzValue a.coefficient (u i) x := by
  classical
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
        (hC x rfl), ih]

/-- **Multiplication by a coordinate centred at the output point.** For a symbol `a`, quantizing
`y ↦ (yⱼ - xⱼ) u(y)` and evaluating at `x` gives `-i Op(∂_{ξⱼ} a) u (x)`. -/
theorem quantizeSchwartzValue_smulLeftCLM_inner_sub_single (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, EuclideanSpace.single j 1⟫) u) x =
      -Complex.I • quantizeSchwartzValue (frequencyDeriv j a).coefficient u x := by
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  obtain ⟨C', hC'⟩ := (frequencyDeriv j a).exists_norm_coefficient_le {x} isCompact_singleton
  have hd (p : CoordinateSpace n × CoordinateSpace n) :
      fderiv ℝ (fun η ↦ a.coefficient (p.1, η)) p.2 (EuclideanSpace.single j 1) =
        (frequencyDeriv j a).coefficient p := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
  rw [quantizeSchwartzValue_smulLeftCLM_inner_sub
    ((a.contDiff_coefficient.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) _ (hC x rfl)
    (m' := m - 1) (fun ξ ↦ by have h := hd (x, ξ); dsimp only at h; rw [h]; exact hC' x rfl ξ)]
  simp only [hd]

/-- **Multiplication by the squared distance to the output point.** For a symbol `a`, quantizing
`y ↦ ‖y - x‖² u(y)` and evaluating at `x` gives `Op(-Δ_ξ a) u (x)`. -/
theorem quantizeSchwartzValue_smulLeftCLM_norm_sub_sq (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ ‖y - x‖ ^ 2) u) x =
      quantizeSchwartzValue (-frequencyLaplacian a).coefficient u x := by
  set M : Fin n → 𝓢(CoordinateSpace n, V) →L[ℝ] 𝓢(CoordinateSpace n, V) := fun j ↦
    SchwartzMap.smulLeftCLM V (fun y ↦ ⟪y - x, EuclideanSpace.single j 1⟫)
  have hM : SchwartzMap.smulLeftCLM V (fun y ↦ ‖y - x‖ ^ 2) u = ∑ j, M j (M j u) := by
    ext y
    have h₁ : (fun y : CoordinateSpace n ↦ ‖y - x‖ ^ 2).HasTemperateGrowth :=
      (Function.hasTemperateGrowth_norm_sq (CoordinateSpace n)).comp (f := (· - x)) (by fun_prop)
    have h₂ (j : Fin n) : (fun y : CoordinateSpace n ↦
        ⟪y - x, EuclideanSpace.single j (1 : ℝ)⟫).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.smulLeftCLM_apply_apply h₁, sum_apply, EuclideanSpace.real_norm_sq_eq]
    simp only [M, SchwartzMap.smulLeftCLM_apply_apply (h₂ _)]
    simp only [smul_smul, ← Finset.sum_smul, EuclideanSpace.inner_single_right, one_mul,
      RCLike.conj_to_real, sq]
  have hneg : (-frequencyLaplacian a).coefficient = (-1 : ℂ) • (frequencyLaplacian a).coefficient
    := by rw [coefficient_neg, neg_one_smul]
  rw [hM, quantizeSchwartzValue_sum_right, hneg, quantizeSchwartzValue_smul_left,
    frequencyLaplacian_apply, quantizeSchwartzValue_sum_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quantizeSchwartzValue_smulLeftCLM_inner_sub_single,
    quantizeSchwartzValue_smulLeftCLM_inner_sub_single, smul_smul, coefficient_inclusion]
  congr 1
  simp

/-- Iterating `quantizeSchwartzValue_smulLeftCLM_norm_sub_sq`: quantizing
`y ↦ ‖y - x‖^(2N) u(y)` and evaluating at `x` gives `Op((-Δ_ξ)^N a) u (x)`. -/
theorem quantizeSchwartzValue_iterate_smulLeftCLM_norm_sub_sq (a : Symbol n V W m) (N : ℕ)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        ((SchwartzMap.smulLeftCLM V (fun y ↦ ‖y - x‖ ^ 2))^[N] u) x =
      quantizeSchwartzValue (negFrequencyLaplacianPow N a).coefficient u x := by
  induction N generalizing u with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, ih, quantizeSchwartzValue_smulLeftCLM_norm_sub_sq,
      coefficient_negFrequencyLaplacianPow_succ]

end Symbol

section LowOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- For a coefficient of order `m < -dim E` at the position `x`, the frequency slice
`ζ ↦ a(x, 2πζ)` is integrable. -/
theorem integrable_coefficient_two_pi_smul {a : E × E → V →L[ℂ] W} {x : E} {C m : ℝ}
    (hmeas : AEStronglyMeasurable fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (hm : m < -finrank ℝ E) :
    Integrable fun ζ ↦ a (x, (2 * π) • ζ) :=
  ((integrable_one_add_norm_smul_sq_rpow volume Real.two_pi_pos.ne' hm).const_mul C).mono'
    (hmeas.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_smul volume Real.two_pi_pos.ne'))
    (ae_of_all _ fun _ ↦ hC _)

/-- **The kernel of an operator of low order.** If `ξ ↦ a(x, ξ)` is a.e. strongly measurable
with `‖a(x, ξ)‖ ≤ C ⟨ξ⟩ ^ m` for some `m < -dim E`, then the quantization at `x` is given by the
absolutely convergent kernel `k(x, z) = ∫ exp(2πi ⟪ζ, z⟫) a(x, 2πζ) dζ`, Mathlib's inverse
Fourier transform of the rescaled frequency slice:
`Op(a) u (x) = ∫ k(x, x - y) u(y) dy`. In angular frequency,
`k(x, z) = (2π)⁻ⁿ ∫ exp(i ⟪z, ξ⟫) a(x, ξ) dξ`. -/
theorem quantizeSchwartzValue_eq_integral_fourierInv [CompleteSpace V] [CompleteSpace W]
    {a : E × E → V →L[ℂ] W} {x : E} {C m : ℝ}
    (hmeas : AEStronglyMeasurable fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (hm : m < -finrank ℝ E)
    (u : 𝓢(E, V)) :
    quantizeSchwartzValue a u x = ∫ y, 𝓕⁻ (fun ζ ↦ a (x, (2 * π) • ζ)) (x - y) (u y) := by
  have ha := integrable_coefficient_two_pi_smul hmeas hC hm
  set F : E × E → W := fun p ↦ (𝐞 ⟪p.1, x - p.2⟫ : ℂ) • a (x, (2 * π) • p.1) (u p.2)
  have hF : Integrable F (volume.prod volume) := by
    refine (ha.norm.mul_prod u.integrable.norm).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · have h₁ : AEStronglyMeasurable (fun p : E × E ↦ a (x, (2 * π) • p.1))
          (volume.prod volume) := ha.aestronglyMeasurable.comp_fst
      have h₂ : Continuous fun p : E × E ↦ (𝐞 ⟪p.1, x - p.2⟫ : ℂ) := by fun_prop
      exact h₂.aestronglyMeasurable.smul
        (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (h₁.prodMk (u.continuous.comp continuous_snd).aestronglyMeasurable))
    · simp only [F, norm_smul, Circle.norm_coe, one_mul]
      exact (a _).le_opNorm _
  have hinner (ζ : E) : 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (𝓕 u ζ) = ∫ y, F (ζ, y) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq, ← ContinuousLinearMap.integral_comp_comm _
      ((Real.fourierIntegral_convergent_iff ζ).2 u.integrable), Circle.smul_def,
      ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    have h : ⟪ζ, x - y⟫ = ⟪ζ, x⟫ + -⟪y, ζ⟫ := by
      rw [inner_sub_right, real_inner_comm y ζ, sub_eq_add_neg]
    simp only [F, Circle.smul_def, map_smul, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      h]
  rw [quantizeSchwartzValue_def, integral_congr_ae (ae_of_all _ hinner),
    integral_integral_swap hF]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [Real.fourierInv_eq, ContinuousLinearMap.integral_apply]
  · simp [F, Circle.smul_def]
  · exact ha.norm.mono' ((by fun_prop : Continuous fun ζ : E ↦ 𝐞 ⟪ζ, x - y⟫
      ).aestronglyMeasurable.smul ha.aestronglyMeasurable) (ae_of_all _ fun ζ ↦ by simp)

end LowOrder

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-- For a symbol of order `m < -n`, each frequency slice `ζ ↦ a(x, 2πζ)` is integrable. -/
theorem integrable_coefficient_two_pi_smul (a : Symbol n V W m) (hm : m < -n)
    (x : CoordinateSpace n) : Integrable fun ζ ↦ a.coefficient (x, (2 * π) • ζ) := by
  obtain ⟨C, hC⟩ := a.exists_norm_coefficient_le {x} isCompact_singleton
  exact TauCeti.integrable_coefficient_two_pi_smul (a.continuous_coefficient_slice x
    ).aestronglyMeasurable (hC x rfl) (by simpa using hm)

/-- The phase `exp(2πi ⟪ζ, z⟫)` times an integrable function is integrable. -/
private lemma integrable_fourierChar_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : CoordinateSpace n → F} (hf : Integrable f) (z : CoordinateSpace n) :
    Integrable fun ζ ↦ 𝐞 ⟪ζ, z⟫ • f ζ := by
  simpa [inner_neg_right] using (Real.fourierIntegral_convergent_iff (μ := volume) (-z)).2 hf

/-- **The kernel of a frequency derivative.** For a symbol `c` of order `m < -n`, the kernel
`k_c(x, z) = ∫ exp(2πi ⟪ζ, z⟫) c(x, 2πζ) dζ` satisfies `k_{∂_{ξⱼ} c}(x, z) = -i zⱼ k_c(x, z)`: an
integration by parts in the frequency. -/
theorem fourierInv_coefficient_frequencyDeriv (c : Symbol n V W m) (hm : m < -n) (j : Fin n)
    (x z : CoordinateSpace n) :
    𝓕⁻ (fun ζ ↦ (frequencyDeriv j c).coefficient (x, (2 * π) • ζ)) z =
      (-(Complex.I * z j)) • 𝓕⁻ (fun ζ ↦ c.coefficient (x, (2 * π) • ζ)) z := by
  set e : CoordinateSpace n := EuclideanSpace.single j 1
  have hc := c.integrable_coefficient_two_pi_smul hm x
  have hc' := (frequencyDeriv j c).integrable_coefficient_two_pi_smul (by linarith) x
  have hdc (ζ : CoordinateSpace n) : HasLineDerivAt ℝ (fun ζ ↦ c.coefficient (x, (2 * π) • ζ))
      ((2 * π : ℝ) • (frequencyDeriv j c).coefficient (x, (2 * π) • ζ)) ζ e := by
    have hd : Differentiable ℝ fun η ↦ c.coefficient (x, η) :=
      (c.contDiff_coefficient.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
    have h := ((hd ((2 * π) • ζ)).hasFDerivAt.comp ζ
      ((hasFDerivAt_id ζ).const_smul (2 * π))).hasLineDerivAt e
    convert h using 1
    · rfl
    · simp [e, coordinateDeriv_cons]
  have hde (ζ : CoordinateSpace n) : HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, z⟫ : ℂ))
      ((2 * π * Complex.I * z j) * 𝐞 ⟪ζ, z⟫) ζ e := by
    have hin : HasFDerivAt (fun ζ : CoordinateSpace n ↦ ⟪ζ, z⟫) (innerSL ℝ z) ζ := by
      simpa [real_inner_comm] using (innerSL ℝ z).hasFDerivAt (x := ζ)
    convert ((hasDerivAt_fourierChar ⟪ζ, z⟫).hasFDerivAt.comp ζ hin).hasLineDerivAt e using 1
    · rfl
    · simp [e, EuclideanSpace.inner_single_right]
      ring
  -- the pairing `(A, s) ↦ s • A`, as a real bilinear map
  let B : (V →L[ℂ] W) →L[ℝ] ℂ →L[ℝ] (V →L[ℂ] W) := (ContinuousLinearMap.lsmul ℝ ℂ).flip
  have hB (A : V →L[ℂ] W) (s : ℂ) : B A s = s • A := rfl
  have e₁ : (fun ζ ↦ B ((2 * π : ℝ) • (frequencyDeriv j c).coefficient (x, (2 * π) • ζ))
      (𝐞 ⟪ζ, z⟫ : ℂ)) = fun ζ ↦ (2 * π : ℝ) •
        (𝐞 ⟪ζ, z⟫ • (frequencyDeriv j c).coefficient (x, (2 * π) • ζ)) := by
    funext ζ
    simp only [hB, Circle.smul_def]
    exact smul_comm _ _ _
  have e₂ : (fun ζ ↦ B (c.coefficient (x, (2 * π) • ζ))
      ((2 * π * Complex.I * z j) * 𝐞 ⟪ζ, z⟫)) = fun ζ ↦ (2 * π * Complex.I * z j) •
        (𝐞 ⟪ζ, z⟫ • c.coefficient (x, (2 * π) • ζ)) := by
    funext ζ
    simp only [hB, Circle.smul_def, mul_smul]
  have e₃ : (fun ζ ↦ B (c.coefficient (x, (2 * π) • ζ)) (𝐞 ⟪ζ, z⟫ : ℂ)) =
      fun ζ ↦ 𝐞 ⟪ζ, z⟫ • c.coefficient (x, (2 * π) • ζ) := by
    funext ζ
    simp [hB, Circle.smul_def]
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := B) (v := e) (f := fun ζ ↦ c.coefficient (x, (2 * π) • ζ))
    (f' := fun ζ ↦ (2 * π : ℝ) • (frequencyDeriv j c).coefficient (x, (2 * π) • ζ))
    (g := fun ζ ↦ (𝐞 ⟪ζ, z⟫ : ℂ)) (g' := fun ζ ↦ (2 * π * Complex.I * z j) * 𝐞 ⟪ζ, z⟫)
    (by rw [e₁]; exact (integrable_fourierChar_smul hc' z).smul (2 * π : ℝ))
    (by rw [e₂]; exact (integrable_fourierChar_smul hc z).smul (2 * π * Complex.I * z j : ℂ))
    (by rw [e₃]; exact integrable_fourierChar_smul hc z)
    (fun ζ _ ↦ hdc ζ) (fun ζ _ ↦ hde ζ)
  rw [e₁, e₂, integral_smul, integral_smul, ← Real.fourierInv_eq, ← Real.fourierInv_eq,
    ← Complex.coe_smul, eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero] at hibp
  have hne : ((2 * π : ℝ) : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  refine smul_right_injective _ hne ?_
  simp only
  rw [hibp, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

/-- The coefficient of `-Δ_ξ a` is minus the sum of the second frequency derivatives of `a`. -/
private lemma coefficient_neg_frequencyLaplacian (a : Symbol n V W m) (p) :
    (-frequencyLaplacian a).coefficient p =
      -∑ j, (frequencyDeriv j (frequencyDeriv j a)).coefficient p := by
  rw [coefficient_neg, Pi.neg_apply, frequencyLaplacian_apply, coefficient_sum, Finset.sum_apply]
  simp

/-- **The kernel of the negative frequency Laplacian.** For a symbol `c` of order `m < -n`, the
kernel `k_c(x, z) = ∫ exp(2πi ⟪ζ, z⟫) c(x, 2πζ) dζ` satisfies `k_{-Δ_ξ c}(x, z) = ‖z‖² k_c(x, z)`.
-/
theorem fourierInv_coefficient_neg_frequencyLaplacian (c : Symbol n V W m) (hm : m < -n)
    (x z : CoordinateSpace n) :
    𝓕⁻ (fun ζ ↦ (-frequencyLaplacian c).coefficient (x, (2 * π) • ζ)) z =
      (‖z‖ ^ 2) • 𝓕⁻ (fun ζ ↦ c.coefficient (x, (2 * π) • ζ)) z := by
  have hint (j : Fin n) :=
    (frequencyDeriv j (frequencyDeriv j c)).integrable_coefficient_two_pi_smul (by linarith) x
  have hR : 𝓕⁻ (fun ζ ↦ (-frequencyLaplacian c).coefficient (x, (2 * π) • ζ)) z =
      -∑ j, 𝓕⁻ (fun ζ ↦ (frequencyDeriv j (frequencyDeriv j c)).coefficient (x, (2 * π) • ζ)) z
      := by
    simp only [coefficient_neg_frequencyLaplacian, Real.fourierInv_eq, Circle.smul_def, smul_neg,
      Finset.smul_sum]
    rw [integral_neg, integral_finsetSum _ fun j _ ↦ by
      simpa [Circle.smul_def] using integrable_fourierChar_smul (hint j) z]
  rw [hR, EuclideanSpace.real_norm_sq_eq, Finset.sum_smul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [fourierInv_coefficient_frequencyDeriv _ (by linarith),
    fourierInv_coefficient_frequencyDeriv c hm, smul_smul, ← neg_smul, ← Complex.coe_smul]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

section Smoothness

/-! ### Smoothness of the kernel of an operator of low order -/

/-- The rescaled weight `ζ ↦ ⟨2πζ⟩ ^ m` is integrable on `ℝⁿ` for `m < -n`. -/
private lemma integrable_weight {m' : ℝ} (hm : m' < -n) :
    Integrable fun ζ : CoordinateSpace n ↦ (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m' / 2) :=
  integrable_one_add_norm_smul_sq_rpow volume Real.two_pi_pos.ne' (by simpa using hm)

section Generic

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- The derivative in `(x, z)` of the kernel integrand `exp(2πi ⟪ζ, z⟫) f(x, 2πζ)`. -/
private def kernelIntegrandFDeriv (f : CoordinateSpace n × CoordinateSpace n → U)
    (p : CoordinateSpace n × CoordinateSpace n) (ζ : CoordinateSpace n) :
    CoordinateSpace n × CoordinateSpace n →L[ℝ] U :=
  (𝐞 ⟪ζ, p.2⟫ : ℂ) • ((fderiv ℝ (fun y ↦ f (y, (2 * π) • ζ)) p.1).comp
      (ContinuousLinearMap.fst ℝ _ _)) +
    ((ContinuousLinearMap.toSpanSingleton ℝ (2 * π * Complex.I * 𝐞 ⟪ζ, p.2⟫)).comp
      ((innerSL ℝ ζ).comp (ContinuousLinearMap.snd ℝ _ _))).smulRight (f (p.1, (2 * π) • ζ))

private lemma kernelIntegrandFDeriv_apply (f : CoordinateSpace n × CoordinateSpace n → U)
    (p y : CoordinateSpace n × CoordinateSpace n) (ζ : CoordinateSpace n) :
    kernelIntegrandFDeriv f p ζ y =
      (𝐞 ⟪ζ, p.2⟫ : ℂ) • fderiv ℝ (fun y ↦ f (y, (2 * π) • ζ)) p.1 y.1 +
        ((2 * π * Complex.I * 𝐞 ⟪ζ, p.2⟫) * ⟪ζ, y.2⟫) • f (p.1, (2 * π) • ζ) := by
  simp [kernelIntegrandFDeriv, mul_comm, Complex.real_smul, mul_smul]

private lemma continuous_kernelIntegrand {f : CoordinateSpace n × CoordinateSpace n → U}
    (hf : Continuous f) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (𝐞 ⟪q.2, q.1.2⟫ : ℂ) • f (q.1.1, (2 * π) • q.2) := by
  fun_prop

private lemma hasFDerivAt_kernelIntegrand {f : CoordinateSpace n × CoordinateSpace n → U}
    (hf : ContDiff ℝ 1 f) (p : CoordinateSpace n × CoordinateSpace n) (ζ : CoordinateSpace n) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪ζ, p.2⟫ : ℂ) • f (p.1, (2 * π) • ζ)) (kernelIntegrandFDeriv f p ζ) p := by
  have he := (hasDerivAt_fourierChar ⟪ζ, p.2⟫).hasFDerivAt.comp p
    ((innerSL ℝ ζ).hasFDerivAt.comp p hasFDerivAt_snd)
  have hc := (((hf.comp (contDiff_id.prodMk (contDiff_const (c := (2 * π) • ζ)))).differentiable
    (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  exact he.smul hc

private lemma continuous_kernelIntegrandFDeriv {f : CoordinateSpace n × CoordinateSpace n → U}
    (hf : ContDiff ℝ 1 f) (p : CoordinateSpace n × CoordinateSpace n) :
    Continuous (kernelIntegrandFDeriv f p) := by
  have hD : Continuous fun ζ : CoordinateSpace n ↦
      fderiv ℝ (fun y ↦ f (y, (2 * π) • ζ)) p.1 :=
    (ContDiff.fderiv (f := fun (ζ y : CoordinateSpace n) ↦ f (y, (2 * π) • ζ))
      (hf.comp (contDiff_snd.prodMk (contDiff_fst.const_smul _)))
      contDiff_const (n := 0) (by simp)).continuous
  have hc : Continuous fun ζ : CoordinateSpace n ↦ f (p.1, (2 * π) • ζ) :=
    hf.continuous.comp (by fun_prop)
  refine continuous_clm_apply.2 fun y ↦ ?_
  simp only [kernelIntegrandFDeriv_apply]
  fun_prop

private lemma norm_kernelIntegrandFDeriv_le (f : CoordinateSpace n × CoordinateSpace n → U)
    (p : CoordinateSpace n × CoordinateSpace n) (ζ : CoordinateSpace n) :
    ‖kernelIntegrandFDeriv f p ζ‖ ≤ ‖fderiv ℝ (fun y ↦ f (y, (2 * π) • ζ)) p.1‖ +
      ‖(2 * π) • ζ‖ * ‖f (p.1, (2 * π) • ζ)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
  rw [kernelIntegrandFDeriv_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Circle.norm_coe, one_mul]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le y) (norm_nonneg _))
  · rw [norm_smul, norm_mul, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_I,
      mul_one, Complex.norm_real, norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le]
    have hi : ‖⟪ζ, y.2⟫‖ ≤ ‖ζ‖ * ‖y‖ :=
      (norm_inner_le_norm ζ y.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le y) (norm_nonneg _))
    have h2 : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg Real.two_pi_pos.le]
    rw [h2]
    calc 2 * π * ‖⟪ζ, y.2⟫‖ * ‖f (p.1, (2 * π) • ζ)‖
        ≤ 2 * π * (‖ζ‖ * ‖y‖) * ‖f (p.1, (2 * π) • ζ)‖ := by gcongr
      _ = 2 * π * ‖ζ‖ * ‖f (p.1, (2 * π) • ζ)‖ * ‖y‖ := by ring

private lemma norm_kernelIntegrandFDeriv_le_rpow {p₀ : CoordinateSpace n × CoordinateSpace n}
    {f : CoordinateSpace n × CoordinateSpace n → U} {C C' : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ, ‖f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ,
      ‖fderiv ℝ (fun y ↦ f (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ζ : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n)
    (hp : p ∈ Metric.ball p₀ 1) :
    ‖kernelIntegrandFDeriv f p ζ‖ ≤
      (max C' 0 + C) * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m + 1) / 2) := by
  have hp1 : p.1 ∈ Metric.closedBall p₀.1 1 := Metric.mem_closedBall.2
    (((le_max_left _ _).trans_eq Prod.dist_eq.symm).trans (Metric.mem_ball.1 hp).le)
  set w := 1 + ‖(2 * π) • ζ‖ ^ 2
  have hw := one_add_norm_sq_rpow_mul_norm_le ((2 * π) • ζ) m
  have hw' : w ^ (m / 2) ≤ w ^ ((m + 1) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖(2 * π) • ζ‖]) (by linarith)
  have h₁ : ‖fderiv ℝ (fun y ↦ f (y, (2 * π) • ζ)) p.1‖ ≤ max C' 0 * w ^ (m / 2) :=
    (hC' p.1 hp1 _).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h₂ := hC p.1 hp1 ((2 * π) • ζ)
  refine (norm_kernelIntegrandFDeriv_le f p ζ).trans ?_
  calc _ ≤ max C' 0 * w ^ (m / 2) + ‖(2 * π) • ζ‖ * (C * w ^ (m / 2)) := by gcongr
    _ = max C' 0 * w ^ (m / 2) + C * (w ^ (m / 2) * ‖(2 * π) • ζ‖) := by ring
    _ ≤ max C' 0 * w ^ ((m + 1) / 2) + C * w ^ ((m + 1) / 2) := by gcongr
    _ = (max C' 0 + C) * w ^ ((m + 1) / 2) := by ring

/-- Differentiation of the kernel `(x, z) ↦ ∫ exp(2πi ⟪ζ, z⟫) f(x, 2πζ) dζ` under the integral sign,
for a `C¹` function `f` whose values and position derivatives are `O(⟨ξ⟩ ^ m)` near `x₀`, with
`m + 1 < -n`. -/
private lemma hasFDerivAt_integral_kernelIntegrand
    {f : CoordinateSpace n × CoordinateSpace n → U} (hf : ContDiff ℝ 1 f) (hm : m + 1 < -n)
    {p₀ : CoordinateSpace n × CoordinateSpace n} {C C' : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ, ‖f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ,
      ‖fderiv ℝ (fun y ↦ f (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) :
    HasFDerivAt (fun p : CoordinateSpace n × CoordinateSpace n ↦
      ∫ ζ, (𝐞 ⟪ζ, p.2⟫ : ℂ) • f (p.1, (2 * π) • ζ)) (∫ ζ, kernelIntegrandFDeriv f p₀ ζ) p₀ := by
  have hint : Integrable fun ζ : CoordinateSpace n ↦ (𝐞 ⟪ζ, p₀.2⟫ : ℂ) • f (p₀.1, (2 * π) • ζ) :=
    ((integrable_weight (by linarith : m < -n)).const_mul C).mono'
      ((continuous_kernelIntegrand hf.continuous).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun ζ ↦ by
        rw [norm_smul, Circle.norm_coe, one_mul]
        exact hC _ (Metric.mem_closedBall_self zero_le_one) _)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds p₀ one_pos)
    (Filter.Eventually.of_forall fun p ↦ ((continuous_kernelIntegrand hf.continuous).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable) hint
    (continuous_kernelIntegrandFDeriv hf p₀).aestronglyMeasurable
    (ae_of_all _ fun ζ ↦ norm_kernelIntegrandFDeriv_le_rpow hC0 hC hC' ζ)
    ((integrable_weight hm).const_mul _)
    (ae_of_all _ fun ζ p _ ↦ hasFDerivAt_kernelIntegrand hf p ζ)

/-- The derivative of the kernel in the direction `y = (h, w)`: the position derivative falls on
`f`, the displacement derivative brings down `2πi ⟪ζ, w⟫`. -/
private lemma fderiv_integral_kernelIntegrand_apply
    {f : CoordinateSpace n × CoordinateSpace n → U} (hf : ContDiff ℝ 1 f) (hm : m + 1 < -n)
    {p₀ : CoordinateSpace n × CoordinateSpace n} {C C' : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ, ‖f (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hC' : ∀ x ∈ Metric.closedBall p₀.1 1, ∀ ξ,
      ‖fderiv ℝ (fun y ↦ f (y, ξ)) x‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (y : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      ∫ ζ, (𝐞 ⟪ζ, p.2⟫ : ℂ) • f (p.1, (2 * π) • ζ)) p₀ y =
      ∫ ζ, kernelIntegrandFDeriv f p₀ ζ y := by
  have hint : Integrable (kernelIntegrandFDeriv f p₀) :=
    ((integrable_weight hm).const_mul _).mono'
      (continuous_kernelIntegrandFDeriv hf p₀).aestronglyMeasurable
      (ae_of_all _ fun ζ ↦ norm_kernelIntegrandFDeriv_le_rpow hC0 hC hC' ζ p₀
        (Metric.mem_ball_self one_pos))
  rw [(hasFDerivAt_integral_kernelIntegrand hf hm hC0 hC hC').fderiv,
    ContinuousLinearMap.integral_apply hint]

end Generic

private lemma fourierInv_coefficient_eq (c : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    𝓕⁻ (fun ζ ↦ c.coefficient (p.1, (2 * π) • ζ)) p.2 =
      ∫ ζ, (𝐞 ⟪ζ, p.2⟫ : ℂ) • c.coefficient (p.1, (2 * π) • ζ) := by
  simp [Real.fourierInv_eq, Circle.smul_def]

/-- The phase times a frequency slice of a symbol of order `m < -n` is integrable. -/
private lemma integrable_kernelIntegrand {m' : ℝ} (c : Symbol n V W m') (hm : m' < -n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable fun ζ ↦ (𝐞 ⟪ζ, p.2⟫ : ℂ) • c.coefficient (p.1, (2 * π) • ζ) := by
  simpa [Circle.smul_def] using
    integrable_fourierChar_smul (c.integrable_coefficient_two_pi_smul hm p.1) p.2

/-- The kernel of a symbol of order `m < -n` is jointly continuous in the position and the
displacement. -/
private lemma continuous_fourierInv_coefficient (c : Symbol n V W m) (hm : m < -n) :
    Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕⁻ (fun ζ ↦ c.coefficient (p.1, (2 * π) • ζ)) p.2 := by
  simp only [fourierInv_coefficient_eq]
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨C, hC⟩ := c.exists_norm_coefficient_le (Metric.closedBall p₀.1 1)
    (isCompact_closedBall _ _)
  have hk := continuous_kernelIntegrand c.contDiff_coefficient.continuous
  refine continuousAt_of_dominated (bound := fun ζ ↦ C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2))
    (Filter.Eventually.of_forall fun p ↦
      (hk.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.mem_of_superset (Metric.ball_mem_nhds p₀ one_pos) fun p hp ↦ ae_of_all _ fun ζ ↦ ?_)
    ((integrable_weight hm).const_mul C)
    (ae_of_all _ fun ζ ↦ (hk.comp (continuous_id.prodMk continuous_const)).continuousAt)
  have hp : p.1 ∈ Metric.closedBall p₀.1 1 := Metric.mem_closedBall.2
    (((le_max_left _ _).trans_eq Prod.dist_eq.symm).trans (Metric.mem_ball.1 hp).le)
  rw [norm_smul, Circle.norm_coe, one_mul]
  exact hC _ hp _


/-- The real-linear map `ξ ↦ ⟪w, ξ⟫ • 1` of the frequency, whose symbol is that of `-i ∂_w`. -/
private def innerFrequency (w : CoordinateSpace n) : CoordinateSpace n →L[ℝ] (W →L[ℂ] W) :=
  (innerSL ℝ w).smulRight (ContinuousLinearMap.id ℂ W)

private lemma fderiv_fourierInv_coefficient_apply (c : Symbol n V W m)
    (hm : m + 1 < -n) (p y : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕⁻ (fun ζ ↦ c.coefficient (p.1, (2 * π) • ζ)) p.2) p y =
      ∑ j, y.1 j • 𝓕⁻ (fun ζ ↦ (spatialDeriv j c).coefficient (p.1, (2 * π) • ζ)) p.2 +
        Complex.I • 𝓕⁻ (fun ζ ↦
          ((ofFrequencyCLM (innerFrequency y.2)).comp c).coefficient (p.1, (2 * π) • ζ)) p.2 := by
  obtain ⟨C, hC0, hC⟩ := c.exists_bound_coefficient _ (isCompact_closedBall p.1 1)
  obtain ⟨C', hC'⟩ := c.exists_bound_fderiv_coefficient _ (isCompact_closedBall p.1 1)
  have hpt (ζ : CoordinateSpace n) : kernelIntegrandFDeriv c.coefficient p ζ y =
      ∑ j, y.1 j • ((𝐞 ⟪ζ, p.2⟫ : ℂ) • (spatialDeriv j c).coefficient (p.1, (2 * π) • ζ)) +
        Complex.I • ((𝐞 ⟪ζ, p.2⟫ : ℂ) •
          ((ofFrequencyCLM (innerFrequency y.2)).comp c).coefficient (p.1, (2 * π) • ζ)) := by
    rw [kernelIntegrandFDeriv_apply]
    congr 1
    · conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y.1]
      simp [map_sum, map_smul, fderiv_coefficient_single, Finset.smul_sum, smul_comm (y.1 _)]
    · simp only [coefficient_comp, coefficient_ofFrequencyCLM, innerFrequency,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_right,
        real_inner_comm ζ y.2, ContinuousLinearMap.smul_comp, ContinuousLinearMap.id_comp,
        smul_smul, ← Complex.coe_smul]
      congr 1
      push_cast
      ring
  simp only [fourierInv_coefficient_eq]
  have hc1 : ContDiff ℝ 1 c.coefficient := c.contDiff_coefficient.of_le (by simp)
  rw [fderiv_integral_kernelIntegrand_apply hc1 hm hC0 hC hC',
    integral_congr_ae (ae_of_all _ hpt), integral_add, integral_finsetSum]
  · simp only [integral_smul]
  · exact fun j _ ↦ (integrable_kernelIntegrand (spatialDeriv j c) (by linarith) p).smul (y.1 j)
  · exact integrable_finsetSum _ fun j _ ↦
      (integrable_kernelIntegrand (spatialDeriv j c) (by linarith) p).smul (y.1 j)
  · exact (integrable_kernelIntegrand ((ofFrequencyCLM (innerFrequency y.2)).comp c)
      (by linarith) p).smul Complex.I

/-- **Smoothness of the kernel of an operator of low order.** For a symbol `c` of order `m` with
`m + k < -n`, the kernel `k_c(x, z) = ∫ exp(2πi ⟪ζ, z⟫) c(x, 2πζ) dζ` is jointly `C^k` in the
position `x` and the displacement `z`. -/
theorem contDiff_fourierInv_coefficient (k : ℕ) {m : ℝ} (c : Symbol n V W m)
    (hm : m + k < -n) :
    ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕⁻ (fun ζ ↦ c.coefficient (p.1, (2 * π) • ζ)) p.2 := by
  induction k generalizing m with
  | zero => exact contDiff_zero.2 (continuous_fourierInv_coefficient c (by simpa using hm))
  | succ k ih =>
    have hm1 : m + 1 < -n := by push_cast at hm; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun p ↦ ?_, by simp, fun y ↦ ?_⟩
    · obtain ⟨C, hC0, hC⟩ := c.exists_bound_coefficient _ (isCompact_closedBall p.1 1)
      obtain ⟨C', hC'⟩ := c.exists_bound_fderiv_coefficient _ (isCompact_closedBall p.1 1)
      simp only [fourierInv_coefficient_eq]
      have hc1 : ContDiff ℝ 1 c.coefficient := c.contDiff_coefficient.of_le (by simp)
      exact (hasFDerivAt_integral_kernelIntegrand hc1 hm1 hC0 hC hC').differentiableAt
    simp only [fderiv_fourierInv_coefficient_apply c hm1]
    refine (ContDiff.sum fun j _ ↦ (ih (spatialDeriv j c) ?_).const_smul _).add
      ((ih _ ?_).const_smul _)
    · push_cast at hm
      linarith
    · push_cast at hm
      linarith

end Smoothness

section OffDiagonal

/-! ### The kernel off the diagonal -/

/-- **The Schwartz kernel of a quantization off the diagonal.** For a symbol `a` of order `m` and
`x ≠ y`, `offDiagonalKernel a x y = ‖x - y‖^(-2N) k(x, x - y)`, where `N = ⌊(m + n) / 2⌋₊ + 1` and
`k(x, z) = ∫ exp(2πi ⟪ζ, z⟫) ((-Δ_ξ)^N a)(x, 2πζ) dζ` is the absolutely convergent kernel of the
symbol `(-Δ_ξ)^N a` of order `m - 2N < -n`. Every `N` with `m - 2N < -n` gives the same value
(`TauCeti.Symbol.offDiagonalKernel_eq`). It represents `Op(a)` away from the support of the input
(`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`) and is smooth off the
diagonal (`TauCeti.Symbol.contDiffOn_offDiagonalKernel`). On the diagonal the formula gives `0`;
there the Schwartz kernel is in general not a function. -/
def offDiagonalKernel (a : Symbol n V W m) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  ((‖x - y‖ ^ 2)⁻¹ ^ (⌊(m + n) / 2⌋₊ + 1)) •
    𝓕⁻ (fun ζ ↦ (negFrequencyLaplacianPow (⌊(m + n) / 2⌋₊ + 1) a).coefficient
      (x, (2 * π) • ζ)) (x - y)

private lemma order_sub_two_mul_floor_lt (m : ℝ) (n k : ℕ) :
    m - 2 * ((⌊(m + n + k) / 2⌋₊ + 1 : ℕ) : ℝ) + k < -n := by
  have := Nat.lt_floor_add_one ((m + n + k) / 2)
  push_cast
  linarith

/-- One more application of `-Δ_ξ`, compensated by one more factor `‖z‖⁻²`, does not change the
kernel. -/
private lemma inv_norm_sq_pow_smul_fourierInv_succ (a : Symbol n V W m) {N : ℕ}
    (hN : m - 2 * N < -n) (x : CoordinateSpace n) {z : CoordinateSpace n} (hz : z ≠ 0) :
    ((‖z‖ ^ 2)⁻¹ ^ (N + 1)) •
        𝓕⁻ (fun ζ ↦ (negFrequencyLaplacianPow (N + 1) a).coefficient (x, (2 * π) • ζ)) z =
      ((‖z‖ ^ 2)⁻¹ ^ N) •
        𝓕⁻ (fun ζ ↦ (negFrequencyLaplacianPow N a).coefficient (x, (2 * π) • ζ)) z := by
  simp only [coefficient_negFrequencyLaplacianPow_succ]
  rw [fourierInv_coefficient_neg_frequencyLaplacian _ hN, smul_smul, pow_succ, mul_assoc,
    inv_mul_cancel₀ (by positivity), mul_one]

/-- The off-diagonal kernel can be computed with any number `N` of applications of `-Δ_ξ` for
which `m - 2N < -n`. -/
theorem offDiagonalKernel_eq (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = ((‖x - y‖ ^ 2)⁻¹ ^ N) •
      𝓕⁻ (fun ζ ↦ (negFrequencyLaplacianPow N a).coefficient (x, (2 * π) • ζ)) (x - y) := by
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  set F : ℕ → V →L[ℂ] W := fun N ↦ ((‖x - y‖ ^ 2)⁻¹ ^ N) •
    𝓕⁻ (fun ζ ↦ (negFrequencyLaplacianPow N a).coefficient (x, (2 * π) • ζ)) (x - y)
  -- `F` is constant on the admissible values of `N`
  have hmono {N₁ N₂ : ℕ} (h₁ : m - 2 * N₁ < -n) (h : N₁ ≤ N₂) : F N₂ = F N₁ := by
    induction N₂, h using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      have hk' : m - 2 * k < -n := by
        have : (N₁ : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      exact (inv_norm_sq_pow_smul_fourierInv_succ a hk' x hz).trans ih
  have h₀ : m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
    simpa using order_sub_two_mul_floor_lt m n 0
  change F (⌊(m + n) / 2⌋₊ + 1) = F N
  rcases le_total N (⌊(m + n) / 2⌋₊ + 1) with h | h
  · exact hmono hN h
  · exact (hmono h₀ h).symm

/-- **The kernel is smooth off the diagonal.** The off-diagonal kernel of a symbol is smooth on
the complement of the diagonal `{(x, y) | x ≠ y}`. -/
theorem contDiffOn_offDiagonalKernel (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦ offDiagonalKernel a p.1 p.2)
      {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  set N := ⌊(m + n + k) / 2⌋₊ + 1
  have hNk : m - 2 * N + k < -n := order_sub_two_mul_floor_lt m n k
  have hN : m - 2 * N < -n := by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hK := (contDiff_fourierInv_coefficient k (negFrequencyLaplacianPow N a) hNk).comp
    (contDiff_fst.prodMk (contDiff_fst.sub contDiff_snd) :
      ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦ (p.1, p.1 - p.2))
  have hw : ContDiffOn ℝ k (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (‖p.1 - p.2‖ ^ 2)⁻¹ ^ N) {p | p.1 ≠ p.2} :=
    (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).contDiffOn.inv
      fun p hp ↦ by simpa [sub_eq_zero] using hp).pow N
  exact (hw.smul hK.contDiffOn).congr fun p hp ↦ offDiagonalKernel_eq a hN hp

/-- Iterated multiplication of a Schwartz function by a temperate function. -/
private lemma iterate_smulLeftCLM_apply {h : CoordinateSpace n → ℝ} (hh : h.HasTemperateGrowth)
    (N : ℕ) (w : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n) :
    ((SchwartzMap.smulLeftCLM V h)^[N] w) y = (h y ^ N) • w y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', SchwartzMap.smulLeftCLM_apply_apply hh, ih, smul_smul,
      pow_succ']

/-- **The kernel represents the quantization away from the input.** For a compactly supported
Schwartz function `u` whose support does not contain `x`,
`Op(a) u (x) = ∫ K_a(x, y) u(y) dy`, with `K_a = offDiagonalKernel a`. -/
theorem quantizeSchwartzValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ y, offDiagonalKernel a x y (u y) := by
  have hN : m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
    simpa using order_sub_two_mul_floor_lt m n 0
  set N := ⌊(m + n) / 2⌋₊ + 1
  set g : CoordinateSpace n → ℝ := fun y ↦ (‖y - x‖ ^ 2)⁻¹ ^ N
  have hg {y : CoordinateSpace n} (hy : y ≠ x) : ContDiffAt ℝ ∞ g y :=
    ((((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt).inv
      (by simpa [sub_eq_zero] using hy)).pow N
  have hux : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have hsmooth : ContDiff ℝ ∞ fun y ↦ g y • u y := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    rcases eq_or_ne y x with rfl | hy
    · refine contDiffAt_const (c := (0 : V)).congr_of_eventuallyEq ?_
      filter_upwards [hux] with z hz
      simp [hz]
    · exact (hg hy).smul (u.smooth ⊤).contDiffAt
  have hsupp : HasCompactSupport fun y ↦ g y • u y := hu.smul_left
  set v := hsupp.toSchwartzMap hsmooth
  have hne {y : CoordinateSpace n} (hy : u y ≠ 0) : y ≠ x := by
    rintro rfl
    exact hx (subset_tsupport _ hy)
  have hW : (SchwartzMap.smulLeftCLM V (fun y ↦ ‖y - x‖ ^ 2))^[N] v = u := by
    ext y
    have h₁ : (fun y : CoordinateSpace n ↦ ‖y - x‖ ^ 2).HasTemperateGrowth :=
      (Function.hasTemperateGrowth_norm_sq (CoordinateSpace n)).comp (f := (· - x)) (by fun_prop)
    rw [iterate_smulLeftCLM_apply h₁, HasCompactSupport.toSchwartzMap_toFun, smul_smul]
    rcases eq_or_ne (u y) 0 with hy | hy
    · simp [hy]
    · have : ‖y - x‖ ^ 2 ≠ 0 := by simpa [sub_eq_zero] using hne hy
      rw [show (‖y - x‖ ^ 2) ^ N * g y = 1 by simp [g, this], one_smul]
  obtain ⟨C, hC⟩ := (negFrequencyLaplacianPow N a).exists_norm_coefficient_le {x}
    isCompact_singleton
  conv_lhs => rw [← hW]
  rw [quantizeSchwartzValue_iterate_smulLeftCLM_norm_sub_sq,
    quantizeSchwartzValue_eq_integral_fourierInv
      ((negFrequencyLaplacianPow N a).continuous_coefficient_slice x).aestronglyMeasurable
      (hC x rfl) (by simpa using hN)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [HasCompactSupport.toSchwartzMap_toFun]
  rcases eq_or_ne (u y) 0 with hy | hy
  · simp [hy]
  · rw [offDiagonalKernel_eq a hN (hne hy).symm, smul_apply,
      ContinuousLinearMap.map_smul_of_tower, norm_sub_rev]

theorem offDiagonalKernel_add (a b : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (a + b) x y = offDiagonalKernel a x y + offDiagonalKernel b x y := by
  have hN : m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
    simpa using order_sub_two_mul_floor_lt m n 0
  simp only [offDiagonalKernel, map_add, coefficient_add, Pi.add_apply, Real.fourierInv_eq,
    Circle.smul_def, smul_add]
  rw [integral_add, smul_add]
  · simpa [Circle.smul_def] using integrable_fourierChar_smul
      ((negFrequencyLaplacianPow _ a).integrable_coefficient_two_pi_smul hN x) (x - y)
  · simpa [Circle.smul_def] using integrable_fourierChar_smul
      ((negFrequencyLaplacianPow _ b).integrable_coefficient_two_pi_smul hN x) (x - y)

theorem offDiagonalKernel_smul (c : ℂ) (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (c • a) x y = c • offDiagonalKernel a x y := by
  simp only [offDiagonalKernel, map_smul, coefficient_smul, Pi.smul_apply, Real.fourierInv_eq,
    smul_comm _ c, integral_smul]

/-- A constant symbol, such as the symbol `1` of the identity, has no kernel off the diagonal. -/
@[simp]
theorem offDiagonalKernel_const (T : V →L[ℂ] W) (x y : CoordinateSpace n) :
    offDiagonalKernel (const T : Symbol n V W 0) x y = 0 := by
  simp only [offDiagonalKernel, negFrequencyLaplacianPow_succ_const, coefficient_zero,
    Pi.zero_apply, Real.fourierInv_eq, Circle.smul_def, smul_zero, integral_zero]

end OffDiagonal

end Symbol

end TauCeti
