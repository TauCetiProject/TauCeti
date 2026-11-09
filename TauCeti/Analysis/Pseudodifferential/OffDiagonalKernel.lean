/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The kernel of a pseudodifferential operator off the diagonal

For a symbol `a` of order `m` on `ℝⁿ`, the Schwartz kernel of its Kohn–Nirenberg quantization,
`K_a(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`, is an absolutely convergent integral only when
`m < -n`; in general it is a distribution. Away from the diagonal it is nevertheless a function.
This file proves this by repeated integration by parts in the frequency.

Multiplying the input by the displacement `⟪x - y, v⟫` and evaluating `Op(a)` at `x` amounts to
replacing the symbol by `i ∂_{ξ, v} a`, a symbol of one order lower
(`TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub`). Summing over the coordinates, multiplying
by `‖x - y‖ ^ (2N)` replaces `a` by `(-Δ_ξ)^N a`
(`TauCeti.Symbol.quantizeSchwartzValue_smulLeftCLM_norm_sub_pow`). Once `m - 2N < -n`, the symbol
`Δ_ξ^N a` has an absolutely convergent kernel, so for an input `u` vanishing near `x`,
dividing `u` by `‖x - y‖ ^ (2N)` gives

`Op(a) u (x) = ∫ (-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y) u(y) dy`.

This defines the off-diagonal kernel `TauCeti.Symbol.offDiagonalKernel a`. It does not depend on
`N`, because `K_{Δ_ξ b} = -‖x - y‖² K_b` for symbols `b` of order below `-n`
(`TauCeti.Symbol.quantizationKernel_frequencyLaplacian`), and for `m < -n` it is the absolutely
convergent kernel itself.

## Main results

* `TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub`: `Op(a) (⟪x - ·, v⟫ u) (x) = i Op(a') u (x)`
  when `a'` is the frequency derivative of `a` along `v`.
* `TauCeti.Symbol.quantizeSchwartzValue_smulLeftCLM_norm_sub_pow`:
  `Op(a) (‖x - ·‖^(2N) u) (x) = (-1)^N Op(Δ_ξ^N a) u (x)`.
* `TauCeti.Symbol.offDiagonalKernel_eq`: the off-diagonal kernel is
  `(-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y)` for every `N` with `m - 2N < -n`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K(x, y) u(y) dy` for compactly supported `u` vanishing near `x`.
* `TauCeti.Symbol.continuousOn_offDiagonalKernel`: the kernel is continuous off the diagonal.
* `TauCeti.Symbol.exists_norm_offDiagonalKernel_le`: `‖K(x, y)‖ ≤ C ‖x - y‖^(-2N)` for `x` in a
  compact set, for every `N` with `m - 2N < -n`; in particular the kernel decays faster than any
  power of `‖x - y‖` as `y → ∞`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff LineDeriv
open MeasureTheory Real FourierTransform Module

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Integration by parts in the frequency -/

/-- **Multiplication by the displacement.** If `ξ ↦ a(x, ξ)` has line derivative `a'(x, ξ)` along
`v`, and both have growth bounds at `x`, then multiplying the input by `⟪x - y, v⟫` and evaluating
the quantization at `x` replaces `a` by `i a'`:
`Op(a) (⟪x - ·, v⟫ u) (x) = i Op(a') u (x)`. In terms of `D = -i ∂`, the coefficient becomes
`-D_{ξ, v} a`, as for the kernel in `TauCeti.inner_smul_quantizationKernel`. -/
theorem quantizeSchwartzValue_smulLeftCLM_inner_sub {a a' : E × E → V →L[ℂ] W} {x v : E}
    {C C' m m' : ℝ} (hda : ∀ ξ, HasLineDerivAt ℝ (fun ξ ↦ a (x, ξ)) (a' (x, ξ)) ξ v)
    (hmeas : AEStronglyMeasurable (fun ξ ↦ a (x, ξ)))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (hmeas' : AEStronglyMeasurable (fun ξ ↦ a' (x, ξ)))
    (hC' : ∀ ξ, ‖a' (x, ξ)‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2)) (u : 𝓢(E, V)) :
    quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪x - y, v⟫) u) x =
      Complex.I • quantizeSchwartzValue a' u x := by
  -- On the Fourier side the input `⟪x - ·, v⟫ u` becomes `-(i / 2π) G` with `G = c F + ∂_v F`,
  -- where `F = 𝓕 u` and `c = 2πi ⟪x, v⟫`, and `𝐞 ⟪ζ, x⟫ G ζ` is the line derivative of
  -- `𝐞 ⟪ζ, x⟫ F ζ` along `v`. Integrating by parts moves this derivative onto `a(x, 2πζ)`, whose
  -- line derivative is `2π a'(x, 2πζ)`, and the constants combine to `i`.
  set F := 𝓕 u
  set c : ℂ := 2 * π * Complex.I * ⟪x, v⟫
  set G : 𝓢(E, V) := c • F + ∂_{v} F
  -- The character `ζ ↦ 𝐞 ⟪ζ, x⟫` has line derivative `c 𝐞 ⟪ζ, x⟫` along `v`.
  have he (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) (c * 𝐞 ⟪ζ, x⟫) ζ v := by
    convert (Real.differentiable_fourierChar_neg_bilinear_left (innerSL ℝ) (-x)
      ζ).hasFDerivAt.hasLineDerivAt v using 1
    · simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg]
    · rw [Real.fderiv_fourierChar_neg_bilinear_left_apply]
      simp only [innerSL_apply_apply ℝ, inner_neg_right, neg_neg, Complex.ofReal_neg, c,
        real_inner_comm x v]
      ring
  have hg (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • F ζ) (𝐞 ⟪ζ, x⟫ • G ζ) ζ v := by
    have hF : HasLineDerivAt ℝ F (∂_{v} F ζ) ζ v := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      exact (F.differentiableAt).hasFDerivAt.hasLineDerivAt v
    have h : HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ) • F ζ)
        ((𝐞 ⟪ζ, x⟫ : ℂ) • ∂_{v} F ζ + (c * 𝐞 ⟪ζ, x⟫) • F ζ) ζ v := by
      have := HasDerivAt.smul (he ζ) hF
      simp only [zero_smul, add_zero] at this
      exact this
    simp only [Circle.smul_def]
    convert h using 1
    simp only [G, add_apply, smul_apply, smul_add, smul_smul, mul_comm c]
    rw [add_comm]
  have hf (ζ : E) : HasLineDerivAt ℝ (fun ζ ↦ a (x, (2 * π) • ζ))
      ((2 * π) • a' (x, (2 * π) • ζ)) ζ v := by
    simpa only [HasLineDerivAt, smul_add, smul_comm (2 * π) _ v] using
      (hda ((2 * π) • ζ)).smul (2 * π)
  -- Integration by parts for the evaluation pairing, with integrands as in
  -- `integrable_quantizeSchwartzValue_integrand`.
  have hB (T : V →L[ℂ] W) (w : V) :
      ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ T w = T w := rfl
  have hint (b : E × E → V →L[ℂ] W) (f : 𝓢(E, V)) :
      (fun ζ ↦ b (x, (2 * π) • ζ) (𝐞 ⟪ζ, x⟫ • f ζ)) =
        fun ζ ↦ 𝐞 ⟪ζ, x⟫ • b (x, (2 * π) • ζ) (f ζ) := by
    funext ζ
    simp only [Circle.smul_def, map_smul]
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ)
    (f := fun ζ ↦ a (x, (2 * π) • ζ)) (f' := fun ζ ↦ (2 * π) • a' (x, (2 * π) • ζ))
    (g := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • F ζ) (g' := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • G ζ)
    (((integrable_quantizeSchwartzValue_integrand hmeas' hC' F).smul (2 * π)).congr
      (ae_of_all _ fun ζ ↦ by simp only [Pi.smul_apply, hB, smul_apply, Circle.smul_def,
        map_smul, smul_comm (2 * π)]))
    (by
      simp only [hB, hint a]
      exact integrable_quantizeSchwartzValue_integrand hmeas hC G)
    (by
      simp only [hB, hint a]
      exact integrable_quantizeSchwartzValue_integrand hmeas hC F)
    (fun ζ _ ↦ hf ζ) (fun ζ _ ↦ hg ζ)
  simp only [hB, smul_apply, hint] at hparts
  -- Both sides of `hparts` are multiples of the two quantizations.
  have hL : quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪x - y, v⟫) u) x =
      (-(Complex.I / (2 * π))) • ∫ ζ, 𝐞 ⟪ζ, x⟫ • a (x, (2 * π) • ζ) (G ζ) := by
    rw [quantizeSchwartzValue_def, SchwartzMap.fourier_smulLeftCLM_inner_sub, ← integral_smul]
    congr 1 with ζ
    simp only [smul_apply, map_smul, smul_comm (𝐞 _)]
    rfl
  have hR : ∫ ζ, (2 * π) • a' (x, (2 * π) • ζ) (𝐞 ⟪ζ, x⟫ • F ζ) =
      ((2 * π : ℝ) : ℂ) • quantizeSchwartzValue a' u x := by
    rw [Complex.coe_smul, quantizeSchwartzValue_def, ← integral_smul]
    congr 1 with ζ
    simp only [Circle.smul_def, map_smul]
    rfl
  rw [hL, hparts, hR, smul_neg, smul_smul, ← neg_smul]
  congr 1
  push_cast
  field_simp

namespace Symbol

/-! ### Symbols -/

variable {n : ℕ} {m : ℝ}

/-- A growth bound for the frequency slice of a symbol at a single position. -/
private lemma exists_bound_slice (a : Symbol n V W m) (x : CoordinateSpace n) :
    ∃ C, ∀ ξ, ‖a.coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient {x} isCompact_singleton
  exact ⟨C, hC x rfl⟩

private lemma quantizeSchwartzValue_sum_right {ι : Type*} (a : Symbol n V W m) (s : Finset ι)
    (u : ι → 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (∑ i ∈ s, u i) x =
      ∑ i ∈ s, quantizeSchwartzValue a.coefficient (u i) x := by
  classical
  obtain ⟨C, hC⟩ := a.exists_bound_slice x
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, quantizeSchwartzValue_add_right
      (a.continuous_coefficient_slice x).aestronglyMeasurable hC, ih]

private lemma quantizeSchwartzValue_sum_left {ι : Type*} (s : Finset ι) (a : ι → Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (∑ i ∈ s, a i).coefficient u x =
      ∑ i ∈ s, quantizeSchwartzValue (a i).coefficient u x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨C, hC⟩ := (a i).exists_bound_slice x
    obtain ⟨C', hC'⟩ := (∑ i ∈ s, a i).exists_bound_slice x
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefficient_add,
      quantizeSchwartzValue_add_left ((a i).continuous_coefficient_slice x).aestronglyMeasurable
        hC ((∑ i ∈ s, a i).continuous_coefficient_slice x).aestronglyMeasurable hC', ih]

/-- **Multiplication by a coordinate of the displacement.** Multiplying the input by
`(x - y)_j` and evaluating the quantization at `x` replaces the symbol by `i ∂_{ξ_j} a`. -/
theorem quantizeSchwartzValue_smulLeftCLM_coord_sub (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ (x - y) j) u) x =
      Complex.I • quantizeSchwartzValue (frequencyDeriv j a).coefficient u x := by
  have h : (fun y : CoordinateSpace n ↦ (x - y) j) =
      fun y ↦ ⟪x - y, EuclideanSpace.single j (1 : ℝ)⟫ := by
    funext y
    simp [EuclideanSpace.inner_single_right]
  obtain ⟨C, hC⟩ := a.exists_bound_slice x
  obtain ⟨C', hC'⟩ := (frequencyDeriv j a).exists_bound_slice x
  rw [h]
  exact quantizeSchwartzValue_smulLeftCLM_inner_sub (a.hasLineDerivAt_coefficient_single j x)
    (a.continuous_coefficient_slice x).aestronglyMeasurable hC
    ((frequencyDeriv j a).continuous_coefficient_slice x).aestronglyMeasurable hC' u

private lemma hasTemperateGrowth_norm_sub_pow (x : CoordinateSpace n) (N : ℕ) :
    (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ (2 * N)).HasTemperateGrowth := by
  have h : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ (2 * N)) =
      ((fun z : CoordinateSpace n ↦ ‖z‖ ^ 2) ∘ fun y ↦ x - y) ^ N := by
    funext y
    simp [pow_mul]
  rw [h]
  exact Function.HasTemperateGrowth.pow
    ((Function.hasTemperateGrowth_norm_sq _).comp (by fun_prop)) N

/-- **Multiplication by the squared distance.** Multiplying the input by `‖x - y‖²` and
evaluating the quantization at `x` replaces the symbol by `-Δ_ξ a`. -/
theorem quantizeSchwartzValue_smulLeftCLM_norm_sub_sq (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ ‖x - y‖ ^ 2) u) x =
      -quantizeSchwartzValue (frequencyLaplacian a).coefficient u x := by
  have hsq : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ 2) =
      fun y ↦ ∑ j, ((fun y : CoordinateSpace n ↦ (x - y) j) * fun y ↦ (x - y) j) y := by
    funext y
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [sq]
  have htg (j : Fin n) : (fun y : CoordinateSpace n ↦ (x - y) j).HasTemperateGrowth := by
    have h : (fun y : CoordinateSpace n ↦ (x - y) j) =
        fun y ↦ ⟪x - y, EuclideanSpace.single j (1 : ℝ)⟫ := by
      funext y
      simp [EuclideanSpace.inner_single_right]
    rw [h]
    fun_prop
  rw [hsq, SchwartzMap.smulLeftCLM_sum fun j _ ↦ (htg j).mul (htg j), sum_apply,
    quantizeSchwartzValue_sum_right, frequencyLaplacian_eq_sum, quantizeSchwartzValue_sum_left,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← SchwartzMap.smulLeftCLM_smulLeftCLM_apply (htg j) (htg j),
    quantizeSchwartzValue_smulLeftCLM_coord_sub,
    quantizeSchwartzValue_smulLeftCLM_coord_sub, coefficient_inclusion, smul_smul,
    Complex.I_mul_I, neg_one_smul]

/-- **Multiplication by a power of the squared distance.** Multiplying the input by
`‖x - y‖ ^ (2N)` and evaluating the quantization at `x` replaces the symbol by `(-Δ_ξ)^N a`. -/
theorem quantizeSchwartzValue_smulLeftCLM_norm_sub_pow (N : ℕ) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ ‖x - y‖ ^ (2 * N)) u) x =
      (-1 : ℝ) ^ N • quantizeSchwartzValue (frequencyLaplacianPow N a).coefficient u x := by
  induction N generalizing m with
  | zero =>
    simp
  | succ N ih =>
    have h : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ (2 * (N + 1))) =
        (fun y ↦ ‖x - y‖ ^ 2) * fun y ↦ ‖x - y‖ ^ (2 * N) := by
      funext y
      simp only [Pi.mul_apply]
      ring
    have hc : quantizeSchwartzValue (frequencyLaplacianPow (N + 1) a).coefficient u x =
        quantizeSchwartzValue (frequencyLaplacianPow N (frequencyLaplacian a)).coefficient u x :=
      by rw [coefficient_frequencyLaplacianPow_succ]
    have h2 : (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ 2).HasTemperateGrowth := by
      simpa using hasTemperateGrowth_norm_sub_pow x 1
    rw [h, ← SchwartzMap.smulLeftCLM_smulLeftCLM_apply h2 (hasTemperateGrowth_norm_sub_pow x N),
      quantizeSchwartzValue_smulLeftCLM_norm_sub_sq, ih, hc, pow_succ, mul_smul, neg_one_smul,
      smul_neg]

private lemma quantizationKernel_sum {ι : Type*} (s : Finset ι) (b : ι → Symbol n V W m)
    (hm : m < -n) (x y : CoordinateSpace n) :
    quantizationKernel (∑ i ∈ s, b i).coefficient x y =
      ∑ i ∈ s, quantizationKernel (b i).coefficient x y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coefficient_add,
      quantizationKernel_add ((b i).integrable_coefficient hm x)
        ((∑ i ∈ s, b i).integrable_coefficient hm x), ih]

/-- **Kernel of the frequency Laplacian.** For a symbol of order `m < -n`,
`K_{Δ_ξ a}(x, y) = -‖x - y‖² K_a(x, y)`. -/
theorem quantizationKernel_frequencyLaplacian (a : Symbol n V W m) (hm : m < -n)
    (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacian a).coefficient x y =
      (-‖x - y‖ ^ 2) • quantizationKernel a.coefficient x y := by
  rw [frequencyLaplacian_eq_sum, quantizationKernel_sum _ _ (by linarith)]
  simp only [coefficient_inclusion]
  simp_rw [quantizationKernel_frequencyDeriv _ (by linarith : m - 1 < -n),
    quantizationKernel_frequencyDeriv _ hm, smul_smul, ← Finset.sum_smul]
  rw [← Complex.coe_smul]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination (((x - y) j : ℂ)) ^ 2 * Complex.I_sq

/-- Iterating `TauCeti.Symbol.quantizationKernel_frequencyLaplacian`: once `m - 2N < -n`,
`K_{Δ_ξ^(N + k) a}(x, y) = (-‖x - y‖²)^k K_{Δ_ξ^N a}(x, y)`. -/
theorem quantizationKernel_frequencyLaplacianPow_add (a : Symbol n V W m) {N : ℕ}
    (hN : m - 2 * N < -n) (k : ℕ) (x y : CoordinateSpace n) :
    quantizationKernel (frequencyLaplacianPow (N + k) a).coefficient x y =
      (-‖x - y‖ ^ 2) ^ k • quantizationKernel (frequencyLaplacianPow N a).coefficient x y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, coefficient_frequencyLaplacianPow_succ',
      quantizationKernel_frequencyLaplacian _ (by push_cast; linarith), ih, smul_smul,
      pow_succ (-‖x - y‖ ^ 2) k, mul_comm]

private lemma sub_two_mul_floor_lt (m : ℝ) (n : ℕ) :
    m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
  have := Nat.lt_floor_add_one ((m + n) / 2)
  push_cast
  linarith

/-- The Schwartz kernel of the quantization of a symbol of order `m`, off the diagonal:
`(-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y)` with `N = ⌊(m + n) / 2⌋₊ + 1`, so that `m - 2N < -n`.
It does not depend on this choice of `N` (`TauCeti.Symbol.offDiagonalKernel_eq`), and it has the
junk value `0` on the diagonal. -/
def offDiagonalKernel (a : Symbol n V W m) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  ((-1) ^ (⌊(m + n) / 2⌋₊ + 1) / ‖x - y‖ ^ (2 * (⌊(m + n) / 2⌋₊ + 1))) •
    quantizationKernel (frequencyLaplacianPow (⌊(m + n) / 2⌋₊ + 1) a).coefficient x y

/-- The off-diagonal kernel vanishes on the diagonal by convention. -/
@[simp]
theorem offDiagonalKernel_self (a : Symbol n V W m) (x : CoordinateSpace n) :
    offDiagonalKernel a x x = 0 := by
  simp [offDiagonalKernel]

/-- **Independence of the exponent.** Off the diagonal, for every `N` with `m - 2N < -n`,
the kernel is `(-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y)`. -/
theorem offDiagonalKernel_eq (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = ((-1) ^ N / ‖x - y‖ ^ (2 * N)) •
      quantizationKernel (frequencyLaplacianPow N a).coefficient x y := by
  have hr : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
  have key (N : ℕ) (hN : m - 2 * N < -n) (k : ℕ) :
      ((-1) ^ (N + k) / ‖x - y‖ ^ (2 * (N + k))) •
          quantizationKernel (frequencyLaplacianPow (N + k) a).coefficient x y =
        ((-1) ^ N / ‖x - y‖ ^ (2 * N)) •
          quantizationKernel (frequencyLaplacianPow N a).coefficient x y := by
    rw [quantizationKernel_frequencyLaplacianPow_add a hN k, smul_smul]
    congr 1
    have h1 : ((-1 : ℝ)) ^ (N + k) * (-1) ^ k = (-1) ^ N := by
      rw [pow_add, mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
    rw [neg_pow, ← h1]
    field_simp
    ring
  rw [offDiagonalKernel, ← key _ (sub_two_mul_floor_lt m n) N, add_comm, key _ hN]

/-- For a symbol of order `m < -n`, the off-diagonal kernel is the absolutely convergent kernel
`TauCeti.quantizationKernel`. -/
theorem offDiagonalKernel_eq_quantizationKernel (a : Symbol n V W m) (hm : m < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  rw [offDiagonalKernel_eq a (N := 0) (by simpa using hm) hxy]
  simp

/-- **Kernel representation off the diagonal.** If a compactly supported Schwartz function `u`
vanishes near `x`, then `Op(a) u (x) = ∫ K(x, y) u(y) dy` with the off-diagonal kernel `K`. -/
theorem quantizeSchwartzValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ y, offDiagonalKernel a x y (u y) := by
  set N := ⌊(m + n) / 2⌋₊ + 1
  -- Divide `u` by `‖x - y‖ ^ (2N)`; the quotient `w` is smooth since `u` vanishes near `x`.
  set g : CoordinateSpace n → ℝ := fun y ↦ (‖x - y‖ ^ (2 * N))⁻¹
  have hwc : ContDiff ℝ ∞ (fun y ↦ g y • u y) := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ tsupport u
    · have hxy : x - y ≠ 0 := sub_ne_zero.2 fun h ↦ hx (h ▸ hy)
      have hd : ContDiffAt ℝ ∞ (fun y : CoordinateSpace n ↦ ‖x - y‖ ^ (2 * N)) y :=
        (hasTemperateGrowth_norm_sub_pow x N).1.contDiffAt
      exact (hd.inv (pow_ne_zero _ (norm_ne_zero_iff.2 hxy))).smul (u.smooth ⊤).contDiffAt
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
      simp [hz]
  have hws : HasCompactSupport (fun y ↦ g y • u y) := hu.smul_left
  set w := hws.toSchwartzMap hwc
  have hu_eq : SchwartzMap.smulLeftCLM V (fun y ↦ ‖x - y‖ ^ (2 * N)) w = u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_norm_sub_pow x N),
      HasCompactSupport.toSchwartzMap_toFun, smul_smul]
    by_cases hy : y = x
    · subst hy
      simp [image_eq_zero_of_notMem_tsupport hx]
    · rw [mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hy)))),
        one_smul]
  conv_lhs => rw [← hu_eq]
  rw [quantizeSchwartzValue_smulLeftCLM_norm_sub_pow,
    quantizeSchwartzValue_eq_integral_quantizationKernel
      ((frequencyLaplacianPow N a).integrable_coefficient (sub_two_mul_floor_lt m n) x),
    ← integral_smul]
  congr 1 with y
  rw [offDiagonalKernel, smul_apply, HasCompactSupport.toSchwartzMap_toFun,
    ContinuousLinearMap.map_smul_of_tower, smul_smul, div_eq_mul_inv]

/-- **Continuity off the diagonal.** The off-diagonal kernel is continuous on `{(x, y) | x ≠ y}`. -/
theorem continuousOn_offDiagonalKernel (a : Symbol n V W m) :
    ContinuousOn (Function.uncurry (offDiagonalKernel a)) {p | p.1 ≠ p.2} := by
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hK := (frequencyLaplacianPow N a).continuous_quantizationKernel (sub_two_mul_floor_lt m n)
  have hs : ContinuousOn (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (-1) ^ N / ‖p.1 - p.2‖ ^ (2 * N)) {p | p.1 ≠ p.2} :=
    continuousOn_const.div (by fun_prop) fun p hp ↦
      pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))
  exact hs.smul hK.continuousOn

/-- **Decay off the diagonal.** For every `N` with `m - 2N < -n` and every compact set `K` of
positions, `‖K(x, y)‖ ≤ C ‖x - y‖^(-2N)` for `x ∈ K` and all `y`. -/
theorem exists_norm_offDiagonalKernel_le (a : Symbol n V W m) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) {N : ℕ} (hN : m - 2 * N < -n) :
    ∃ C, ∀ x ∈ K, ∀ y, ‖offDiagonalKernel a x y‖ ≤ C / ‖x - y‖ ^ (2 * N) := by
  set b := frequencyLaplacianPow N a
  obtain ⟨C, hC0, hC⟩ := b.exists_bound_coefficient K hK
  have hweight : Integrable (fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ ((m - 2 * N) / 2)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (CoordinateSpace n)))
      (r := -(m - 2 * N)) (by simp only [finrank_euclideanSpace_fin]; linarith)
    simpa only [neg_neg, neg_div] using h
  set I := ∫ ξ : CoordinateSpace n, (1 + ‖ξ‖ ^ 2) ^ ((m - 2 * N) / 2)
  refine ⟨((2 * π) ^ n)⁻¹ * (C * I), fun x hx y ↦ ?_⟩
  have hD : 0 ≤ ((2 * π) ^ n)⁻¹ * (C * I) :=
    mul_nonneg (by positivity) (mul_nonneg hC0 (integral_nonneg fun _ ↦ by positivity))
  rcases eq_or_ne x y with rfl | hxy
  · rw [offDiagonalKernel_self, norm_zero]
    exact div_nonneg hD (by positivity)
  have hint : ∫ ξ, ‖b.coefficient (x, ξ)‖ ≤ C * I := by
    rw [← integral_const_mul]
    exact integral_mono (b.integrable_coefficient hN x).norm (hweight.const_mul C) (hC x hx)
  have hk := norm_quantizationKernel_le b.coefficient x y
  rw [finrank_euclideanSpace_fin] at hk
  rw [offDiagonalKernel_eq a hN hxy, norm_smul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    norm_pow, norm_norm, div_mul_eq_mul_div, one_mul]
  gcongr
  exact hk.trans (mul_le_mul_of_nonneg_left hint (by positivity))

end Symbol

end TauCeti
