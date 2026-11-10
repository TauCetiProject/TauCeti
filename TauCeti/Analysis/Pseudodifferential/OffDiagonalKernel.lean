/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# The kernel of a pseudodifferential operator off the diagonal

For a symbol `a` of order `m` on `ℝⁿ`, the Schwartz kernel of its Kohn–Nirenberg quantization,
`K_a(x, y) = (2π)⁻ⁿ ∫ exp(i ⟪x - y, ξ⟫) a(x, ξ) dξ`, is an absolutely convergent integral only when
`m < -n`; in general it is a distribution. Away from the diagonal it is nevertheless a function.
This file proves this by repeated integration by parts in the frequency.

Multiplying the input by the displacement `⟪x - y, v⟫` and evaluating `Op(a)` at `x` amounts to
replacing the symbol by `i ∂_{ξ, v} a`, a symbol of one order lower
(`TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub`, a rearrangement of the integration by parts
`TauCeti.inner_smul_quantizeSchwartzValue`). Summing over the coordinates, multiplying
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

* `TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub`:
  `Op(a) (⟪x - ·, v⟫ u) (x) = i Op(∂_{ξ, v} a) u (x)`.
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

/-- **Multiplication by the displacement.** If `ξ ↦ a(x, ξ)` is `C¹`, and it and its frequency
derivative `∂_{ξ, v} a` in the direction `v` have growth bounds at `x`, then multiplying the input
by `⟪x - y, v⟫` and evaluating the quantization at `x` replaces `a` by `i ∂_{ξ, v} a`:
`Op(a) (⟪x - ·, v⟫ u) (x) = i Op(∂_{ξ, v} a) u (x)`. In terms of `D = -i ∂`, the coefficient
becomes `-D_{ξ, v} a`, as for the kernel in `TauCeti.inner_smul_quantizationKernel`. -/
theorem quantizeSchwartzValue_smulLeftCLM_inner_sub {a : E × E → V →L[ℂ] W} {x : E}
    {C C' m m' : ℝ} (ha : ContDiff ℝ 1 fun ξ ↦ a (x, ξ))
    (hC : ∀ ξ, ‖a (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) (v : E)
    (hC' : ∀ ξ, ‖fderiv ℝ (fun η ↦ a (x, η)) ξ v‖ ≤ C' * (1 + ‖ξ‖ ^ 2) ^ (m' / 2))
    (u : 𝓢(E, V)) :
    quantizeSchwartzValue a (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪x - y, v⟫) u) x =
      Complex.I • quantizeSchwartzValue (fun p ↦ fderiv ℝ (fun η ↦ a (p.1, η)) p.2 v) u x := by
  -- `⟪x - y, v⟫ u + ⟪y, v⟫ u = ⟪x, v⟫ u`, so this is `inner_smul_quantizeSchwartzValue`.
  have hu : SchwartzMap.smulLeftCLM V (fun y ↦ ⟪x - y, v⟫) u +
      SchwartzMap.smulLeftCLM V (⟪·, v⟫) u = (⟪x, v⟫ : ℂ) • u := by
    have h : (fun y ↦ ⟪x - y, v⟫) + (⟪·, v⟫) = fun _ ↦ ⟪x, v⟫ := by
      funext y
      simp [inner_sub_left]
    rw [← add_apply, ← SchwartzMap.smulLeftCLM_add (by fun_prop) (by fun_prop), h,
      SchwartzMap.smulLeftCLM_const, smul_apply, ContinuousLinearMap.id_apply, Complex.coe_smul]
  have h := quantizeSchwartzValue_add_right ha.continuous.aestronglyMeasurable hC
    (SchwartzMap.smulLeftCLM V (fun y ↦ ⟪x - y, v⟫) u) (SchwartzMap.smulLeftCLM V (⟪·, v⟫) u)
  rw [hu, quantizeSchwartzValue_smul_right, Complex.coe_smul,
    inner_smul_quantizeSchwartzValue ha hC v hC' u, add_comm] at h
  exact (add_right_cancel h).symm

namespace Symbol

/-! ### Symbols -/

variable {n : ℕ} {m : ℝ}

private lemma hasTemperateGrowth_coord_sub (x : CoordinateSpace n) (j : Fin n) :
    (fun y : CoordinateSpace n ↦ (x - y) j).HasTemperateGrowth :=
  (EuclideanSpace.proj j).hasTemperateGrowth.comp (by fun_prop : (x - ·).HasTemperateGrowth)

/-- **Multiplication by a coordinate of the displacement.** Multiplying the input by
`(x - y)_j` and evaluating the quantization at `x` replaces the symbol by `i ∂_{ξ_j} a`. -/
theorem quantizeSchwartzValue_smulLeftCLM_coord_sub (a : Symbol n V W m) (j : Fin n)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ (x - y) j) u) x =
      Complex.I • quantizeSchwartzValue (frequencyDeriv j a).coefficient u x := by
  -- `(x - y)_j u + y_j u = x_j u`, so this is `ofLp_smul_quantizeSchwartzValue`.
  have hg : (fun y : CoordinateSpace n ↦ y j).HasTemperateGrowth :=
    (EuclideanSpace.proj j).hasTemperateGrowth
  have hu : SchwartzMap.smulLeftCLM V (fun y ↦ (x - y) j) u +
      SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u = (x j : ℂ) • u := by
    have h : (fun y : CoordinateSpace n ↦ (x - y) j) + (fun y ↦ y j) = fun _ ↦ x j := by
      funext y
      simp
    rw [← add_apply, ← SchwartzMap.smulLeftCLM_add (hasTemperateGrowth_coord_sub x j) hg, h,
      SchwartzMap.smulLeftCLM_const, smul_apply, ContinuousLinearMap.id_apply, Complex.coe_smul]
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  have h := quantizeSchwartzValue_add_right (a.continuous_coefficient_slice x).aestronglyMeasurable
    hC (SchwartzMap.smulLeftCLM V (fun y ↦ (x - y) j) u)
    (SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ y j) u)
  rw [hu, quantizeSchwartzValue_smul_right, Complex.coe_smul, ofLp_smul_quantizeSchwartzValue,
    add_comm] at h
  exact (add_right_cancel h).symm

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
  have htg := hasTemperateGrowth_coord_sub x
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
      simpa using Function.hasTemperateGrowth_norm_sub_pow x 1
    rw [h, ← SchwartzMap.smulLeftCLM_smulLeftCLM_apply h2
        (Function.hasTemperateGrowth_norm_sub_pow x N),
      quantizeSchwartzValue_smulLeftCLM_norm_sub_sq, ih, hc, pow_succ, mul_smul, neg_one_smul,
      smul_neg]

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
        (Function.hasTemperateGrowth_norm_sub_pow x N).1.contDiffAt
      exact (hd.inv (pow_ne_zero _ (norm_ne_zero_iff.2 hxy))).smul (u.smooth ⊤).contDiffAt
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
      simp [hz]
  have hws : HasCompactSupport (fun y ↦ g y • u y) := hu.smul_left
  set w := hws.toSchwartzMap hwc
  have hu_eq : SchwartzMap.smulLeftCLM V (fun y ↦ ‖x - y‖ ^ (2 * N)) w = u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_norm_sub_pow x N),
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
  rw [offDiagonalKernel_eq a hN hxy]
  simp only [norm_smul, norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_norm,
    one_div_mul_eq_div]
  gcongr
  exact hk.trans (mul_le_mul_of_nonneg_left hint (by positivity))

end Symbol

end TauCeti
