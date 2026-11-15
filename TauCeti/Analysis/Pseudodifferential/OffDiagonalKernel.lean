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
(`TauCeti.quantizeSchwartzValue_smulLeftCLM_inner_sub` in
`TauCeti.Analysis.Pseudodifferential.Quantization`). Summing over the coordinates, multiplying
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

* `TauCeti.Symbol.offDiagonalKernel_eq`: the off-diagonal kernel is
  `(-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y)` for every `N` with `m - 2N < -n`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K(x, y) u(y) dy` for compactly supported `u` vanishing near `x`.
* `TauCeti.Symbol.continuousOn_offDiagonalKernel`, `TauCeti.Symbol.contDiffOn_offDiagonalKernel`:
  the kernel is continuous, and indeed smooth, off the diagonal.
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

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace Symbol

variable {n : ℕ} {m : ℝ}

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
      simp [pow_add, mul_assoc, ← mul_pow]
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

/-- **Smoothness off the diagonal.** The off-diagonal kernel is smooth on `{(x, y) | x ≠ y}`: for
each `k`, choosing `N` with `m - 2N + k < -n` makes the kernel of `Δ_ξ^N a` of class `C^k`
(`TauCeti.Symbol.contDiff_quantizationKernel`). -/
theorem contDiffOn_offDiagonalKernel (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (Function.uncurry (offDiagonalKernel a)) {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  have hN := sub_two_mul_floor_lt (m + k) n
  set N := ⌊(m + k + n) / 2⌋₊ + 1
  have hd : ContDiff ℝ k fun p : CoordinateSpace n × CoordinateSpace n ↦ ‖p.1 - p.2‖ ^ (2 * N) := by
    simp_rw [pow_mul]
    exact ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).pow N
  have hs : ContDiffOn ℝ k (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (-1) ^ N / ‖p.1 - p.2‖ ^ (2 * N)) {p | p.1 ≠ p.2} :=
    contDiffOn_const.div hd.contDiffOn fun p hp ↦
      pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))
  have hK := ((frequencyLaplacianPow N a).contDiff_quantizationKernel k
    (by linarith)).contDiffOn (s := {p | p.1 ≠ p.2})
  exact (hs.smul hK).congr fun p hp ↦ offDiagonalKernel_eq a (by linarith) hp

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
