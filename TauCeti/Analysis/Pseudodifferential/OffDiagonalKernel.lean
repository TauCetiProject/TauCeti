/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Pseudodifferential kernels are smooth off the diagonal

The left quantization of a symbol `a ∈ S^m_{1,0}` on `ℝⁿ` is formally the integral operator with
kernel `K_a(x, y) = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`. For `m < -n` this integral converges
absolutely (`TauCeti.quantizationKernel`); in general it does not, and `K_a` is only a distribution.
Away from the diagonal it is nevertheless a smooth function, by repeated integration by parts in the
frequency: multiplying the kernel by `-‖x - y‖²` replaces `a` by its frequency Laplacian `Δ_ξ a`,
a symbol of order `m - 2`, so `K_a(x, y) = (-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)` where the right side
converges absolutely as soon as `m - 2N < -n`, and is `C^k` as soon as `m - 2N + k < -n`.

The ingredients are proved where the kernel and the quantization are defined: the smoothness
`TauCeti.Symbol.contDiff_quantizationKernel` and the identity
`TauCeti.Symbol.quantizationKernel_iteratedFrequencyLaplacian` for the absolutely convergent kernel
in `TauCeti.Analysis.Pseudodifferential.Kernel`, and its operator form
`TauCeti.Symbol.quantizeSchwartzValue_iteratedFrequencyLaplacian`, valid for symbols of every order,
in `TauCeti.Analysis.Pseudodifferential.Quantization`.

## Main results

* `TauCeti.Symbol.offDiagonalKernel`: the kernel `K_a(x, y)` of a symbol of any order for `x ≠ y`,
  with the formula `TauCeti.Symbol.offDiagonalKernel_eq` for every admissible `N`; it agrees with
  `TauCeti.quantizationKernel` when `m < -n`
  (`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`).
* `TauCeti.Symbol.offDiagonalKernel_self`: the convention `K_a(x, x) = 0`, and
  `TauCeti.Symbol.offDiagonalKernel_add`, `TauCeti.Symbol.offDiagonalKernel_smul`,
  `TauCeti.Symbol.offDiagonalKernel_zero`: linearity in the symbol.
* `TauCeti.Symbol.contDiffOn_offDiagonalKernel`: **the kernel is smooth off the diagonal.**
* `TauCeti.Symbol.norm_offDiagonalKernel_le`: `‖K_a(x, y)‖ ≤ C_{x,N} ‖x - y‖⁻²ᴺ` for every `N`
  with `m - 2N < -n`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K_a(x, y) u(y) dy` for compactly supported Schwartz `u` vanishing near `x`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open scoped SchwartzMap ContDiff
open MeasureTheory Real Module

noncomputable section

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### The kernel off the diagonal -/

/-- `N = ⌊(m + n) / 2⌋ + 1` frequency Laplacians bring the order `m` below `-n`. -/
private theorem sub_two_mul_floor_add_one_lt (n : ℕ) (m : ℝ) :
    m - 2 * ((⌊(m + n) / 2⌋₊ + 1 : ℕ) : ℝ) < -n := by
  have := Nat.lt_floor_add_one ((m + n) / 2)
  push_cast
  linarith

/-- The kernel `K_a(x, y)` of the quantization of a symbol `a` of order `m`, off the diagonal
`x = y`. For any `N` with `m - 2N < -n`, the symbol `Δ_ξ^N a` has an absolutely convergent kernel,
and `K_a(x, y) = (-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)` (`TauCeti.Symbol.offDiagonalKernel_eq`); when
`m < -n` this is the kernel `TauCeti.quantizationKernel` itself
(`TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel`), and for every order it represents
`Op(a)` away from the diagonal
(`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`). The definition uses
`N = ⌊(m + n) / 2⌋ + 1`. On the diagonal the kernel of a general symbol is singular, and the value
`0` given by this formula there is a convention. -/
def offDiagonalKernel (a : Symbol n V W m) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  ((-‖x - y‖ ^ 2) ^ (⌊(m + n) / 2⌋₊ + 1))⁻¹ •
    quantizationKernel (iteratedFrequencyLaplacian (⌊(m + n) / 2⌋₊ + 1) a).coefficient x y

theorem offDiagonalKernel_def (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel a x y = ((-‖x - y‖ ^ 2) ^ (⌊(m + n) / 2⌋₊ + 1))⁻¹ •
      quantizationKernel (iteratedFrequencyLaplacian (⌊(m + n) / 2⌋₊ + 1) a).coefficient x y :=
  (rfl)

/-- Applying `M` more frequency Laplacians does not change the kernel formula off the diagonal. -/
private theorem inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add (a : Symbol n V W m)
    {N : ℕ} (hN : m - 2 * N < -n) (M : ℕ) {x y : CoordinateSpace n} (hxy : x ≠ y) :
    ((-‖x - y‖ ^ 2) ^ (N + M))⁻¹ •
        quantizationKernel (iteratedFrequencyLaplacian (N + M) a).coefficient x y =
      ((-‖x - y‖ ^ 2) ^ N)⁻¹ •
        quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y := by
  have hr : -‖x - y‖ ^ 2 ≠ 0 :=
    neg_ne_zero.2 (pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)))
  rw [coefficient_iteratedFrequencyLaplacian_add,
    quantizationKernel_iteratedFrequencyLaplacian _ hN, smul_smul, pow_add, mul_inv,
    mul_assoc, inv_mul_cancel₀ (pow_ne_zero M hr), mul_one]

/-- **Kernel formula off the diagonal.** For every `N` with `m - 2N < -n` and `x ≠ y`, the kernel
of `a` is `(-‖x - y‖²)⁻ᴺ K_{Δ_ξ^N a}(x, y)`. -/
theorem offDiagonalKernel_eq (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = ((-‖x - y‖ ^ 2) ^ N)⁻¹ •
      quantizationKernel (iteratedFrequencyLaplacian N a).coefficient x y := by
  rw [offDiagonalKernel_def, ← inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add a
      (sub_two_mul_floor_add_one_lt n m) N hxy,
    ← inv_smul_quantizationKernel_iteratedFrequencyLaplacian_add a hN
      (⌊(m + n) / 2⌋₊ + 1) hxy, add_comm]

/-- For a symbol of order `m < -n`, the kernel off the diagonal is the absolutely convergent
kernel `K_a(x, y) = ∫ exp(2πi ⟪ζ, x - y⟫) a(x, 2πζ) dζ`. -/
theorem offDiagonalKernel_eq_quantizationKernel (a : Symbol n V W m) (hm : m < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  rw [offDiagonalKernel_eq a (N := 0) (by simpa using hm) hxy]
  simp

/-- **Pseudodifferential kernels are smooth off the diagonal.** The kernel of a symbol of any order
is smooth on `{(x, y) | x ≠ y}`. -/
theorem contDiffOn_offDiagonalKernel (a : Symbol n V W m) :
    ContDiffOn ℝ ∞ (Function.uncurry (offDiagonalKernel a)) {p | p.1 ≠ p.2} := by
  refine contDiffOn_infty.2 fun k ↦ ?_
  -- Use `N` Laplacians, with `m - 2N + k < -n`, so that the kernel of `Δ_ξ^N a` is `C^k`.
  have hN := sub_two_mul_floor_add_one_lt n (m + k)
  set N := ⌊(m + k + n) / 2⌋₊ + 1
  have h₁ : ContDiffOn ℝ k (fun p : CoordinateSpace n × CoordinateSpace n ↦
      ((-‖p.1 - p.2‖ ^ 2) ^ N)⁻¹) {p | p.1 ≠ p.2} :=
    (((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_snd)).neg.pow N).contDiffOn.inv
      fun p hp ↦ pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 hp))))
  have h₂ := ((iteratedFrequencyLaplacian N a).contDiff_quantizationKernel k
    (by linarith)).contDiffOn (s := {p | p.1 ≠ p.2})
  exact (h₁.smul h₂).congr fun p hp ↦ offDiagonalKernel_eq a (by linarith) hp

/-- **Decay off the diagonal.** For every `N` with `m - 2N < -n` and `x ≠ y`,
`‖K_a(x, y)‖ ≤ ‖x - y‖⁻²ᴺ (2π)⁻ⁿ ∫ ‖Δ_ξ^N a(x, ξ)‖ dξ`. In particular, for fixed `x` the kernel
decays faster than every power of `‖x - y‖`. -/
theorem norm_offDiagonalKernel_le (a : Symbol n V W m) {N : ℕ} (hN : m - 2 * N < -n)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    ‖offDiagonalKernel a x y‖ ≤ (‖x - y‖ ^ (2 * N))⁻¹ *
      (((2 * π) ^ n)⁻¹ * ∫ ξ, ‖(iteratedFrequencyLaplacian N a).coefficient (x, ξ)‖) := by
  rw [offDiagonalKernel_eq a hN hxy, norm_smul, norm_inv, norm_pow, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), ← pow_mul]
  gcongr
  simpa using norm_quantizationKernel_le (iteratedFrequencyLaplacian N a).coefficient x y

/-- **Kernel representation off the diagonal.** For a symbol `a` of any order, a compactly
supported Schwartz function `u` and a point `x` outside the support of `u`,
`Op(a) u (x) = ∫ K_a(x, y) u(y) dy`. Thus `offDiagonalKernel a` is the distribution kernel of
`Op(a)` away from the diagonal. -/
theorem quantizeSchwartzValue_eq_integral_offDiagonalKernel [CompleteSpace V] [CompleteSpace W]
    (a : Symbol n V W m) {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u)
    {x : CoordinateSpace n} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ y, offDiagonalKernel a x y (u y) := by
  have hN := sub_two_mul_floor_add_one_lt n m
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hux : ∀ y, y ∉ tsupport u → u y = 0 := fun y hy ↦ image_eq_zero_of_notMem_tsupport hy
  -- `w = (-‖x - ·‖²)⁻ᴺ u` is smooth, since `u` vanishes near `x`, and compactly supported.
  set g : CoordinateSpace n → ℝ := fun y ↦ ((-‖x - y‖ ^ 2) ^ N)⁻¹
  have hg : ContDiffOn ℝ ∞ g {y | y ≠ x} :=
    (((contDiff_norm_sq ℝ).comp (contDiff_const.sub contDiff_id)).neg.pow N).contDiffOn.inv
      fun y hy ↦ pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hy)))))
  have hw_smooth : ContDiff ℝ ∞ fun y ↦ g y • u y := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ tsupport u
    · have hyx : y ≠ x := fun h ↦ hx (h ▸ hy)
      exact (hg.contDiffAt ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hyx)).smul
        (u.smooth ⊤).contDiffAt
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hy] with z hz
      rw [hux z hz, smul_zero]
  set w := (hu.smul_left (f := g)).toSchwartzMap hw_smooth
  have hw (y : CoordinateSpace n) : w y = g y • u y :=
    HasCompactSupport.toSchwartzMap_toFun _ _ y
  -- `(-‖x - ·‖²)ᴺ w = u`.
  have hwu : SchwartzMap.smulLeftCLM V (fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N) w = u := by
    ext y
    have htg : (fun y : CoordinateSpace n ↦ (-‖x - y‖ ^ 2) ^ N).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.smulLeftCLM_apply_apply htg, hw, smul_smul]
    by_cases hy : y = x
    · rw [hy, hux x hx, smul_zero]
    · rw [mul_inv_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 (pow_ne_zero 2
        (norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hy)))))), one_smul]
  conv_lhs => rw [← hwu]
  rw [← quantizeSchwartzValue_iteratedFrequencyLaplacian,
    quantizeSchwartzValue_eq_integral_quantizationKernel
      ((iteratedFrequencyLaplacian N a).integrable_coefficient hN x)]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  by_cases hy : y = x
  · simp only [hw, hy, hux x hx, smul_zero, map_zero]
  · dsimp only
    rw [offDiagonalKernel_eq a hN (Ne.symm hy), hw, smul_apply,
      ContinuousLinearMap.map_smul_of_tower]

/-- The kernel off the diagonal is additive in the symbol. -/
@[simp]
theorem offDiagonalKernel_add (a b : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (a + b) x y = offDiagonalKernel a x y + offDiagonalKernel b x y := by
  have h := sub_two_mul_floor_add_one_lt n m
  simp only [offDiagonalKernel_def, map_add, coefficient_add, ← smul_add]
  rw [quantizationKernel_add (integrable_coefficient _ h x) (integrable_coefficient _ h x)]

/-- The kernel off the diagonal is homogeneous in the symbol. -/
@[simp]
theorem offDiagonalKernel_smul (c : ℂ) (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (c • a) x y = c • offDiagonalKernel a x y := by
  simp only [offDiagonalKernel_def, map_smul, coefficient_smul, quantizationKernel_smul]
  exact smul_comm _ _ _

/-- The kernel off the diagonal takes the conventional value `0` on the diagonal. -/
@[simp]
theorem offDiagonalKernel_self (a : Symbol n V W m) (x : CoordinateSpace n) :
    offDiagonalKernel a x x = 0 := by
  simp [offDiagonalKernel_def]

/-- The kernel of the zero symbol vanishes. -/
@[simp]
theorem offDiagonalKernel_zero (x y : CoordinateSpace n) :
    offDiagonalKernel (0 : Symbol n V W m) x y = 0 := by
  simpa using offDiagonalKernel_smul 0 (0 : Symbol n V W m) x y

end Symbol

end TauCeti
