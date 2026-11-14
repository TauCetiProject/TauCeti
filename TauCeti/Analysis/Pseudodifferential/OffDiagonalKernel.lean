/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.SpecificLimits.DyadicSum

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

Near the diagonal the kernel is singular, and for symbols whose estimates are uniform in the
position its size is controlled by the order: if `m + n > 0`, then
`‖K(x, y)‖ ≤ C ‖x - y‖ ^ (-(m + n))`. For `m = 0` this is the size estimate of a
Calderón–Zygmund kernel, one of the hypotheses under which an operator bounded on `L²` is bounded
on `Lᵖ` for `1 < p < ∞`. The proof cuts `a` into its Littlewood–Paley pieces
`aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)` (`TauCeti.Symbol.littlewoodPaleyPiece`). The kernel is the sum of their
absolutely convergent kernels, and at the scale `2^j` the kernel of `aⱼ` has size `(2^j)^(m + n)`
and decays rapidly beyond the distance `2^{-j}`. Summing these bounds over the dyadic scales
(`TauCeti.sum_min_zpow_mul_rpow_neg_le`), the scales `2^j ≤ ‖x - y‖⁻¹` dominate and give
`‖x - y‖ ^ (-(m + n))`.

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
* `TauCeti.Symbol.IsSmoothing.offDiagonalKernel_eq_quantizationKernel`: for a smoothing symbol it
  is the absolutely convergent kernel.
* `TauCeti.Symbol.hasSum_quantizationKernel_littlewoodPaleyPiece`: off the diagonal it is the sum
  of the kernels of the Littlewood–Paley pieces.
* `Symbol.IsUniform.exists_one_add_mul_pow_mul_norm_quantizationKernel_littlewoodPaleyPiece_le`:
  for a uniform symbol, `(1 + 2^j ‖x - y‖)^N ‖K_{aⱼ}(x, y)‖ ≤ C (2^j)^(m + n)`.
* `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le_rpow`: **the size estimate**,
  `‖K(x, y)‖ ≤ C ‖x - y‖ ^ (-(m + n))` for a uniform symbol with `m + n > 0`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §4.1,
  Proposition 1 (the kernel estimates for symbols of order `m`, by dyadic decomposition).
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

/-- For a smoothing symbol, the off-diagonal kernel is the absolutely convergent kernel
`TauCeti.quantizationKernel`. -/
theorem IsSmoothing.offDiagonalKernel_eq_quantizationKernel {a : Symbol n V W m}
    (ha : a.IsSmoothing) {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha (-n - 1)
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hN : (-n - 1 : ℝ) - 2 * N < -n := by
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    linarith
  -- Compare with a representative `b` of order `-n - 1`; the root-namespace lemma for symbols of
  -- order below `-n` is shadowed here by the name of this theorem.
  rw [offDiagonalKernel_eq a (sub_two_mul_floor_lt m n) hxy, ← hb,
    ← TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel b (by linarith) hxy,
    offDiagonalKernel_eq b hN hxy,
    coefficient_frequencyLaplacianPow_congr hb N]

/-! ### The size of the kernel near the diagonal -/

section Size

open Filter Metric Set

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- **Littlewood–Paley decomposition of the off-diagonal kernel.** Off the diagonal, the kernel
of a symbol `a` is the sum of the absolutely convergent kernels of its Littlewood–Paley pieces
`aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)`. -/
theorem hasSum_quantizationKernel_littlewoodPaleyPiece (a : Symbol n V W m)
    {x y : CoordinateSpace n} (hxy : x ≠ y) :
    HasSum (fun j => quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y)
      (offDiagonalKernel a x y) := by
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hN : m - 2 * N < -n := sub_two_mul_floor_lt m n
  -- Off the diagonal every kernel is `(-1)^N ‖x - y‖^(-2N)` times the kernel of `Δ_ξ^N`.
  have hpiece : (fun j => quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y) =
      fun j => ((-1) ^ N / ‖x - y‖ ^ (2 * N)) •
        quantizationKernel (frequencyLaplacianPow N (a.littlewoodPaleyPiece φ j)).coefficient x y :=
    funext fun j => by
      rw [← (a.isSmoothing_littlewoodPaleyPiece φ j).offDiagonalKernel_eq_quantizationKernel hxy,
        offDiagonalKernel_eq _ hN hxy]
  rw [hpiece, offDiagonalKernel_eq a hN hxy]
  refine HasSum.const_smul _ ?_
  -- The kernel integrals of the pieces are summable in norm, since `m - 2N + n < 0`.
  obtain ⟨C, -, hC⟩ :=
    a.exists_integral_norm_frequencyLaplacianPow_littlewoodPaleyPiece_le φ isCompact_singleton N
  set g : ℕ → CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W :=
    fun j => (frequencyLaplacianPow N (a.littlewoodPaleyPiece φ j)).coefficient
  have hF_int (j : ℕ) :
      Integrable fun ζ : CoordinateSpace n => 𝐞 ⟪ζ, x - y⟫ • g j (x, (2 * π) • ζ) :=
    integrable_quantizationKernel_integrand
      ((frequencyLaplacianPow N (a.littlewoodPaleyPiece φ j)).integrable_coefficient hN x) y
  have hs : m - 2 * N + n < 0 := by linarith
  have hgeo : Summable fun j : ℕ => ((2 : ℝ) ^ j) ^ (m - 2 * N + n) := by
    have h := summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 2 ^ (m - 2 * N + n))
      (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hs)
    exact h.congr fun j => Real.rpow_pow_comm zero_le_two _ j
  have hF_sum : Summable fun j => ∫ ζ, ‖𝐞 ⟪ζ, x - y⟫ • g j (x, (2 * π) • ζ)‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) ((hgeo.mul_left C).mul_left |((2 * π) ^ n)⁻¹|)
    simp_rw [Circle.norm_smul (E := V →L[ℂ] W)]
    rw [Measure.integral_comp_smul (μ := volume) (f := fun ξ => ‖g j (x, ξ)‖),
      finrank_euclideanSpace_fin,
      smul_eq_mul]
    gcongr
    exact hC j x rfl
  convert hasSum_integral_of_summable_integral_norm hF_int hF_sum using 1
  · exact funext fun j => quantizationKernel_def _ _ _
  rw [quantizationKernel_def]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  simp_rw [Circle.smul_def]
  exact ((hasSum_coefficient_frequencyLaplacianPow_littlewoodPaleyPiece φ a N x
    ((2 * π) • ζ)).const_smul _).tsum_eq.symm

/-- **The kernels of the Littlewood–Paley pieces.** For a uniform symbol `a` of order `m` and every
`N`, the kernel of the `j`-th piece satisfies `(1 + 2^j ‖x - y‖)^N ‖K_{aⱼ}(x, y)‖ ≤ C (2^j)^(m + n)`
uniformly in `j`, `x` and `y`: at the frequency scale `2^j` the kernel has size `(2^j)^(m + n)`
and decays rapidly beyond the distance `2^{-j}` from the diagonal. -/
theorem IsUniform.exists_one_add_mul_pow_mul_norm_quantizationKernel_littlewoodPaleyPiece_le
    {a : Symbol n V W m} (ha : a.IsUniform) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ) x y,
      (1 + 2 ^ j * ‖x - y‖) ^ N *
          ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y‖ ≤
        C * ((2 : ℝ) ^ j) ^ (m + n) := by
  obtain ⟨C₀, hC₀, h₀⟩ := ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] []
  choose C₁ hC₁ h₁ using fun k : Fin n =>
    ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] (List.replicate N k)
  set A := C₀ + ∑ k, C₁ k
  have hA : 0 ≤ A := add_nonneg hC₀ (Finset.sum_nonneg fun k _ => hC₁ k)
  refine ⟨2 ^ N * (1 + √n ^ N) * ((2 * π) ^ n)⁻¹ * A, by positivity, fun j x y => ?_⟩
  -- Apply the scale-invariant decay estimate at the scale `R = 2^{-j}`, to a representative of the
  -- piece of order `-n - 1`.
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 (a.isSmoothing_littlewoodPaleyPiece φ j) (-n - 1)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have key := b.one_add_norm_div_pow_mul_norm_quantizationKernel_le (x := x) (by linarith)
    (inv_pos.2 h2j) (A := A * ((2 : ℝ) ^ j) ^ (m + n)) N ?_ ?_ y
  · rw [hb, div_inv_eq_mul, mul_comm ‖x - y‖] at key
    exact key.trans_eq (by ring)
  · rw [hb]
    have h := h₀ j x
    simp only [mixedDeriv_nil_nil, List.length_nil, CharP.cast_eq_zero, sub_zero] at h
    exact h.trans (by gcongr; exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hC₁ k))
  · intro k
    rw [hb]
    refine (h₁ k j x).trans ?_
    rw [List.length_replicate, show m - N + n = m + n + -(N : ℝ) by ring,
      Real.rpow_add h2j, Real.rpow_neg h2j.le, Real.rpow_natCast, ← inv_pow, ← mul_assoc]
    gcongr
    exact (Finset.single_le_sum (fun k _ => hC₁ k) (Finset.mem_univ k)).trans
      (le_add_of_nonneg_left hC₀)

/-- **Summing over the dyadic scales.** Let `0 < s < N`. If the terms of a sum `∑ⱼ Kⱼ = S` satisfy
`(1 + 2^j r)^N ‖Kⱼ‖ ≤ C (2^j)^s` for some `r > 0`, then `‖S‖ ≤ C B r ^ (-s)`, where `B` depends
only on `s` and `N`: the scales `2^j ≤ r⁻¹` contribute their sizes, and the higher ones decay. -/
private theorem exists_norm_le_mul_rpow_of_hasSum {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : s < N) :
    ∃ B, 0 ≤ B ∧ ∀ {K : ℕ → V →L[ℂ] W} {S : V →L[ℂ] W} {C r : ℝ}, HasSum K S → 0 ≤ C → 0 < r →
      (∀ j : ℕ, (1 + 2 ^ j * r) ^ N * ‖K j‖ ≤ C * ((2 : ℝ) ^ j) ^ s) → ‖S‖ ≤ C * B * r ^ (-s) := by
  -- The per-scale bounds are `min (b^j u) ((b^j u)^(-δ))` with `b = 2^s`, `u = r^s` and
  -- `δ = (N - s) / s`, which sum to at most `B` over every finite set of scales.
  set b : ℝ := 2 ^ s
  have hb : 1 < b := Real.one_lt_rpow one_lt_two hs
  set δ := (N - s) / s with hδ_def
  have hδ : 0 < δ := div_pos (by linarith) hs
  set B := (1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹
  have hB : 0 ≤ B := by
    have h₁ := sub_pos.2 (inv_lt_one_of_one_lt₀ hb)
    have h₂ := sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg hb (neg_neg_of_pos hδ))
    positivity
  refine ⟨B, hB, fun {K S C r} hKS hC0 hr hC => ?_⟩
  have hterm (j : ℕ) : ‖K j‖ ≤
      C * r ^ (-s) * min (b ^ (j : ℤ) * r ^ s) ((b ^ (j : ℤ) * r ^ s) ^ (-δ)) := by
    set t := (2 : ℝ) ^ j * r
    have ht : 0 < t := by positivity
    have hK := hC j
    have hbt : b ^ (j : ℤ) * r ^ s = t ^ s := by
      rw [zpow_natCast, Real.mul_rpow (by positivity) hr.le]
      congr 1
      exact Real.rpow_pow_comm zero_le_two s j
    have h2j : ((2 : ℝ) ^ j) ^ s = r ^ (-s) * t ^ s := by
      have hrs := (Real.rpow_pos_of_pos hr s).ne'
      rw [Real.mul_rpow (by positivity) hr.le, Real.rpow_neg hr.le]
      field_simp
    have htδ : (t ^ s) ^ (-δ) = t ^ (s - N) := by
      rw [← Real.rpow_mul ht.le, hδ_def]
      congr 1
      field_simp [hs.ne']
      ring
    rw [hbt, htδ, mul_min_of_nonneg _ _ (by positivity)]
    refine le_min ?_ ?_
    · -- Near the diagonal, `‖Kⱼ‖ ≤ C (2^j)^s`.
      calc ‖K j‖ ≤ (1 + t) ^ N * ‖K j‖ :=
            le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith))
        _ ≤ C * ((2 : ℝ) ^ j) ^ s := hK
        _ = C * r ^ (-s) * t ^ s := by rw [h2j, mul_assoc]
    · -- Away from it, `t^N ‖Kⱼ‖ ≤ C (2^j)^s`.
      rw [Real.rpow_sub ht, Real.rpow_natCast, ← mul_div_assoc, le_div_iff₀ (by positivity),
        mul_comm ‖K j‖]
      calc t ^ N * ‖K j‖ ≤ (1 + t) ^ N * ‖K j‖ := by gcongr; linarith
        _ ≤ C * ((2 : ℝ) ^ j) ^ s := hK
        _ = C * r ^ (-s) * t ^ s := by rw [h2j, mul_assoc]
  have hsum (T : Finset ℕ) :
      ∑ j ∈ T, C * r ^ (-s) * min (b ^ (j : ℤ) * r ^ s) ((b ^ (j : ℤ) * r ^ s) ^ (-δ)) ≤
        C * r ^ (-s) * B := by
    rw [← Finset.mul_sum]
    gcongr
    have h := sum_min_zpow_mul_rpow_neg_le hb hδ (r ^ s) (T.map Nat.castEmbedding)
    rwa [Finset.sum_map] at h
  have hnonneg : 0 ≤ fun j : ℕ =>
      C * r ^ (-s) * min (b ^ (j : ℤ) * r ^ s) ((b ^ (j : ℤ) * r ^ s) ^ (-δ)) :=
    fun j => (norm_nonneg _).trans (hterm j)
  calc ‖S‖
      ≤ ∑' j : ℕ, C * r ^ (-s) * min (b ^ (j : ℤ) * r ^ s) ((b ^ (j : ℤ) * r ^ s) ^ (-δ)) :=
        hKS.norm_le_of_bounded (summable_of_sum_le hnonneg hsum).hasSum hterm
    _ ≤ C * r ^ (-s) * B := Real.tsum_le_of_sum_le hnonneg hsum
    _ = C * B * r ^ (-s) := by ring

/-- **The size estimate for the kernel of a uniform symbol.** If `a` is a symbol of order `m`
whose estimates are uniform in the position, with `m + n > 0`, then its kernel off the diagonal
satisfies

`‖K(x, y)‖ ≤ C ‖x - y‖ ^ (-(m + n))` for all `x`, `y`.

For `m = 0` this is the size estimate of a Calderón–Zygmund kernel. The bound follows by summing
the estimates of the Littlewood–Paley pieces over the dyadic scales: the pieces at frequencies
`2^j ≤ ‖x - y‖⁻¹` contribute their sizes `(2^j)^(m + n)`, and the higher ones decay. -/
theorem IsUniform.exists_norm_offDiagonalKernel_le_rpow {a : Symbol n V W m} (ha : a.IsUniform)
    (hm : 0 < m + n) :
    ∃ C, 0 ≤ C ∧ ∀ x y, ‖offDiagonalKernel a x y‖ ≤ C * ‖x - y‖ ^ (-(m + n)) := by
  let φ : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (m + n)
  obtain ⟨C, hC0, hC⟩ :=
    ha.exists_one_add_mul_pow_mul_norm_quantizationKernel_littlewoodPaleyPiece_le φ N
  obtain ⟨B, hB, hsum⟩ := exists_norm_le_mul_rpow_of_hasSum (V := V) (W := W) hm hN
  refine ⟨C * B, mul_nonneg hC0 hB, fun x y => ?_⟩
  rcases eq_or_ne x y with rfl | hxy
  · rw [offDiagonalKernel_self, norm_zero, sub_self, norm_zero,
      Real.zero_rpow (neg_ne_zero.2 hm.ne'), mul_zero]
  exact hsum (a.hasSum_quantizationKernel_littlewoodPaleyPiece φ hxy) hC0
    (norm_pos_iff.2 (sub_ne_zero.2 hxy)) fun j => hC j x y

end Size

end Symbol

end TauCeti
