/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
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

Cutting `a` into its Littlewood–Paley pieces `aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)`
(`TauCeti.Symbol.littlewoodPaleyPiece`), which have bounded frequency support, the kernel is the
sum of their absolutely convergent kernels off the diagonal: the symbols `Δ_ξ^N aⱼ` sum to
`Δ_ξ^N a`, with integrals summable over `j` once `m - 2N < -n`. This needs no uniformity of `a` in
the position. For uniform symbols it is the starting point of the size and smoothness estimates
in `TauCeti.Analysis.Pseudodifferential.StandardKernel`.

## Main results

* `TauCeti.Symbol.offDiagonalKernel_eq`: the off-diagonal kernel is
  `(-1)^N ‖x - y‖^(-2N) K_{Δ_ξ^N a}(x, y)` for every `N` with `m - 2N < -n`.
* `TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`: **kernel representation**,
  `Op(a) u (x) = ∫ K(x, y) u(y) dy` for compactly supported `u` vanishing near `x`.
* `TauCeti.Symbol.continuousOn_offDiagonalKernel`, `TauCeti.Symbol.contDiffOn_offDiagonalKernel`:
  the kernel is continuous, and indeed smooth, off the diagonal.
* `TauCeti.Symbol.stronglyMeasurable_uncurry_offDiagonalKernel`: the kernel, with its value `0` on
  the diagonal, is strongly measurable.
* `TauCeti.Symbol.contDiffOn_quantizationKernel`: the absolutely convergent kernel of a symbol of
  order `m < -n` is smooth off the diagonal.
* `TauCeti.Symbol.eqOn_offDiagonalKernel_of_forall`: **uniqueness**, on an open set `U` not
  containing `x`, a kernel continuous on `U` that represents `u ↦ Op(a) u (x)` on compactly
  supported Schwartz functions supported in `U` is the off-diagonal kernel there.
* `TauCeti.Symbol.exists_norm_offDiagonalKernel_le`: `‖K(x, y)‖ ≤ C ‖x - y‖^(-2N)` for `x` in a
  compact set, for every `N` with `m - 2N < -n`; in particular the kernel decays faster than any
  power of `‖x - y‖` as `y → ∞`.
* `TauCeti.Symbol.localizedOffDiagonalKernel`, `TauCeti.Symbol.contDiff_localizedOffDiagonalKernel`:
  multiplying `K_a` by `1 - χ` for a smooth cutoff `χ` equal to `1` near the diagonal yields a
  globally `C^∞` residual kernel on `ℝⁿ × ℝⁿ`.
* `TauCeti.Symbol.offDiagonalKernel_congr`: the kernel at `(x, y)` only depends on the coefficient
  of the symbol at `x`, whatever its order.
* `TauCeti.Symbol.IsSmoothing.offDiagonalKernel_eq_quantizationKernel`: for a smoothing symbol it
  is the absolutely convergent kernel.
* `TauCeti.Symbol.hasSum_quantizationKernel_littlewoodPaleyPiece`: off the diagonal it is the sum
  of the kernels of the Littlewood–Paley pieces.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* M. E. Taylor, *Pseudodifferential Operators*, Princeton University Press, 1981, Chapter II,
  §§1–2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §4.1,
  Proposition 1 (the kernel estimates for symbols of order `m`, by dyadic decomposition).
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff LineDeriv Topology
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

/-- The off-diagonal kernel of the zero symbol vanishes. -/
@[simp]
theorem offDiagonalKernel_zero (x y : CoordinateSpace n) :
    offDiagonalKernel (0 : Symbol n V W m) x y = 0 := by
  simp [offDiagonalKernel]

/-- The off-diagonal kernel is additive in the symbol. -/
theorem offDiagonalKernel_add (a b : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (a + b) x y = offDiagonalKernel a x y + offDiagonalKernel b x y := by
  rw [offDiagonalKernel, offDiagonalKernel, offDiagonalKernel, map_add, coefficient_add,
    quantizationKernel_add
      ((frequencyLaplacianPow _ a).integrable_coefficient (sub_two_mul_floor_lt m n) x)
      ((frequencyLaplacianPow _ b).integrable_coefficient (sub_two_mul_floor_lt m n) x),
    smul_add]

/-- The off-diagonal kernel is homogeneous in the symbol. -/
@[simp]
theorem offDiagonalKernel_smul (c : ℂ) (a : Symbol n V W m) (x y : CoordinateSpace n) :
    offDiagonalKernel (c • a) x y = c • offDiagonalKernel a x y := by
  rw [offDiagonalKernel, offDiagonalKernel, map_smul, coefficient_smul, quantizationKernel_smul,
    smul_comm]

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

/-- **Continuity in the second variable.** For fixed `x`, the off-diagonal kernel `y ↦ K(x, y)` is
continuous away from `x`. -/
theorem continuousOn_offDiagonalKernel_compl_singleton (a : Symbol n V W m)
    (x : CoordinateSpace n) : ContinuousOn (offDiagonalKernel a x) {x}ᶜ := by
  have hmaps : Set.MapsTo (fun y ↦ (x, y)) {x}ᶜ
      {p : CoordinateSpace n × CoordinateSpace n | p.1 ≠ p.2} :=
    fun y hy (hxy : x = y) ↦ hy (Set.mem_singleton_iff.2 hxy.symm)
  exact ((continuousOn_offDiagonalKernel a).comp
    (continuous_const.prodMk continuous_id).continuousOn hmaps).congr
    fun y _ ↦ (Function.uncurry_apply_pair _ x y).symm

/-- **Measurability.** The off-diagonal kernel, with its value `0` on the diagonal, is strongly
measurable as a function of `(x, y)`, as integral operators with this kernel require. -/
theorem stronglyMeasurable_uncurry_offDiagonalKernel (a : Symbol n V W m) :
    MeasureTheory.StronglyMeasurable (Function.uncurry (offDiagonalKernel a)) := by
  set N := ⌊(m + n) / 2⌋₊ + 1
  have hK := (frequencyLaplacianPow N a).continuous_quantizationKernel (sub_two_mul_floor_lt m n)
  have hs : Measurable (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (-1 : ℝ) ^ N / ‖p.1 - p.2‖ ^ (2 * N)) := by fun_prop
  -- By definition, the kernel is this measurable scalar times a continuous kernel.
  exact hs.stronglyMeasurable.smul hK.stronglyMeasurable

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

/-- **Smoothness off the diagonal for symbols of order `m < -n`.** The absolutely convergent kernel
`K_a` is smooth on `{(x, y) | x ≠ y}`. -/
theorem contDiffOn_quantizationKernel (a : Symbol n V W m) (hm : m < -n) :
    ContDiffOn ℝ ∞ (Function.uncurry (quantizationKernel a.coefficient)) {p | p.1 ≠ p.2} :=
  (contDiffOn_offDiagonalKernel a).congr fun _ hp ↦
    (offDiagonalKernel_eq_quantizationKernel a hm hp).symm

/-- **Uniqueness of the kernel off the diagonal.** On an open set `U` not containing `x`, a kernel
`K` continuous on `U` that represents `u ↦ Op(a) u (x)` on the compactly supported Schwartz
functions supported in `U` is the off-diagonal kernel: `K y = offDiagonalKernel a x y` for every
`y ∈ U`. -/
theorem eqOn_offDiagonalKernel_of_forall [CompleteSpace V] [CompleteSpace W] (a : Symbol n V W m)
    {x : CoordinateSpace n} {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hxU : x ∉ U)
    {K : CoordinateSpace n → V →L[ℂ] W} (hK : ContinuousOn K U)
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → tsupport u ⊆ U →
      quantizeSchwartzValue a.coefficient u x = ∫ y, K y (u y)) :
    Set.EqOn K (offDiagonalKernel a x) U := by
  have hK₀ : ContinuousOn (offDiagonalKernel a x) U :=
    (continuousOn_offDiagonalKernel_compl_singleton a x).mono fun y hy (hyx : y = x) ↦
      hxU (hyx ▸ hy)
  refine hU.eqOn_of_integral_clm_apply_eq (μ := volume) hK hK₀ fun u hu huU ↦ ?_
  rw [← h u hu huU,
    quantizeSchwartzValue_eq_integral_offDiagonalKernel a hu fun hx ↦ hxU (huU hx)]

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

/-- The product `(1 - χ(x, y)) • K_a(x, y)` of `1 - χ` with the off-diagonal kernel of `a`;
when `χ = 1` on a neighborhood of every diagonal point `(x, x)`, this cuts out a neighborhood of
the diagonal and yields a globally smooth residual kernel
(`contDiff_localizedOffDiagonalKernel`). -/
def localizedOffDiagonalKernel (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x y : CoordinateSpace n) : V →L[ℂ] W :=
  (1 - χ x y) • a.offDiagonalKernel x y

@[simp]
theorem localizedOffDiagonalKernel_apply (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x y : CoordinateSpace n) :
    a.localizedOffDiagonalKernel χ x y = (1 - χ x y) • a.offDiagonalKernel x y :=
  (rfl)

theorem localizedOffDiagonalKernel_self (a : Symbol n V W m)
    (χ : CoordinateSpace n → CoordinateSpace n → ℝ) (x : CoordinateSpace n) :
    a.localizedOffDiagonalKernel χ x x = 0 := by
  simp

/-- **Global smoothness of the localized off-diagonal kernel.** Because `1 - χ` vanishes on a
neighborhood of every diagonal point `(x, x)` and `offDiagonalKernel a` is `C^∞` away from the
diagonal, `(x, y) ↦ (1 - χ(x, y)) • K_a(x, y)` is `C^∞` on the *entire* product `ℝⁿ × ℝⁿ`. -/
theorem contDiff_localizedOffDiagonalKernel (a : Symbol n V W m)
    {χ : CoordinateSpace n → CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ (Function.uncurry χ))
    (hχ_diag : ∀ x, Function.uncurry χ =ᶠ[𝓝 (x, x)] 1) :
    ContDiff ℝ ∞ (Function.uncurry (a.localizedOffDiagonalKernel χ)) := by
  refine contDiff_iff_contDiffAt.2 fun ⟨x, y⟩ ↦ ?_
  rcases eq_or_ne x y with rfl | hxy
  · refine (contDiffAt_const (c := (0 : V →L[ℂ] W))).congr_of_eventuallyEq ?_
    filter_upwards [hχ_diag x] with ⟨x', y'⟩ h1
    have h1' : χ x' y' = 1 := h1
    simp [localizedOffDiagonalKernel, h1']
  · exact ((contDiff_const.sub hχ).contDiffAt (x := (x, y))).smul
      (a.contDiffOn_offDiagonalKernel.contDiffAt (isClosed_diagonal.isOpen_compl.mem_nhds hxy))

/-- The off-diagonal kernel at `(x, y)` only depends on the coefficient of the symbol at the
position `x`, and not on the order at which the symbol is regarded. -/
theorem offDiagonalKernel_congr {m' : ℝ} {a : Symbol n V W m} {b : Symbol n V W m'}
    {x : CoordinateSpace n} (h : ∀ ξ, a.coefficient (x, ξ) = b.coefficient (x, ξ))
    (y : CoordinateSpace n) : offDiagonalKernel a x y = offDiagonalKernel b x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  -- Use a common exponent `N`, admissible for both orders.
  set N := max (⌊(m + n) / 2⌋₊ + 1) (⌊(m' + n) / 2⌋₊ + 1)
  have hN {μ : ℝ} (hμ : ⌊(μ + n) / 2⌋₊ + 1 ≤ N) : μ - 2 * N < -n :=
    lt_of_le_of_lt (by gcongr) (sub_two_mul_floor_lt μ n)
  have hΔ (ξ : CoordinateSpace n) := (Filter.EventuallyEq.coefficient_frequencyLaplacianPow
    (Filter.Eventually.of_forall h) N (ξ := ξ)).eq_of_nhds
  rw [offDiagonalKernel_eq a (hN (le_max_left _ _)) hxy,
    offDiagonalKernel_eq b (hN (le_max_right _ _)) hxy, quantizationKernel_def,
    quantizationKernel_def]
  simp only [hΔ]

/-- For a smoothing symbol, the off-diagonal kernel is the absolutely convergent kernel
`TauCeti.quantizationKernel`. -/
theorem IsSmoothing.offDiagonalKernel_eq_quantizationKernel {a : Symbol n V W m}
    (ha : a.IsSmoothing) {x y : CoordinateSpace n} (hxy : x ≠ y) :
    offDiagonalKernel a x y = quantizationKernel a.coefficient x y := by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha (-n - 1)
  -- Compare with a representative `b` of order `-n - 1`; the root-namespace lemma for symbols of
  -- order below `-n` is shadowed here by the name of this theorem.
  rw [offDiagonalKernel_congr (fun ξ => congrFun hb.symm (x, ξ)), ← hb]
  exact TauCeti.Symbol.offDiagonalKernel_eq_quantizationKernel b (by linarith) hxy

/-! ### Littlewood–Paley decomposition of the kernel -/

section LittlewoodPaley

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
    a.exists_integral_norm_coefficient_frequencyLaplacianPow_littlewoodPaleyPiece_le φ
      isCompact_singleton N
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
      (fun j => ?_) ((hgeo.mul_left C).mul_left ((2 * π) ^ n)⁻¹)
    rw [integral_norm_quantizationKernel_integrand (g j), finrank_euclideanSpace_fin]
    gcongr
    exact hC j x (Set.mem_singleton x)
  convert hasSum_integral_of_summable_integral_norm hF_int hF_sum using 1
  · exact funext fun j => quantizationKernel_def _ _ _
  rw [quantizationKernel_def]
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  simp_rw [Circle.smul_def]
  exact ((hasSum_coefficient_frequencyLaplacianPow_littlewoodPaleyPiece φ a N x
    ((2 * π) • ζ)).const_smul _).tsum_eq.symm

end LittlewoodPaley

end Symbol

end TauCeti
