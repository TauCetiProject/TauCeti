/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
public import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
import TauCeti.Analysis.SpecificLimits.DyadicSum

/-!
# Calderón–Zygmund estimates for the kernels of uniform symbols

Let `a` be a symbol of order `m` on `ℝⁿ` whose estimates hold uniformly in the position
(`TauCeti.Symbol.IsUniform`). Off the diagonal, the Schwartz kernel `K(x, y)` of its quantization
is the smooth function `TauCeti.Symbol.offDiagonalKernel a`. This file proves that, when
`m + n > 0`, it is a *standard kernel* of order `m + n`:

* the size estimate `‖K(x, y)‖ ≤ C ‖x - y‖^(-(m + n))`;
* for every `0 < δ < 1` the smoothness estimates
  `‖K(x, y) - K(x, y')‖ ≤ C ‖y - y'‖^δ ‖x - y'‖^(-(m + n + δ))` when `2 ‖y - y'‖ < ‖x - y'‖`, and
  `‖K(x, y) - K(x', y)‖ ≤ C ‖x - x'‖^δ ‖x' - y‖^(-(m + n + δ))` when `2 ‖x - x'‖ < ‖x' - y‖`.

For `m = 0` these are the estimates which the Calderón–Zygmund theorem
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`) asks of the kernel of an operator
and of the kernel `(x, y) ↦ K(y, x)†` of its adjoint, and which, together with the `L²` bound of
the Calderón–Vaillancourt theorem, give bounds in `Lᵖ` for `1 < p < ∞`. The estimates are uniform
in the position, which is where `IsUniform` enters, and they hold for every exponent `δ < 1`; the
Lipschitz case `δ = 1` is not proved here.

## The argument

The Littlewood–Paley pieces `aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)` (`TauCeti.Symbol.littlewoodPaleyPiece`)
have bounded frequency support, so their kernels `Kⱼ = TauCeti.quantizationKernel aⱼ` are
absolutely convergent integrals. Off the diagonal the kernel of `a` is their sum
(`TauCeti.Symbol.IsUniform.hasSum_quantizationKernel_littlewoodPaleyPiece`): the pieces sum to the
symbol, so the partial sums of the quantizations `Op(aⱼ) u (x)` converge to `Op(a) u (x)`, and the
partial sums of the kernels converge locally uniformly away from `x`. Both sides therefore
represent `u ↦ Op(a) u (x)` on test functions supported away from `x`, and the uniqueness of the
off-diagonal kernel (`TauCeti.Symbol.eqOn_offDiagonalKernel_of_forall`) identifies them.

The piece `aⱼ` lives at frequencies of size `2^j`, where it is of size `(2^j)^m` and each
frequency derivative gains a factor `2^{-j}`. Integration by parts in the frequency
(`TauCeti.Symbol.one_add_norm_div_pow_mul_norm_quantizationKernel_le`) gives, for every `N`,

`‖Kⱼ(x, y)‖ ≤ C (2^j)^(m + n) (1 + 2^j ‖x - y‖)^(-N)`,

and the first frequency moment bounds the increments,
`‖Kⱼ(x, y) - Kⱼ(x, y')‖ ≤ D (2^j)^(m + n + 1) ‖y - y'‖`, and similarly in the first variable.
Summing the first bounds over `j` (`TauCeti.exists_tsum_rpow_mul_one_add_rpow_neg_le`) gives the
size estimate. For the smoothness estimates each increment is at most the minimum `min(A, B)` of
the two bounds, and `min(A, B) ≤ A^δ B^(1 - δ)` sums in the same way
(`TauCeti.exists_norm_le_of_hasSum_of_le_of_le`).

## Main results

* `TauCeti.Symbol.IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_le`: the kernel
  bounds of the pieces.
* `TauCeti.Symbol.IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_right_le` and
  `TauCeti.Symbol.IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_left_le`: the
  increments of the piece kernels in each variable.
* `TauCeti.Symbol.IsUniform.hasSum_quantizationKernel_littlewoodPaleyPiece`: off the diagonal the
  kernel of `a` is the sum of the piece kernels.
* `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le`: the size estimate.
* `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_sub_right_le` and
  `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_sub_left_le`: the smoothness estimates.

## References

* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §4.3
  (the kernel estimates of pseudodifferential operators, by dyadic decomposition).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

noncomputable section

open MeasureTheory Real Filter Topology Metric Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-! ### Kernels of the Littlewood–Paley pieces -/

section Pieces

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- On the frequency support of the `j`-th piece, `‖ξ‖ ≤ 2^j φ.rOut`. -/
private theorem norm_mul_norm_coefficient_littlewoodPaleyPiece_le (a : Symbol n V W m) (j : ℕ)
    (x ξ : CoordinateSpace n) :
    ‖ξ‖ * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ ≤
      2 ^ j * φ.rOut * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ := by
  rcases le_or_gt (2 ^ j * φ.rOut) ‖ξ‖ with hξ | hξ
  · rw [a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ, norm_zero, mul_zero,
      mul_zero]
  · exact mul_le_mul_of_nonneg_right hξ.le (norm_nonneg _)

private theorem integrable_norm_mul_norm_coefficient_littlewoodPaleyPiece (a : Symbol n V W m)
    (j : ℕ) (x : CoordinateSpace n) :
    Integrable fun ξ ↦ ‖ξ‖ * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ :=
  (((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x).norm.const_mul
    (2 ^ j * φ.rOut)).mono'
    (continuous_norm.mul ((a.littlewoodPaleyPiece φ j).continuous_coefficient_slice x).norm
      ).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact norm_mul_norm_coefficient_littlewoodPaleyPiece_le φ a j x ξ)

/-- The first frequency moments of the pieces of a uniform symbol:
`∫ ‖ξ‖ ‖aⱼ(x, ξ)‖ dξ ≤ M (2^j)^(m + n + 1)`. -/
private theorem IsUniform.exists_integral_norm_mul_norm_coefficient_littlewoodPaleyPiece_le
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ M, 0 ≤ M ∧ ∀ (j : ℕ) (x : CoordinateSpace n),
      ∫ ξ, ‖ξ‖ * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ ≤
        M * ((2 : ℝ) ^ j) ^ (m + n + 1) := by
  obtain ⟨C₀, hC₀, h₀⟩ := ha.exists_integral_norm_coefficient_littlewoodPaleyPiece_le φ
  refine ⟨φ.rOut * C₀, mul_nonneg φ.rOut_pos.le hC₀, fun j x ↦ ?_⟩
  have hR : 0 ≤ (2 : ℝ) ^ j * φ.rOut := mul_nonneg (by positivity) φ.rOut_pos.le
  calc ∫ ξ, ‖ξ‖ * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖
      ≤ ∫ ξ, 2 ^ j * φ.rOut * ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ :=
        integral_mono (integrable_norm_mul_norm_coefficient_littlewoodPaleyPiece φ a j x)
          (((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x).norm.const_mul _)
          (norm_mul_norm_coefficient_littlewoodPaleyPiece_le φ a j x)
    _ = 2 ^ j * φ.rOut * ∫ ξ, ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖ :=
        integral_const_mul _ _
    _ ≤ 2 ^ j * φ.rOut * (C₀ * ((2 : ℝ) ^ j) ^ (m + n)) := mul_le_mul_of_nonneg_left (h₀ j x) hR
    _ = φ.rOut * C₀ * ((2 : ℝ) ^ j) ^ (m + n + 1) := by
        rw [Real.rpow_add_one (by positivity)]
        ring

/-- **Kernel bounds for the Littlewood–Paley pieces.** For a uniform symbol `a` of order `m` and
every `N`, the kernels of the pieces satisfy
`‖K_{aⱼ}(x, y)‖ ≤ C (2^j)^(m + n) (1 + 2^j ‖x - y‖)^(-N)`, uniformly in `j`, `x` and `y`: at
distance `2^{-j}` from the diagonal the kernel has the size `(2^j)^(m + n)`, and it decays rapidly
beyond. -/
theorem IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_le {a : Symbol n V W m}
    (ha : a.IsUniform) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (j : ℕ) (x y : CoordinateSpace n),
      ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y‖ ≤
        C * ((2 : ℝ) ^ j) ^ (m + n) * (1 + 2 ^ j * ‖x - y‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := ha.exists_integral_norm_coefficient_littlewoodPaleyPiece_le φ
  choose C hC0 hC using fun i : Fin n ↦
    ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] (List.replicate N i)
  set A := C₀ + ∑ i, C i
  have hCA (i : Fin n) : C i ≤ A :=
    (Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hC₀)
  have hC₀A : C₀ ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hC0 i)
  refine ⟨2 ^ N * (1 + √n ^ N) * ((2 * π) ^ n)⁻¹ * A,
    by have := hC₀.trans hC₀A; positivity, fun j x y ↦ ?_⟩
  -- The piece is a symbol of order `-n - 1`, to which the integration by parts applies.
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 (a.isSmoothing_littlewoodPaleyPiece φ j) (-n - 1)
  set t : ℝ := 2 ^ j
  have ht : 0 < t := by positivity
  have h₀' : ∫ ξ, ‖b.coefficient (x, ξ)‖ ≤ A * t ^ (m + n) := by
    rw [hb]
    exact (h₀ j x).trans (mul_le_mul_of_nonneg_right hC₀A (by positivity))
  have hN' (i : Fin n) : ∫ ξ, ‖mixedDeriv [] (List.replicate N i) b.coefficient x ξ‖ ≤
      A * t ^ (m + n) * t⁻¹ ^ N := by
    have hpow : t ^ (m - N + n) = t ^ (m + n) * t⁻¹ ^ N := by
      rw [show m - N + n = (m + n) - N by ring, Real.rpow_sub_natCast ht.ne', inv_pow,
        div_eq_mul_inv]
    rw [hb]
    refine (hC i j x).trans ?_
    rw [List.length_replicate, hpow, ← mul_assoc]
    gcongr
    exact hCA i
  have key := b.one_add_norm_div_pow_mul_norm_quantizationKernel_le (by linarith) (inv_pos.2 ht) N
    h₀' hN' y
  rw [div_inv_eq_mul, hb, mul_comm ‖x - y‖] at key
  have hP : 0 < (1 + t * ‖x - y‖) ^ N := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hP]
  calc ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y‖ * (1 + t * ‖x - y‖) ^ N
      = (1 + t * ‖x - y‖) ^ N * ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y‖ :=
        mul_comm _ _
    _ ≤ 2 ^ N * (1 + √n ^ N) * ((2 * π) ^ n)⁻¹ * (A * t ^ (m + n)) := key
    _ = 2 ^ N * (1 + √n ^ N) * ((2 * π) ^ n)⁻¹ * A * t ^ (m + n) := by ring

/-- **Increments of the piece kernels in the second variable.** For a uniform symbol `a` of order
`m`, `‖K_{aⱼ}(x, y) - K_{aⱼ}(x, y')‖ ≤ D (2^j)^(m + n + 1) ‖y - y'‖`. -/
theorem IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_right_le
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ D, 0 ≤ D ∧ ∀ (j : ℕ) (x y y' : CoordinateSpace n),
      ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y -
          quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y'‖ ≤
        D * ((2 : ℝ) ^ j) ^ (m + n + 1) * ‖y - y'‖ := by
  obtain ⟨M, hM0, hM⟩ :=
    ha.exists_integral_norm_mul_norm_coefficient_littlewoodPaleyPiece_le φ
  refine ⟨((2 * π) ^ n)⁻¹ * M, by positivity, fun j x y y' ↦ ?_⟩
  have h := norm_quantizationKernel_sub_quantizationKernel_right_le
    ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x)
    (integrable_norm_mul_norm_coefficient_littlewoodPaleyPiece φ a j x) y y'
  rw [finrank_euclideanSpace_fin] at h
  calc _ ≤ _ := h
    _ ≤ ((2 * π) ^ n)⁻¹ * ‖y - y'‖ * (M * ((2 : ℝ) ^ j) ^ (m + n + 1)) :=
        mul_le_mul_of_nonneg_left (hM j x) (by positivity)
    _ = ((2 * π) ^ n)⁻¹ * M * ((2 : ℝ) ^ j) ^ (m + n + 1) * ‖y - y'‖ := by ring

/-- The position derivatives of the pieces of a uniform symbol are bounded by `G (2^j)^m`. -/
private theorem IsUniform.exists_norm_fderiv_coefficient_littlewoodPaleyPiece_le
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ G, 0 ≤ G ∧ ∀ (j : ℕ) (w ξ : CoordinateSpace n),
      ‖fderiv ℝ (fun w ↦ (a.littlewoodPaleyPiece φ j).coefficient (w, ξ)) w‖ ≤
        G * ((2 : ℝ) ^ j) ^ m := by
  choose C hC0 hC using fun i : Fin n ↦
    ha.exists_norm_mixedDeriv_littlewoodPaleyPiece_le_two_pow φ [i] []
  obtain ⟨D, hD0, hD⟩ :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.exists_opNorm_le (F := V →L[ℂ] W)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ hC0 i
  refine ⟨D * ∑ i, C i, mul_nonneg hD0.le hsum, fun j w ξ ↦ ?_⟩
  rw [mul_assoc]
  refine hD (by positivity) fun i ↦ ?_
  have hi := mixedDeriv_spatialDeriv i (a.littlewoodPaleyPiece φ j) [] [] w ξ
  rw [mixedDeriv_nil_nil, List.nil_append] at hi
  rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, fderiv_coefficient_single, hi]
  have h := hC i j w ξ
  rw [List.length_nil, Nat.cast_zero, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ ↦ hC0 i) (Finset.mem_univ i)) (by positivity))

/-- The increments in the position of the pieces of a uniform symbol:
`∫ ‖aⱼ(x, ξ) - aⱼ(x', ξ)‖ dξ ≤ G (2^j)^(m + n) ‖x - x'‖`. -/
private theorem IsUniform.exists_integral_norm_coefficient_littlewoodPaleyPiece_sub_le
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ G, 0 ≤ G ∧ ∀ (j : ℕ) (x x' : CoordinateSpace n),
      ∫ ξ, ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ) -
          (a.littlewoodPaleyPiece φ j).coefficient (x', ξ)‖ ≤
        G * ((2 : ℝ) ^ j) ^ (m + n) * ‖x - x'‖ := by
  obtain ⟨G, hG0, hG⟩ := ha.exists_norm_fderiv_coefficient_littlewoodPaleyPiece_le φ
  set v := (volume : Measure (CoordinateSpace n)).real (ball 0 1)
  refine ⟨G * φ.rOut ^ n * v, by have := φ.rOut_pos; positivity, fun j x x' ↦ ?_⟩
  set R := (2 : ℝ) ^ j * φ.rOut
  have hR : 0 ≤ R := by have := φ.rOut_pos; positivity
  set c := G * ((2 : ℝ) ^ j) ^ m * ‖x - x'‖
  -- The increment is at most `c` by the mean value theorem, and vanishes off the ball of radius
  -- `R` that carries the piece.
  have hle (ξ : CoordinateSpace n) : ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ) -
      (a.littlewoodPaleyPiece φ j).coefficient (x', ξ)‖ ≤
        (closedBall (0 : CoordinateSpace n) R).indicator (fun _ ↦ c) ξ := by
    by_cases hξ : ξ ∈ closedBall (0 : CoordinateSpace n) R
    · rw [indicator_of_mem hξ]
      have hd : Differentiable ℝ fun w ↦ (a.littlewoodPaleyPiece φ j).coefficient (w, ξ) :=
        ((a.littlewoodPaleyPiece φ j).contDiff_coefficient_slice ξ).differentiable (by simp)
      exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun w _ ↦ hd w)
        (fun w _ ↦ hG j w ξ) (mem_univ x') (mem_univ x)
    · rw [indicator_of_notMem hξ]
      have hξ' : R ≤ ‖ξ‖ := by
        rw [mem_closedBall_zero_iff, not_le] at hξ
        exact hξ.le
      rw [a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ',
        a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x' hξ', sub_self, norm_zero]
  have hint : Integrable ((closedBall (0 : CoordinateSpace n) R).indicator fun _ ↦ c) :=
    (integrableOn_const (measure_closedBall_lt_top (x := (0 : CoordinateSpace n))).ne
      ).integrable_indicator measurableSet_closedBall
  calc ∫ ξ, ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ) -
        (a.littlewoodPaleyPiece φ j).coefficient (x', ξ)‖
      ≤ ∫ ξ, (closedBall (0 : CoordinateSpace n) R).indicator (fun _ ↦ c) ξ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _) hint
          (Eventually.of_forall hle)
    _ = R ^ n * v * c := by
        rw [integral_indicator_const _ measurableSet_closedBall,
          Measure.addHaar_real_closedBall _ _ hR, finrank_euclideanSpace_fin, smul_eq_mul]
    _ = G * φ.rOut ^ n * v * ((2 : ℝ) ^ j) ^ (m + n) * ‖x - x'‖ := by
        rw [Real.rpow_add (by positivity), Real.rpow_natCast, mul_pow]
        ring

/-- **Increments of the piece kernels in the first variable.** For a uniform symbol `a` of order
`m`, `‖K_{aⱼ}(x, y) - K_{aⱼ}(x', y)‖ ≤ D (2^j)^(m + n + 1) ‖x - x'‖`. -/
theorem IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_left_le
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ D, 0 ≤ D ∧ ∀ (j : ℕ) (x x' y : CoordinateSpace n),
      ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y -
          quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x' y‖ ≤
        D * ((2 : ℝ) ^ j) ^ (m + n + 1) * ‖x - x'‖ := by
  obtain ⟨M, hM0, hM⟩ :=
    ha.exists_integral_norm_mul_norm_coefficient_littlewoodPaleyPiece_le φ
  obtain ⟨G, hG0, hG⟩ := ha.exists_integral_norm_coefficient_littlewoodPaleyPiece_sub_le φ
  refine ⟨((2 * π) ^ n)⁻¹ * (M + G), by positivity, fun j x x' y ↦ ?_⟩
  have h := norm_quantizationKernel_sub_quantizationKernel_left_le
    ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x)
    (integrable_norm_mul_norm_coefficient_littlewoodPaleyPiece φ a j x)
    ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x') y
  rw [finrank_euclideanSpace_fin] at h
  -- Since `2^j ≥ 1`, the bound `G (2^j)^(m + n)` of the coefficient term is at most `G T`.
  have hT : ((2 : ℝ) ^ j) ^ (m + n) ≤ ((2 : ℝ) ^ j) ^ (m + n + 1) := by
    rw [Real.rpow_add_one (by positivity)]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two)
  set T := ((2 : ℝ) ^ j) ^ (m + n + 1)
  calc _ ≤ _ := h
    _ ≤ ((2 * π) ^ n)⁻¹ * (‖x - x'‖ * (M * T) + G * T * ‖x - x'‖) := by
        gcongr
        · exact hM j x
        · exact (hG j x x').trans (by gcongr)
    _ = ((2 * π) ^ n)⁻¹ * (M + G) * T * ‖x - x'‖ := by ring

/-- Away from the diagonal the piece kernels of a uniform symbol decay geometrically in `j`:
`‖K_{aⱼ}(x, z)‖ ≤ C δ^(-N) qʲ` when `‖x - z‖ ≥ δ > 0`, for some `N` and some `q < 1`. -/
private theorem IsUniform.exists_norm_quantizationKernel_littlewoodPaleyPiece_le_geometric
    {a : Symbol n V W m} (ha : a.IsUniform) :
    ∃ (N : ℕ) (C q : ℝ), 0 ≤ C ∧ 0 ≤ q ∧ q < 1 ∧ ∀ (j : ℕ) {δ : ℝ} (x z : CoordinateSpace n),
      0 < δ → δ ≤ ‖x - z‖ →
        ‖quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x z‖ ≤
          C * δ ^ (-(N : ℝ)) * q ^ j := by
  obtain ⟨N, hN⟩ := exists_nat_gt (m + n)
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le φ N
  refine ⟨N, C, (2 : ℝ) ^ (m + n - N), hC0, by positivity,
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith), fun j δ x z hδ hxz ↦ ?_⟩
  refine (hC j x z).trans ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rpow_mul_one_add_rpow_neg_le hδ hxz j) hC0

end Pieces

/-! ### The kernel as a sum of the piece kernels -/

section Sum

variable (φ : ContDiffBump (0 : CoordinateSpace n))

/-- The quantizations of the pieces `j ≤ J` at `x` converge to the quantization of `a` as
`J → ∞`: their sum is the quantization of `φ(2^{-J} ξ) a(x, ξ)`, and the cutoff tends to `1`. -/
private theorem tendsto_sum_quantizeSchwartzValue_littlewoodPaleyPiece (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Tendsto (fun J ↦ ∑ j ∈ Finset.range (J + 1),
        quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x) atTop
      (𝓝 (quantizeSchwartzValue a.coefficient u x)) := by
  set g : CoordinateSpace n → W := fun ζ ↦ 𝐞 ⟪ζ, x⟫ • a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)
  obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
  have hg : Integrable g := integrable_quantizeSchwartzValue_integrand
    (a.continuous_coefficient_slice x).aestronglyMeasurable hC (𝓕 u)
  -- The integrand of each piece is `ψⱼ(2πζ) g(ζ)`.
  have hpiece (j : ℕ) : quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x =
      ∫ ζ, φ.inhomogeneousLittlewoodPaley j ((2 * π) • ζ) • g ζ := by
    rw [quantizeSchwartzValue_def]
    congr 1 with ζ
    simp only [g, coefficient_littlewoodPaleyPiece, smul_apply]
    exact smul_comm _ _ _
  have hint (j : ℕ) : Integrable fun ζ ↦ φ.inhomogeneousLittlewoodPaley j ((2 * π) • ζ) • g ζ :=
    hg.norm.mono' ((((φ.contDiff_inhomogeneousLittlewoodPaley (n := 0) j).continuous.comp
      (continuous_const_smul _)).aestronglyMeasurable).smul hg.1)
      (ae_of_all _ fun ζ ↦ by
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _)
          (by simpa using φ.abs_inhomogeneousLittlewoodPaley_le_one j ((2 * π) • ζ)))
  have hsum (J : ℕ) : ∑ j ∈ Finset.range (J + 1),
      quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x =
        ∫ ζ, φ (((2 : ℝ) ^ J)⁻¹ • (2 * π) • ζ) • g ζ := by
    simp_rw [hpiece]
    rw [← integral_finsetSum _ fun j _ ↦ hint j]
    congr 1 with ζ
    rw [← Finset.sum_smul, φ.sum_inhomogeneousLittlewoodPaley_range]
  simp_rw [hsum]
  rw [quantizeSchwartzValue_def]
  refine tendsto_integral_of_dominated_convergence (fun ζ ↦ ‖g ζ‖)
    (fun J ↦ ((φ.continuous.comp ((continuous_const_smul _).comp
      (continuous_const_smul _))).aestronglyMeasurable).smul hg.1) hg.norm
    (fun J ↦ ae_of_all _ fun ζ ↦ ?_) (ae_of_all _ fun ζ ↦ ?_)
  · rw [norm_smul, Real.norm_of_nonneg φ.nonneg]
    exact mul_le_of_le_one_left (norm_nonneg _) φ.le_one
  · -- For `2^J ≥ ‖2πζ‖ / φ.rIn` the cutoff equals `1`.
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_ge_atTop
      (‖(2 * π) • ζ‖ / φ.rIn)] with J hJ
    rw [φ.one_of_mem_closedBall, one_smul]
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity),
      inv_mul_le_iff₀ (by positivity)]
    exact (div_le_iff₀ φ.rIn_pos).1 hJ

/-- The quantizations of the pieces at `x` are given by their kernels. -/
private theorem sum_quantizeSchwartzValue_littlewoodPaleyPiece_eq_integral [CompleteSpace V]
    [CompleteSpace W] (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u x =
      ∫ z, (∑ j ∈ Finset.range J,
        quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x z) (u z) := by
  have hint (j : ℕ) : Integrable fun z ↦
      quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x z (u z) := by
    have hK := (a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x
    refine (u.integrable.norm.const_mul (((2 * π) ^ n)⁻¹ *
      ∫ ξ, ‖(a.littlewoodPaleyPiece φ j).coefficient (x, ξ)‖)).mono'
      ((continuous_quantizationKernel_right hK).clm_apply u.continuous).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    simpa only [finrank_euclideanSpace_fin] using
      norm_quantizationKernel_le (a.littlewoodPaleyPiece φ j).coefficient x z
  simp_rw [sum_apply]
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  exact Finset.sum_congr rfl fun j _ ↦ quantizeSchwartzValue_eq_integral_quantizationKernel
    ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x) u

/-- The kernel of a uniform symbol is represented, on test functions supported away from `x`, by
the sum of the piece kernels: the partial sums converge with a bound `B ‖u z‖`. -/
private theorem IsUniform.quantizeSchwartzValue_eq_integral_tsum [CompleteSpace V]
    [CompleteSpace W] {a : Symbol n V W m} (ha : a.IsUniform) {x : CoordinateSpace n}
    {u : 𝓢(CoordinateSpace n, V)} (hx : x ∉ tsupport u) :
    quantizeSchwartzValue a.coefficient u x = ∫ z, (∑' j,
      quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x z) (u z) := by
  set K : ℕ → CoordinateSpace n → V →L[ℂ] W :=
    fun j ↦ quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x
  obtain ⟨N, C, q, hC0, hq0, hq1, hK⟩ :=
    ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le_geometric φ
  -- The support of `u` is at a distance `δ > 0` from `x`.
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport u).isOpen_compl x hx
  have hdist {z : CoordinateSpace n} (hz : z ∈ tsupport u) : δ ≤ ‖x - z‖ := by
    have := mt (@hball z) (not_not.2 hz)
    rwa [mem_ball, not_lt, dist_comm, dist_eq_norm] at this
  have hgeo := summable_geometric_of_lt_one hq0 hq1
  set B := C * δ ^ (-(N : ℝ)) * (1 - q)⁻¹
  have hpartial (J : ℕ) {z : CoordinateSpace n} (hz : z ∈ tsupport u) :
      ∑ j ∈ Finset.range J, ‖K j z‖ ≤ B := by
    calc ∑ j ∈ Finset.range J, ‖K j z‖ ≤ ∑ j ∈ Finset.range J, C * δ ^ (-(N : ℝ)) * q ^ j :=
          Finset.sum_le_sum fun j _ ↦ hK j x z hδ (hdist hz)
      _ ≤ ∑' j, C * δ ^ (-(N : ℝ)) * q ^ j :=
          (hgeo.mul_left _).sum_le_tsum _ fun j _ ↦ by positivity
      _ = B := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hlim : Tendsto (fun J ↦ ∫ z, (∑ j ∈ Finset.range J, K j z) (u z)) atTop
      (𝓝 (∫ z, (∑' j, K j z) (u z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ B * ‖u z‖)
      (fun J ↦ ((continuous_finsetSum _ fun j _ ↦ continuous_quantizationKernel_right
        ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x)).clm_apply
          u.continuous).aestronglyMeasurable)
      (u.integrable.norm.const_mul B) (fun J ↦ ae_of_all _ fun z ↦ ?_) (ae_of_all _ fun z ↦ ?_)
    · by_cases hz : z ∈ tsupport u
      · refine (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (hpartial J hz)) (norm_nonneg _))
      · simp [image_eq_zero_of_notMem_tsupport hz]
    · by_cases hz : z ∈ tsupport u
      · have hs : Summable fun j ↦ K j z :=
          Summable.of_norm_bounded (hgeo.mul_left (C * δ ^ (-(N : ℝ))))
            fun j ↦ hK j x z hδ (hdist hz)
        exact ((ContinuousLinearMap.apply ℂ W (u z)).continuous.tendsto _).comp
          hs.hasSum.tendsto_sum_nat
      · simp [image_eq_zero_of_notMem_tsupport hz]
  refine tendsto_nhds_unique (tendsto_sum_quantizeSchwartzValue_littlewoodPaleyPiece φ a u x) ?_
  simp_rw [sum_quantizeSchwartzValue_littlewoodPaleyPiece_eq_integral φ a u x]
  exact hlim.comp (tendsto_add_atTop_nat 1)

/-- The sum of the piece kernels of a uniform symbol is continuous off the diagonal, by locally
uniform convergence. -/
private theorem IsUniform.continuousOn_tsum_quantizationKernel_littlewoodPaleyPiece
    [CompleteSpace W] {a : Symbol n V W m} (ha : a.IsUniform) (x : CoordinateSpace n) :
    ContinuousOn (fun z ↦ ∑' j, quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x z)
      {x}ᶜ := by
  obtain ⟨N, C, q, -, hq0, hq1, hK⟩ :=
    ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le_geometric φ
  intro z₀ hz₀
  have hδ : 0 < ‖x - z₀‖ / 2 := half_pos (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hz₀)))
  -- On the closed set `{z | ‖x - z₀‖ / 2 ≤ ‖x - z‖}`, a neighbourhood of `z₀`, the series
  -- converges uniformly.
  have hs : {z | ‖x - z₀‖ / 2 ≤ ‖x - z‖} ∈ 𝓝 z₀ := by
    refine mem_of_superset (ball_mem_nhds z₀ hδ) fun z hz ↦ ?_
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_add_le (x - z) (z - z₀)
    rw [sub_add_sub_cancel] at this
    simp only [mem_ofPred_eq]
    linarith
  exact ((continuousOn_tsum (fun j ↦ (continuous_quantizationKernel_right
    ((a.isSmoothing_littlewoodPaleyPiece φ j).integrable_coefficient x)).continuousOn)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (C * (‖x - z₀‖ / 2) ^ (-(N : ℝ))))
    fun j z hz ↦ hK j x z hδ (by simpa only [mem_ofPred_eq] using hz)).continuousAt hs
    ).continuousWithinAt

/-- **The kernel as a sum of the piece kernels.** Off the diagonal, the kernel of a uniform symbol
is the sum of the absolutely convergent kernels of its Littlewood–Paley pieces. -/
theorem IsUniform.hasSum_quantizationKernel_littlewoodPaleyPiece [CompleteSpace V]
    [CompleteSpace W] {a : Symbol n V W m} (ha : a.IsUniform) {x y : CoordinateSpace n}
    (hxy : x ≠ y) :
    HasSum (fun j ↦ quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y)
      (offDiagonalKernel a x y) := by
  obtain ⟨N, C, q, -, hq0, hq1, hK⟩ :=
    ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le_geometric φ
  have hy : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hs : Summable fun j ↦ quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
      fun j ↦ hK j x y hy le_rfl
  have heq := eqOn_offDiagonalKernel_of_forall a isOpen_compl_singleton (by simp)
    (ha.continuousOn_tsum_quantizationKernel_littlewoodPaleyPiece φ x)
    (fun u _ hu ↦ ha.quantizeSchwartzValue_eq_integral_tsum φ fun hx ↦ hu hx rfl)
    (Ne.symm hxy : y ≠ x)
  exact heq ▸ hs.hasSum

end Sum

/-! ### The size and smoothness estimates -/

/-- A fixed bump function, used to cut symbols into Littlewood–Paley pieces. -/
private def standardBump : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, one_pos, one_lt_two⟩

/-- **The size estimate.** The kernel of a uniform symbol `a` of order `m` on `ℝⁿ` with
`m + n > 0` satisfies `‖K(x, y)‖ ≤ C ‖x - y‖^(-(m + n))` off the diagonal. -/
theorem IsUniform.exists_norm_offDiagonalKernel_le [CompleteSpace V] [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) (hm : 0 < m + n) :
    ∃ C, 0 ≤ C ∧ ∀ x y : CoordinateSpace n, x ≠ y →
      ‖offDiagonalKernel a x y‖ ≤ C * ‖x - y‖ ^ (-(m + n)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (m + n)
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le standardBump N
  obtain ⟨E, hE0, hE⟩ := exists_tsum_rpow_mul_one_add_rpow_neg_le hm hN
  refine ⟨C * E, mul_nonneg hC0 hE0, fun x y hxy ↦ ?_⟩
  obtain ⟨hsum, hle⟩ := hE _ (norm_pos_iff.2 (sub_ne_zero.2 hxy))
  rw [← (ha.hasSum_quantizationKernel_littlewoodPaleyPiece standardBump hxy).tsum_eq]
  refine (tsum_of_norm_bounded (hsum.mul_left C).hasSum fun j ↦ (hC j x y).trans_eq
    (mul_assoc _ _ _)).trans ?_
  rw [tsum_mul_left, mul_assoc]
  exact mul_le_mul_of_nonneg_left hle hC0

/-- The common step of the two smoothness estimates. If the increments of the piece kernels
between `(x, y)` and `(x', y')` are at most `D (2^j)^(m + n + 1) d`, and both points are at
distance at least `r / 2` from the diagonal, then the increment of the kernel is at most
`C d^δ r^(-(m + n + δ))`. -/
private theorem IsUniform.exists_norm_offDiagonalKernel_sub_le_of_increment [CompleteSpace V]
    [CompleteSpace W] {a : Symbol n V W m} (ha : a.IsUniform) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 0 < m + n + δ) {D : ℝ} (hD0 : 0 ≤ D) :
    ∃ C, 0 ≤ C ∧ ∀ {x y x' y' : CoordinateSpace n} {d r : ℝ}, 0 ≤ d → 0 < r →
      r / 2 ≤ ‖x - y‖ → r / 2 ≤ ‖x' - y'‖ →
      (∀ j : ℕ, ‖quantizationKernel (a.littlewoodPaleyPiece standardBump j).coefficient x y -
          quantizationKernel (a.littlewoodPaleyPiece standardBump j).coefficient x' y'‖ ≤
        D * ((2 : ℝ) ^ j) ^ (m + n + 1) * d) →
      ‖offDiagonalKernel a x y - offDiagonalKernel a x' y'‖ ≤ C * d ^ δ * r ^ (-(m + n + δ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((m + n + δ) / (1 - δ))
  have hN' : m + n + δ < N * (1 - δ) := (div_lt_iff₀ (by linarith)).1 hN
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_le standardBump N
  obtain ⟨E, hE0, hE⟩ := exists_norm_le_of_hasSum_of_le_of_le hm hδ0 hδ1 hN'
  refine ⟨E * D ^ δ * (2 * C) ^ (1 - δ) * 2 ^ (m + n + δ), by positivity,
    fun {x y x' y' d r} hd hr hxy hxy' hD ↦ ?_⟩
  have hr2 : 0 < r / 2 := half_pos hr
  have hsize (j : ℕ) {w z : CoordinateSpace n} (hwz : r / 2 ≤ ‖w - z‖) :
      ‖quantizationKernel (a.littlewoodPaleyPiece standardBump j).coefficient w z‖ ≤
        C * ((2 : ℝ) ^ j) ^ (m + n) * (1 + 2 ^ j * (r / 2)) ^ (-(N : ℝ)) :=
    (hC j w z).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
      (by gcongr) (by simp)) (by positivity))
  have hne {w z : CoordinateSpace n} (hwz : r / 2 ≤ ‖w - z‖) : w ≠ z :=
    sub_ne_zero.1 (norm_pos_iff.1 (hr2.trans_le hwz))
  have hL := (ha.hasSum_quantizationKernel_littlewoodPaleyPiece standardBump (hne hxy)).sub
    (ha.hasSum_quantizationKernel_littlewoodPaleyPiece standardBump (hne hxy'))
  refine (hE hL (by positivity : (0 : ℝ) ≤ 2 * C) hD0 hd hr2 hD (fun j ↦ ?_)).trans_eq ?_
  · refine (norm_sub_le _ _).trans ?_
    rw [two_mul, add_mul, add_mul]
    exact add_le_add (hsize j hxy) (hsize j hxy')
  · rw [Real.div_rpow hr.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul]
    ring

/-- **The smoothness estimate in the second variable.** The kernel of a uniform symbol `a` of
order `m` on `ℝⁿ` satisfies, for `0 < δ < 1` with `m + n + δ > 0`,
`‖K(x, y) - K(x, y')‖ ≤ C ‖y - y'‖^δ ‖x - y'‖^(-(m + n + δ))` whenever
`2 ‖y - y'‖ < ‖x - y'‖`. -/
theorem IsUniform.exists_norm_offDiagonalKernel_sub_right_le [CompleteSpace V] [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 0 < m + n + δ) :
    ∃ C, 0 ≤ C ∧ ∀ x y y' : CoordinateSpace n, 2 * ‖y - y'‖ < ‖x - y'‖ →
      ‖offDiagonalKernel a x y - offDiagonalKernel a x y'‖ ≤
        C * ‖y - y'‖ ^ δ * ‖x - y'‖ ^ (-(m + n + δ)) := by
  obtain ⟨D, hD0, hD⟩ :=
    ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_right_le standardBump
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_offDiagonalKernel_sub_le_of_increment hδ0 hδ1 hm hD0
  refine ⟨C, hC0, fun x y y' h ↦ ?_⟩
  have hd := norm_nonneg (y - y')
  -- Both `‖x - y‖` and `‖x - y'‖` are at least `r / 2`, with `r = ‖x - y'‖`.
  have hxy : ‖x - y'‖ / 2 ≤ ‖x - y‖ := by
    have := norm_add_le (x - y) (y - y')
    rw [sub_add_sub_cancel] at this
    linarith
  exact hC hd (by linarith) hxy (by linarith) fun j ↦ hD j x y y'

/-- **The smoothness estimate in the first variable.** The kernel of a uniform symbol `a` of order
`m` on `ℝⁿ` satisfies, for `0 < δ < 1` with `m + n + δ > 0`,
`‖K(x, y) - K(x', y)‖ ≤ C ‖x - x'‖^δ ‖x' - y‖^(-(m + n + δ))` whenever
`2 ‖x - x'‖ < ‖x' - y‖`. -/
theorem IsUniform.exists_norm_offDiagonalKernel_sub_left_le [CompleteSpace V] [CompleteSpace W]
    {a : Symbol n V W m} (ha : a.IsUniform) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : 0 < m + n + δ) :
    ∃ C, 0 ≤ C ∧ ∀ x x' y : CoordinateSpace n, 2 * ‖x - x'‖ < ‖x' - y‖ →
      ‖offDiagonalKernel a x y - offDiagonalKernel a x' y‖ ≤
        C * ‖x - x'‖ ^ δ * ‖x' - y‖ ^ (-(m + n + δ)) := by
  obtain ⟨D, hD0, hD⟩ :=
    ha.exists_norm_quantizationKernel_littlewoodPaleyPiece_sub_left_le standardBump
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_offDiagonalKernel_sub_le_of_increment hδ0 hδ1 hm hD0
  refine ⟨C, hC0, fun x x' y h ↦ ?_⟩
  have hd := norm_nonneg (x - x')
  -- Both `‖x - y‖` and `‖x' - y‖` are at least `r / 2`, with `r = ‖x' - y‖`.
  have hxy : ‖x' - y‖ / 2 ≤ ‖x - y‖ := by
    have := norm_add_le (x' - x) (x - y)
    rw [sub_add_sub_cancel, norm_sub_rev x' x] at this
    linarith
  exact hC hd (by linarith) hxy (by linarith) fun j ↦ hD j x x' y

end Symbol

end TauCeti
