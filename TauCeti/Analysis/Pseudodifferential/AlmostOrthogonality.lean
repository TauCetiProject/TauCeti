/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.Lp
public import TauCeti.Analysis.Pseudodifferential.Symbol.Dyadic
public import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint

/-!
# Littlewood–Paley pieces of a quantization on `L²`

Let `a` be a symbol of order `m` whose estimates are uniform in the position, and let
`aⱼ(x, ξ) = ψⱼ(ξ) a(x, ξ)` be its Littlewood–Paley pieces
(`TauCeti.Symbol.littlewoodPaleyPiece`), cut off to frequencies of size `2^j`. Each piece has
bounded frequency support, so its quantization `Tⱼ = Op(aⱼ)` is an integral operator with an
integrable kernel, bounded on every `Lᵖ`. This file proves two of the estimates on the operators
`Tⱼ` that enter the Cotlar–Stein almost-orthogonality lemma
(`TauCeti.norm_sum_le_of_almost_orthogonal`), the route to the `L²` boundedness of `Op(a)` for
`m = 0` (Calderón–Vaillancourt):

* the diagonal estimates `‖Tⱼ‖ ≤ C (2^j)^m`, uniformly bounded for `m = 0`;
* exact orthogonality `Tⱼ Tₖ† = 0` once the frequency supports of `aⱼ` and `aₖ` are disjoint,
  which happens as soon as `|j - k|` exceeds a constant depending only on the partition.

The second estimate rests on a formula for the kernel of `Op(a) Op(b)†` for symbols with
integrable frequency slices: by Plancherel's theorem in the middle variable,

`∫ K_a(x, y) K_b(z, y)† dy = ∫ exp(2πi ⟪ζ, x - z⟫) a(x, 2πζ) b(z, 2πζ)† dζ`

(`TauCeti.integral_quantizationKernel_comp_adjoint`). So the composition only sees the products
`a(x, ξ) b(z, ξ)†` at equal frequencies, and vanishes when these do. The products
`Tⱼ† Tₖ` in the other order are not zero; their decay in `|j - k|` comes from the regularity of `a`
in the position and is not treated here.

## Main results

* `TauCeti.Symbol.quantizeLp_comp_adjoint_eq_zero`: `Op(a) Op(b)† = 0` on `L²` when
  `a(x, ξ) b(z, ξ)† = 0` for all `x`, `z` and `ξ`.
* `TauCeti.Symbol.quantizeLittlewoodPaleyPiece`: the quantization of the `j`-th piece of a
  uniform symbol, as an operator on `Lᵖ`.
* `TauCeti.Symbol.IsUniform.exists_norm_quantizeLittlewoodPaleyPiece_le`: the diagonal estimates
  `‖Tⱼ‖ ≤ C (2^j)^m`.
* `TauCeti.Symbol.quantizeLittlewoodPaleyPiece_comp_adjoint_succ_eq_zero` and
  `TauCeti.Symbol.exists_quantizeLittlewoodPaleyPiece_comp_adjoint_eq_zero`: frequency
  orthogonality of the pieces.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VII, §2.
-/

public section

open scoped FourierTransform SchwartzMap RealInnerProductSpace ENNReal NNReal
open MeasureTheory Real FourierTransform Module ContinuousLinearMap

noncomputable section

namespace TauCeti

namespace Symbol

/-! ### Orthogonality of quantizations -/

section Orthogonality

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m₁ m₂ : ℝ}

/-- **Orthogonality of quantizations.** Let `a` and `b` be uniform symbols of orders below `-n`.
If `a(x, ξ) b(z, ξ)† = 0` for all positions `x`, `z` and every frequency `ξ`, for instance if the
frequency supports of `a` and `b` are disjoint, then `Op(a) Op(b)† = 0` on `L²`. -/
theorem quantizeLp_comp_adjoint_eq_zero (a : Symbol n V W m₁) (b : Symbol n V W m₂)
    (hm₁ : m₁ < -n) (hm₂ : m₂ < -n) (ha : a.IsUniform) (hb : b.IsUniform)
    (h : ∀ x z ξ, a.coefficient (x, ξ) ∘L adjoint (b.coefficient (z, ξ)) = 0) :
    a.quantizeLp 2 hm₁ ha ∘L adjoint (b.quantizeLp 2 hm₂ hb) = 0 := by
  obtain ⟨A₁, hA₁, hB₁⟩ := ha.exists_lintegral_enorm_quantizationKernel_le hm₁
  obtain ⟨A₂, hA₂, hB₂⟩ := hb.exists_lintegral_enorm_quantizationKernel_le hm₂
  -- The kernel of the composition is the kernel of the zero coefficient.
  have hzero (x z : CoordinateSpace n) :
      ∫ y, quantizationKernel a.coefficient x y ∘L adjoint (quantizationKernel b.coefficient z y) =
        0 := by
    rw [integral_quantizationKernel_comp_adjoint (a.integrable_coefficient hm₁ x)
      (b.integrable_coefficient hm₂ z) (b.continuous_coefficient_slice z)
      (hb.integrable_quantizationKernel hm₂ z)]
    simp only [h]
    exact quantizationKernel_zero x z
  have hA : ∀ᵐ x ∂(volume : Measure (CoordinateSpace n)), ∫⁻ z,
      ‖∫ y, quantizationKernel a.coefficient x y ∘L
        adjoint (quantizationKernel b.coefficient z y)‖ₑ ≤ (0 : ℝ≥0) :=
    ae_of_all _ fun x ↦ by simp [hzero]
  have hB : ∀ᵐ z ∂(volume : Measure (CoordinateSpace n)), ∫⁻ x,
      ‖∫ y, quantizationKernel a.coefficient x y ∘L
        adjoint (quantizationKernel b.coefficient z y)‖ₑ ≤ (0 : ℝ≥0) :=
    ae_of_all _ fun z ↦ by simp [hzero]
  rw [quantizeLp_eq_integralOperatorLp (ae_of_all _ hA₁) (ae_of_all _ hB₁),
    quantizeLp_eq_integralOperatorLp (ae_of_all _ hA₂) (ae_of_all _ hB₂),
    integralOperatorLp_comp_adjoint _ _ _ _ _ _ hA hB]
  refine ContinuousLinearMap.ext fun u ↦ integralOperatorLp_eq_iff.2 ?_
  filter_upwards [Lp.coeFn_zero W 2 (volume : Measure (CoordinateSpace n))] with x hx
  simp only [hzero, zero_apply, integral_zero, hx, Pi.zero_apply]

end Orthogonality

/-! ### The Littlewood–Paley pieces on `Lᵖ` -/

section Pieces

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  (φ : ContDiffBump (0 : CoordinateSpace n))

/-- The `j`-th Littlewood–Paley piece of a symbol, as a symbol of order `-(n + 1)`: its frequency
support is bounded, so it is a symbol of every order. -/
private def littlewoodPaleyPieceLow (a : Symbol n V W m) (j : ℕ) : Symbol n V W (-(n + 1)) :=
  ofBoundedFrequencySupport (a.littlewoodPaleyPiece φ j).coefficient
    (a.littlewoodPaleyPiece φ j).contDiff_coefficient (2 ^ j * φ.rOut)
    fun x _ hξ ↦ a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x hξ

private theorem coefficient_littlewoodPaleyPieceLow (a : Symbol n V W m) (j : ℕ) :
    (a.littlewoodPaleyPieceLow φ j).coefficient = (a.littlewoodPaleyPiece φ j).coefficient :=
  coefficient_ofBoundedFrequencySupport _ _ _ _

private theorem IsUniform.littlewoodPaleyPieceLow {a : Symbol n V W m} (ha : a.IsUniform)
    (j : ℕ) : (a.littlewoodPaleyPieceLow φ j).IsUniform :=
  (ha.littlewoodPaleyPiece φ j).ofBoundedFrequencySupport _ _

variable (p) in
/-- The quantization of the `j`-th Littlewood–Paley piece `ψⱼ(ξ) a(x, ξ)` of a uniform symbol
`a`, as a bounded operator `Lᵖ(ℝⁿ; V) → Lᵖ(ℝⁿ; W)` for `1 ≤ p ≤ ∞`: the piece has bounded
frequency support, so its kernel is integrable. It acts by the kernel of the piece
(`TauCeti.Symbol.coeFn_quantizeLittlewoodPaleyPiece`), on Schwartz functions as the quantization
of the piece (`TauCeti.Symbol.coeFn_quantizeLittlewoodPaleyPiece_toLp`), and for `a` of order `m`
its norm is at most `C (2^j)^m`
(`TauCeti.Symbol.IsUniform.exists_norm_quantizeLittlewoodPaleyPiece_le`). -/
def quantizeLittlewoodPaleyPiece (a : Symbol n V W m) (ha : a.IsUniform) (j : ℕ) :
    Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ]
      Lp W p (volume : Measure (CoordinateSpace n)) :=
  quantizeLp p (a.littlewoodPaleyPieceLow φ j) (by linarith) (ha.littlewoodPaleyPieceLow φ j)

variable {a : Symbol n V W m} {ha : a.IsUniform}

/-- The quantization of a Littlewood–Paley piece acts by the kernel of the piece. -/
theorem coeFn_quantizeLittlewoodPaleyPiece (j : ℕ)
    (u : Lp V p (volume : Measure (CoordinateSpace n))) :
    quantizeLittlewoodPaleyPiece p φ a ha j u =ᵐ[volume]
      fun x ↦ ∫ y, quantizationKernel (a.littlewoodPaleyPiece φ j).coefficient x y (u y) := by
  rw [← coefficient_littlewoodPaleyPieceLow]
  exact coeFn_quantizeLp u

/-- On Schwartz functions, the quantization of a Littlewood–Paley piece is the quantization
`Op(ψⱼ a)` of the piece. -/
theorem coeFn_quantizeLittlewoodPaleyPiece_toLp [CompleteSpace V] [CompleteSpace W] (j : ℕ)
    (u : 𝓢(CoordinateSpace n, V)) :
    quantizeLittlewoodPaleyPiece p φ a ha j (u.toLp p) =ᵐ[volume]
      quantizeSchwartzValue (a.littlewoodPaleyPiece φ j).coefficient u := by
  rw [← coefficient_littlewoodPaleyPieceLow]
  exact coeFn_quantizeLp_toLp u

/-- **Uniform bounds for the Littlewood–Paley pieces.** For a uniform symbol `a` of order `m`, the
quantization of the `j`-th piece has norm at most `C (2^j)^m` on every `Lᵖ`, with `C`
independent of `j`. For `m = 0` the pieces are uniformly bounded: these are the diagonal estimates
of the almost-orthogonality argument for the `L²` boundedness of `Op(a)`. -/
theorem IsUniform.exists_norm_quantizeLittlewoodPaleyPiece_le (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ j, ‖quantizeLittlewoodPaleyPiece p φ a ha j‖ ≤ C * ((2 : ℝ) ^ j) ^ m := by
  -- The integrated dyadic estimates give the hypotheses of the scale-invariant bound
  -- `norm_quantizeLp_le` with `A = D (2^j)^(m + n)` and `R = 2^{-j}`, so `‖Tⱼ‖ ≲ A Rⁿ`.
  obtain ⟨C₀, hC₀, h₀⟩ := ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] []
  choose C hC h₁ using fun i : Fin n ↦
    ha.exists_integral_norm_mixedDeriv_littlewoodPaleyPiece_le φ [] (List.replicate (n + 1) i)
  set D := C₀ + ∑ i, C i
  have hD₀ : C₀ ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ hC i)
  have hD (i : Fin n) : C i ≤ D :=
    (Finset.single_le_sum (fun i _ ↦ hC i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left hC₀)
  set K : ℝ := 2 ^ (n + 1) * (1 + √n ^ (n + 1)) * ((2 * π) ^ n)⁻¹ *
    ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹
  have hK : 0 ≤ K := by
    have : 0 ≤ ∫ w : CoordinateSpace n, ((1 + ‖w‖) ^ (n + 1))⁻¹ :=
      integral_nonneg fun w ↦ by positivity
    positivity
  refine ⟨K * D, mul_nonneg hK (hC₀.trans hD₀), fun j ↦ ?_⟩
  have ht : (0 : ℝ) < 2 ^ j := by positivity
  have hpow (k : ℕ) : (((2 : ℝ) ^ j)⁻¹) ^ k = ((2 : ℝ) ^ j) ^ (-(k : ℝ)) := by
    rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]
  refine (norm_quantizeLp_le (A := D * ((2 : ℝ) ^ j) ^ (m + n)) (R := ((2 : ℝ) ^ j)⁻¹)
    (inv_pos.2 ht) (fun x ↦ ?_) (fun x i ↦ ?_)).trans_eq ?_
  · rw [coefficient_littlewoodPaleyPieceLow]
    have h := h₀ j x
    simp only [mixedDeriv_nil_nil, List.length_nil, Nat.cast_zero, sub_zero] at h
    exact h.trans (by gcongr)
  · rw [coefficient_littlewoodPaleyPieceLow, hpow, mul_assoc, ← Real.rpow_add ht]
    refine (h₁ i j x).trans ?_
    rw [List.length_replicate]
    push_cast
    exact mul_le_mul (hD i) (le_of_eq (by ring_nf)) (by positivity) (hC₀.trans hD₀)
  · rw [hpow, show ((2 : ℝ) ^ j) ^ m = ((2 : ℝ) ^ j) ^ (m + n) * ((2 : ℝ) ^ j) ^ (-(n : ℝ)) by
      rw [← Real.rpow_add ht]; ring_nf]
    simp only [K]
    ring

end Pieces

/-! ### Orthogonality of separated Littlewood–Paley pieces -/

section PiecesOrthogonality

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m m' : ℝ}
  (φ : ContDiffBump (0 : CoordinateSpace n))

/-- **Frequency orthogonality of the Littlewood–Paley pieces.** If `2^j φ.rOut ≤ 2^k φ.rIn`, the
`j`-th piece of `a` and the `(k + 1)`-st piece of `b` have disjoint frequency supports, so
`Op(ψⱼ a) Op(ψₖ₊₁ b)† = 0` on `L²`. -/
theorem quantizeLittlewoodPaleyPiece_comp_adjoint_succ_eq_zero (a : Symbol n V W m)
    (b : Symbol n V W m') (ha : a.IsUniform) (hb : b.IsUniform) {j k : ℕ}
    (hjk : 2 ^ j * φ.rOut ≤ 2 ^ k * φ.rIn) :
    quantizeLittlewoodPaleyPiece 2 φ a ha j ∘L
      adjoint (quantizeLittlewoodPaleyPiece 2 φ b hb (k + 1)) = 0 := by
  refine quantizeLp_comp_adjoint_eq_zero _ _ _ _ _ _ fun x z ξ ↦ ?_
  simp only [coefficient_littlewoodPaleyPieceLow]
  rcases le_or_gt (2 ^ j * φ.rOut) ‖ξ‖ with h | h
  · rw [a.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ x h,
      ContinuousLinearMap.zero_comp]
  · rw [b.coefficient_littlewoodPaleyPiece_succ_eq_zero_of_norm_le φ z (h.le.trans hjk),
      map_zero, ContinuousLinearMap.comp_zero]

/-- **Frequency orthogonality of the Littlewood–Paley pieces**, in the other order: if
`2^j φ.rOut ≤ 2^k φ.rIn`, then `Op(ψₖ₊₁ a) Op(ψⱼ b)† = 0` on `L²`. -/
theorem quantizeLittlewoodPaleyPiece_succ_comp_adjoint_eq_zero (a : Symbol n V W m)
    (b : Symbol n V W m') (ha : a.IsUniform) (hb : b.IsUniform) {j k : ℕ}
    (hjk : 2 ^ j * φ.rOut ≤ 2 ^ k * φ.rIn) :
    quantizeLittlewoodPaleyPiece 2 φ a ha (k + 1) ∘L
      adjoint (quantizeLittlewoodPaleyPiece 2 φ b hb j) = 0 := by
  refine quantizeLp_comp_adjoint_eq_zero _ _ _ _ _ _ fun x z ξ ↦ ?_
  simp only [coefficient_littlewoodPaleyPieceLow]
  rcases le_or_gt (2 ^ j * φ.rOut) ‖ξ‖ with h | h
  · rw [b.coefficient_littlewoodPaleyPiece_eq_zero_of_le_norm φ z h, map_zero,
      ContinuousLinearMap.comp_zero]
  · rw [a.coefficient_littlewoodPaleyPiece_succ_eq_zero_of_norm_le φ x (h.le.trans hjk),
      ContinuousLinearMap.zero_comp]

/-- **Almost orthogonality of the Littlewood–Paley pieces in frequency.** There is an `N`,
depending only on the bump function `φ`, such that `Op(ψⱼ a) Op(ψₖ b)† = 0` and
`Op(ψₖ a) Op(ψⱼ b)† = 0` on `L²` whenever `j + N ≤ k`. In the Cotlar–Stein lemma only the
finitely many terms with `|j - k| < N` remain in the sums of `√‖Tⱼ Tₖ†‖`. -/
theorem exists_quantizeLittlewoodPaleyPiece_comp_adjoint_eq_zero :
    ∃ N : ℕ, ∀ {m m' : ℝ} (a : Symbol n V W m) (b : Symbol n V W m') (ha : a.IsUniform)
      (hb : b.IsUniform) (j k : ℕ), j + N ≤ k →
      quantizeLittlewoodPaleyPiece 2 φ a ha j ∘L
          adjoint (quantizeLittlewoodPaleyPiece 2 φ b hb k) = 0 ∧
        quantizeLittlewoodPaleyPiece 2 φ a ha k ∘L
          adjoint (quantizeLittlewoodPaleyPiece 2 φ b hb j) = 0 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (φ.rOut / φ.rIn) one_lt_two
  rw [div_lt_iff₀ φ.rIn_pos] at hN
  refine ⟨N + 1, fun a b ha hb j k hjk ↦ ?_⟩
  obtain _ | k := k
  · omega
  have h : 2 ^ j * φ.rOut ≤ 2 ^ k * φ.rIn :=
    calc 2 ^ j * φ.rOut ≤ 2 ^ j * (2 ^ N * φ.rIn) := by
          gcongr
      _ = 2 ^ (j + N) * φ.rIn := by ring
      _ ≤ 2 ^ k * φ.rIn :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) φ.rIn_pos.le
  exact ⟨quantizeLittlewoodPaleyPiece_comp_adjoint_succ_eq_zero φ a b ha hb h,
    quantizeLittlewoodPaleyPiece_succ_comp_adjoint_eq_zero φ a b ha hb h⟩

end PiecesOrthogonality

end Symbol

end TauCeti
