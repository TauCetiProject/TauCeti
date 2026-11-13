/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.ProdInner
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Microlocal elliptic regularity for constant-coefficient operators

Let `P = ∑ i ∈ s, c i ∂^(m i)` be a linear differential operator with constant complex
coefficients `c i` and iterated directional derivatives `∂^(m i)` of orders `k i ≤ M`. Its
principal symbol of order `M`, in the geometric convention without factors of `i`, is the
homogeneous polynomial

`σ_M(P)(ξ) = ∑ i ∈ s with k i = M, c i ∏ₗ ⟪m i l, ξ⟫`,

and its *characteristic set* consists of the covectors `ξ ≠ 0` with `σ_M(P)(ξ) = 0`. This file
proves **microlocal elliptic regularity**: at a noncharacteristic covector, `T` is as regular as
`P T`,

`WF(T) ⊆ WF(P T) ∪ Char(P)`

(`Distribution.waveFrontSet_subset_union_sum_smul_iteratedLineDerivOp`). Together with the reverse
microlocality `WF(P T) ⊆ WF(T)` of differential operators, an operator elliptic in the sense that
`σ_M(P)` vanishes nowhere off zero satisfies `WF(P T) = WF(T)`, and hence has the same singular
support: `P T` is smooth on an open set exactly when `T` is. The Laplacian is the basic example
(`Distribution.waveFrontSet_sum_iteratedLineDerivOp_orthonormalBasis`).

## The argument

Write `L(T, ψ)(η) = T (ψ e_η)` for the localized Fourier transform, and
`p(η) = ∑ i ∈ s, c i ∏ₗ 2πi ⟪m i l, η⟫` for the full symbol of `P` in the frequency variable of
Mathlib's Fourier transform. Moving the derivatives onto the cutoff,
`L(∂_v T, ψ) = 2πi ⟪v, η⟫ L(T, ψ) - L(T, ∂_v ψ)`, gives

`p(η) L(T, ψ)(η) = L(P T, ψ)(η) - ∑ i ∈ s, c i D_i(η)`,

where each error `D_i` only involves `L(T, ∂^β ψ)` for derivatives of `ψ`, with one power of `η`
less than `p`. Near a noncharacteristic `(x, ξ)`, `|p(η)| ≥ c (1 + ‖η‖) ^ M` on an open cone `Γ`
around `ξ` for large `η`, while `L(P T, ψ)` decays rapidly on `Γ` for every cutoff `ψ`
supported in a fixed neighbourhood of `x`. If every `L(T, ψ)` with such `ψ` is
`O((1 + ‖η‖) ^ (k - j))` on `Γ`, the identity shows that it is `O((1 + ‖η‖) ^ (k - j - 1))`. The
induction starts from the polynomial growth of the localized Fourier transform, with a degree
`k` uniform over the cutoffs supported in a fixed compact set
(`Distribution.exists_forall_norm_localFourier_le`), and gives rapid decay on `Γ`.

## Main results

* `Distribution.IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp`: if `P T` is
  microlocally smooth at `(x, ξ)` and `σ_M(P)(ξ) ≠ 0`, then `T` is microlocally smooth there.
* `Distribution.waveFrontSet_subset_union_sum_smul_iteratedLineDerivOp`:
  `WF(T) ⊆ WF(P T) ∪ Char(P)`.
* `Distribution.waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`,
  `Distribution.singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero`: an elliptic
  constant-coefficient operator preserves the wave front set and the singular support.
* `Distribution.waveFrontSet_sum_iteratedLineDerivOp_orthonormalBasis`: `WF(Δ T) = WF(T)` for the
  Laplacian `Δ = ∑ ∂_{b i} ∂_{b i}` of an orthonormal basis `b`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.3.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter LineDeriv Real Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Opens E}

/-! ### Polynomial bounds for the symbol -/

/-- The factor `2πi ⟪v, η⟫` contributed by a derivative `∂_v` is bounded by
`2π ‖v‖ (1 + ‖η‖)`. -/
private theorem norm_two_pi_I_inner_le (v η : E) :
    ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * π * ‖v‖ * (1 + ‖η‖) := by
  calc ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ = 2 * π * |⟪v, η⟫| := by
        simp [abs_of_pos Real.pi_pos]
    _ ≤ 2 * π * (‖v‖ * (1 + ‖η‖)) := by
        gcongr
        exact (abs_real_inner_le_norm v η).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (norm_nonneg v))
    _ = 2 * π * ‖v‖ * (1 + ‖η‖) := by ring

/-- The symbol of `∂^m` in the frequency variable of the localized Fourier transform is
`(2πi) ^ r` times the product of the inner products. -/
private theorem prod_two_pi_I_inner {r : ℕ} (m : Fin r → E) (η : E) :
    ∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ) = (2 * π * I) ^ r * ∏ l, (⟪m l, η⟫ : ℂ) := by
  rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]

/-- The principal symbol is positively homogeneous of degree `M`. -/
private theorem principalSymbol_smul {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (M : ℕ) (t : ℝ) (η : E) :
    ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, t • η⟫ : ℂ) =
      (t : ℂ) ^ M * ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, η⟫ : ℂ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hki : k i = M := (Finset.mem_filter.1 hi).2
  have hprod : ∏ l, (⟪m i l, t • η⟫ : ℂ) = (t : ℂ) ^ k i * ∏ l, (⟪m i l, η⟫ : ℂ) := by
    simp only [inner_smul_right, ofReal_mul]
    rw [← Finset.pow_card_mul_prod, Finset.card_univ, Fintype.card_fin]
  have hpow : (t : ℂ) ^ k i = (t : ℂ) ^ M := by rw [hki]
  rw [hprod, hpow]
  ring

/-- **An elliptic cone.** If the principal symbol does not vanish at `ξ`, then it is bounded
below by `c₀ ‖η‖ ^ M` on an open cone around `ξ`, for some `c₀ > 0`. -/
private theorem exists_cone_le_norm_principalSymbol {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} {ξ : E}
    (hξ : ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) ≠ 0) :
    ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ η ∈ Γ,
        c₀ * ‖η‖ ^ M ≤ ‖∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, η⟫ : ℂ)‖ := by
  -- `‖ξ‖ ^ M ≠ 0`: otherwise `ξ = 0` and `M ≠ 0`, and every term of the principal symbol at `ξ`
  -- has a factor `⟪_, 0⟫ = 0`.
  have hξM : 0 < ‖ξ‖ ^ M := by
    rcases eq_or_ne ξ 0 with rfl | hξ0
    · rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp
      · refine absurd (Finset.sum_eq_zero fun i hi ↦ ?_) hξ
        have hki : k i = M := (Finset.mem_filter.1 hi).2
        rw [Finset.prod_eq_zero (i := ⟨0, hki ▸ hM⟩) (Finset.mem_univ _) (by simp), mul_zero]
    · exact pow_pos (norm_pos_iff.2 hξ0) M
  have hσξ := norm_pos_iff.2 hξ
  refine ⟨{η | ‖∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ)‖ / (2 * ‖ξ‖ ^ M) * ‖η‖ ^ M <
      ‖∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, η⟫ : ℂ)‖}, isOpen_lt (by fun_prop) (by fun_prop),
    ?_, fun t ht η hη ↦ ?_, _, by positivity, fun η hη ↦ hη.le⟩
  · simp only [mem_ofPred_eq]
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hξM.ne']
    linarith
  · simp only [mem_ofPred_eq] at hη ⊢
    rw [principalSymbol_smul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg ht.le, norm_smul, Real.norm_of_nonneg ht.le, mul_pow, mul_left_comm]
    exact mul_lt_mul_of_pos_left hη (pow_pos ht M)

/-- **The full symbol is elliptic at large frequencies.** If all orders are at most `M` and the
principal symbol is bounded below by `c₀ ‖η‖ ^ M` on `Γ`, then the full symbol
`∑ i ∈ s, c i ∏ₗ 2πi ⟪m i l, η⟫` is bounded below by a multiple of `(1 + ‖η‖) ^ M` on `Γ` outside a
ball: the terms of lower order are smaller by a factor `‖η‖`. -/
private theorem exists_le_norm_symbol {ι : Type*} {s : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M) {Γ : Set E} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hΓ : ∀ η ∈ Γ, c₀ * ‖η‖ ^ M ≤ ‖∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, η⟫ : ℂ)‖) :
    ∃ R c' : ℝ, 0 < c' ∧ ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ := by
  set A : ℝ := ∑ i ∈ s with k i ≠ M, ‖c i‖ * ((2 * π) ^ k i * ∏ l, ‖m i l‖)
  set B : ℝ := (2 * π) ^ M * c₀
  have hB : 0 < B := by positivity
  have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp [abs_of_pos pi_pos]
  refine ⟨max 1 (2 * A / B), B / 2 ^ (M + 1), by positivity, fun η hη hR ↦ ?_⟩
  have h1 : 1 ≤ ‖η‖ := (le_max_left _ _).trans hR
  have hAη : 2 * A ≤ B * ‖η‖ := by
    rw [mul_comm B]
    exact (div_le_iff₀ hB).1 ((le_max_right _ _).trans hR)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i ↦ k i = M)]
  -- The terms of order `M` give `(2πi) ^ M` times the principal symbol.
  have htop : ∑ i ∈ s with k i = M, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ) =
      (2 * π * I) ^ M * ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, η⟫ : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hpow : (2 * π * I : ℂ) ^ k i = (2 * π * I) ^ M := by rw [(Finset.mem_filter.1 hi).2]
    rw [prod_two_pi_I_inner, hpow]
    ring
  -- The terms of order less than `M` are bounded by `A ‖η‖ ^ M / ‖η‖`.
  have hlow : ‖∑ i ∈ s with ¬k i = M, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ * ‖η‖ ≤
      A * ‖η‖ ^ M := by
    refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hki : k i + 1 ≤ M := by
      have := hk i (Finset.mem_filter.1 hi).1
      have := (Finset.mem_filter.1 hi).2
      omega
    rw [prod_two_pi_I_inner, norm_mul, norm_mul, norm_pow, h2π]
    calc ‖c i‖ * ((2 * π) ^ k i * ‖∏ l, (⟪m i l, η⟫ : ℂ)‖) * ‖η‖
        ≤ ‖c i‖ * ((2 * π) ^ k i * ((∏ l, ‖m i l‖) * ‖η‖ ^ k i)) * ‖η‖ := by
          gcongr
          rw [← ofReal_prod, norm_real]
          simpa using TauCeti.norm_prod_inner_le (𝕜 := ℝ) Finset.univ (m i) η
      _ = ‖c i‖ * ((2 * π) ^ k i * ∏ l, ‖m i l‖) * ‖η‖ ^ (k i + 1) := by ring
      _ ≤ ‖c i‖ * ((2 * π) ^ k i * ∏ l, ‖m i l‖) * ‖η‖ ^ M :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hki) (by positivity)
  set L := ‖∑ i ∈ s with ¬k i = M, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖
  have hL : L ≤ B / 2 * ‖η‖ ^ M := by
    refine le_of_mul_le_mul_right ?_ (zero_lt_one.trans_le h1)
    nlinarith [pow_nonneg (norm_nonneg η) M]
  have hpow : (1 + ‖η‖) ^ M ≤ 2 ^ M * ‖η‖ ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) M
  have htop' : B * ‖η‖ ^ M ≤
      ‖∑ i ∈ s with k i = M, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ := by
    rw [htop, norm_mul, norm_pow, h2π]
    calc B * ‖η‖ ^ M = (2 * π) ^ M * (c₀ * ‖η‖ ^ M) := by simp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hΓ η hη) (by positivity)
  calc B / 2 ^ (M + 1) * (1 + ‖η‖) ^ M ≤ B / 2 ^ (M + 1) * (2 ^ M * ‖η‖ ^ M) := by gcongr
    _ = B * ‖η‖ ^ M - B / 2 * ‖η‖ ^ M := by
        rw [pow_succ]
        field_simp
        ring
    _ ≤ _ - L := by gcongr
    _ ≤ _ := by
        rw [sub_le_iff_le_add]
        exact htop'.trans (norm_le_add_norm_add _ _)

/-! ### Transfer of decay through derivatives -/

/-- **Each derivative costs one order of decay.** If the localized Fourier transforms of `T` with
cutoffs supported in `U` are `O((1 + ‖η‖) ^ k / (1 + ‖η‖) ^ j)` on `Γ`, those of `∂^m T`, for
`r` directions `m`, are `O((1 + ‖η‖) ^ (k + r) / (1 + ‖η‖) ^ j)`. -/
private theorem exists_localFourier_iteratedLineDerivOp_le {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    {j k : ℕ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U) :
    ∃ C, ∀ η ∈ Γ,
      (1 + ‖η‖) ^ j * ‖(∂^{m} T).localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ (k + r) := by
  induction r generalizing ψ with
  | zero => simpa using hT ψ hψ
  | succ r ih =>
    obtain ⟨C₁, hC₁⟩ := ih (Fin.tail m) ψ hψ
    obtain ⟨C₂, hC₂⟩ := ih (Fin.tail m) (∂_{m 0} ψ) ((tsupport_lineDerivOp_subset ψ _).trans hψ)
    refine ⟨2 * π * ‖m 0‖ * C₁ + |C₂|, fun η hη ↦ ?_⟩
    have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
    rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp]
    calc (1 + ‖η‖) ^ j * ‖2 * π * I * ⟪m 0, η⟫ * (∂^{Fin.tail m} T).localFourier ψ η -
          (∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η‖
        ≤ (1 + ‖η‖) ^ j * (‖(2 * π * I * ⟪m 0, η⟫ : ℂ)‖ *
            ‖(∂^{Fin.tail m} T).localFourier ψ η‖ +
              ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η‖) := by
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (1 + ‖η‖) ^ j * (2 * π * ‖m 0‖ * (1 + ‖η‖) *
            ‖(∂^{Fin.tail m} T).localFourier ψ η‖ +
              ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η‖) := by
          gcongr
          exact norm_two_pi_I_inner_le _ _
      _ = 2 * π * ‖m 0‖ * (1 + ‖η‖) *
            ((1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier ψ η‖) +
              (1 + ‖η‖) ^ j * ‖(∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η‖ := by ring
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * (1 + ‖η‖) ^ (k + r)) +
            |C₂| * (1 + ‖η‖) ^ (k + r + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (hC₁ η hη) (by positivity)) <|
            (hC₂ η hη).trans <| mul_le_mul (le_abs_self _)
              (pow_le_pow_right₀ hw (Nat.le_succ _)) (by positivity) (abs_nonneg _)
      _ = (2 * π * ‖m 0‖ * C₁ + |C₂|) * (1 + ‖η‖) ^ (k + (r + 1)) := by ring

/-- **The symbol of an iterated derivative.** Under the hypothesis of
`exists_localFourier_iteratedLineDerivOp_le`, the localized Fourier transform of `∂^m T` is its
symbol `∏ₗ 2πi ⟪m l, η⟫` times that of `T`, up to an error decaying one order faster than the
bound on `∂^m T`. -/
private theorem exists_localFourier_iteratedLineDerivOp_sub_le {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    {j k : ℕ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k)
    {r : ℕ} (m : Fin r → E) (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U) :
    ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) * ‖(∂^{m} T).localFourier ψ η -
      (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ (k + r) := by
  induction r generalizing ψ with
  | zero => exact ⟨0, fun η _ ↦ by simp⟩
  | succ r ih =>
    obtain ⟨C₁, hC₁⟩ := ih (Fin.tail m) ψ hψ
    obtain ⟨C₂, hC₂⟩ := exists_localFourier_iteratedLineDerivOp_le hT (Fin.tail m) (∂_{m 0} ψ)
      ((tsupport_lineDerivOp_subset ψ _).trans hψ)
    refine ⟨2 * π * ‖m 0‖ * C₁ + C₂, fun η hη ↦ ?_⟩
    set a : ℂ := 2 * π * I * ⟪m 0, η⟫
    set D := (∂^{Fin.tail m} T).localFourier ψ η -
      (∏ l, (2 * π * I * ⟪Fin.tail m l, η⟫ : ℂ)) * T.localFourier ψ η
    set B := (∂^{Fin.tail m} T).localFourier (∂_{m 0} ψ) η
    have hid : (∂^{m} T).localFourier ψ η -
        (∏ l, (2 * π * I * ⟪m l, η⟫ : ℂ)) * T.localFourier ψ η = a * D - B := by
      rw [iteratedLineDerivOp_succ_left, localFourier_lineDerivOp, Fin.prod_univ_succ]
      simp only [a, D, B, Fin.tail]
      ring
    rw [hid]
    calc (1 + ‖η‖) ^ (j + 1) * ‖a * D - B‖ ≤ (1 + ‖η‖) ^ (j + 1) * (‖a‖ * ‖D‖ + ‖B‖) := by
          gcongr
          exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (1 + ‖η‖) ^ (j + 1) * (2 * π * ‖m 0‖ * (1 + ‖η‖) * ‖D‖ + ‖B‖) := by
          gcongr
          exact norm_two_pi_I_inner_le _ _
      _ = 2 * π * ‖m 0‖ * (1 + ‖η‖) * ((1 + ‖η‖) ^ (j + 1) * ‖D‖) +
            (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖B‖) := by ring
      _ ≤ 2 * π * ‖m 0‖ * (1 + ‖η‖) * (C₁ * (1 + ‖η‖) ^ (k + r)) +
            (1 + ‖η‖) * (C₂ * (1 + ‖η‖) ^ (k + r)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hC₁ η hη) (by positivity))
            (mul_le_mul_of_nonneg_left (hC₂ η hη) (by positivity))
      _ = (2 * π * ‖m 0‖ * C₁ + C₂) * (1 + ‖η‖) ^ (k + (r + 1)) := by ring

/-- **The symbol identity.** Moving the derivatives of `P` onto the cutoff writes
`p(η) L(T, ψ)(η)` as `L(P T, ψ)(η)` minus errors that decay one order faster than
`L(∂^(m i) T, ψ)`. Hence, if `P T` has localized Fourier transforms `O((1 + ‖η‖) ^ -(j + 1))` on
`Γ` and those of `T` are `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)`, then
`p(η) L(T, ψ)(η) = O((1 + ‖η‖) ^ (k₀ + M) / (1 + ‖η‖) ^ (j + 1))` on `Γ`. -/
private theorem exists_symbol_mul_localFourier_le {ι : Type*} {s : Finset ι} {c : ι → ℂ}
    {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M) {T : 𝓓'(Ω, ℂ)}
    {U Γ : Set E} {j k₀ : ℕ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k₀)
    (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U) {Cp : ℝ} (hCp : ∀ η ∈ Γ,
      (1 + ‖η‖) ^ (j + 1) * ‖(∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η‖ ≤ Cp) :
    ∃ S, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) *
      ‖(∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η‖ ≤
        S * (1 + ‖η‖) ^ (k₀ + M) := by
  choose Cd hCd using fun i ↦ exists_localFourier_iteratedLineDerivOp_sub_le hT (m i) ψ hψ
  refine ⟨|Cp| + ∑ i ∈ s, ‖c i‖ * |Cd i|, fun η hη ↦ ?_⟩
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  have hwM : 1 ≤ (1 + ‖η‖) ^ (k₀ + M) := one_le_pow₀ hw
  set D : ι → ℂ := fun i ↦ (∂^{m i} T).localFourier ψ η -
    (∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η
  have hid : (∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)) * T.localFourier ψ η =
      (∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η - ∑ i ∈ s, c i * D i := by
    rw [localFourier_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [localFourier_smul]
    ring
  rw [hid]
  calc (1 + ‖η‖) ^ (j + 1) *
        ‖(∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η - ∑ i ∈ s, c i * D i‖
      ≤ (1 + ‖η‖) ^ (j + 1) * (‖(∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η‖ +
          ∑ i ∈ s, ‖c i‖ * ‖D i‖) := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ = (1 + ‖η‖) ^ (j + 1) * ‖(∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η‖ +
          ∑ i ∈ s, ‖c i‖ * ((1 + ‖η‖) ^ (j + 1) * ‖D i‖) := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ ≤ |Cp| * (1 + ‖η‖) ^ (k₀ + M) +
          ∑ i ∈ s, ‖c i‖ * (|Cd i| * (1 + ‖η‖) ^ (k₀ + M)) := by
        refine add_le_add ((hCp η hη).trans ((le_abs_self _).trans
          (le_mul_of_one_le_right (abs_nonneg _) hwM))) (Finset.sum_le_sum fun i hi ↦ ?_)
        refine mul_le_mul_of_nonneg_left ((hCd i η hη).trans ?_) (norm_nonneg _)
        exact mul_le_mul (le_abs_self _) (pow_le_pow_right₀ hw (by have := hk i hi; omega))
          (by positivity) (abs_nonneg _)
    _ = (|Cp| + ∑ i ∈ s, ‖c i‖ * |Cd i|) * (1 + ‖η‖) ^ (k₀ + M) := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **One step of the regularity induction.** Suppose that `P T` has rapidly decreasing localized
Fourier transforms on `Γ` for every cutoff supported in `U`, and that the full symbol of `P` is
bounded below by `c' (1 + ‖η‖) ^ M` on `Γ` outside a ball. If the localized Fourier transforms
of `T` with these cutoffs are `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)` on `Γ`, then they are
`O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ (j + 1))`. -/
private theorem exists_localFourier_le_succ {ι : Type*} {s : Finset ι} {c : ι → ℂ} {k : ι → ℕ}
    {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M) {T : 𝓓'(Ω, ℂ)} {U Γ : Set E}
    (hP : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U → ∀ N : ℕ, ∃ C, ∀ η ∈ Γ,
      (1 + ‖η‖) ^ N * ‖(∑ i ∈ s, c i • ∂^{m i} T).localFourier ψ η‖ ≤ C)
    {R c' : ℝ} (hc' : 0 < c') (hp : ∀ η ∈ Γ, R ≤ ‖η‖ →
      c' * (1 + ‖η‖) ^ M ≤ ‖∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖)
    {j k₀ : ℕ} (hT : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ U →
      ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k₀)
    (ψ : 𝓓(Ω, ℂ)) (hψ : tsupport ψ ⊆ U) :
    ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k₀ := by
  obtain ⟨C₀, hC₀⟩ := hT ψ hψ
  obtain ⟨Cp, hCp⟩ := hP ψ hψ (j + 1)
  obtain ⟨S, hS⟩ := exists_symbol_mul_localFourier_le hk hT ψ hψ hCp
  refine ⟨max ((1 + R) * C₀) (S / c'), fun η hη ↦ ?_⟩
  have hw : 1 ≤ 1 + ‖η‖ := le_add_of_nonneg_right (norm_nonneg η)
  rcases lt_or_ge ‖η‖ R with hηR | hηR
  · -- At bounded frequencies the extra factor `1 + ‖η‖` is at most `1 + R`.
    calc (1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖
        = (1 + ‖η‖) * ((1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖) := by ring
      _ ≤ (1 + R) * (C₀ * (1 + ‖η‖) ^ k₀) :=
          mul_le_mul (by linarith) (hC₀ η hη) (by positivity) (by linarith)
      _ = (1 + R) * C₀ * (1 + ‖η‖) ^ k₀ := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · -- At large frequencies divide the bound on `p(η) L(T, ψ)(η)` by `|p(η)| ≥ c' (1 + ‖η‖) ^ M`.
    have hpη := hp η hη hηR
    have hSη := hS η hη
    rw [norm_mul] at hSη
    have hkey : c' * (1 + ‖η‖) ^ M * ((1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖) ≤
        S * (1 + ‖η‖) ^ k₀ * (1 + ‖η‖) ^ M := by
      calc c' * (1 + ‖η‖) ^ M * ((1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖)
          ≤ ‖∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ *
              ((1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖) := by gcongr
        _ = (1 + ‖η‖) ^ (j + 1) * (‖∑ i ∈ s, c i * ∏ l, (2 * π * I * ⟪m i l, η⟫ : ℂ)‖ *
              ‖T.localFourier ψ η‖) := by ring
        _ ≤ S * (1 + ‖η‖) ^ (k₀ + M) := hSη
        _ = S * (1 + ‖η‖) ^ k₀ * (1 + ‖η‖) ^ M := by ring
    have hwMpos : 0 < (1 + ‖η‖) ^ M := by positivity
    calc (1 + ‖η‖) ^ (j + 1) * ‖T.localFourier ψ η‖ ≤ S / c' * (1 + ‖η‖) ^ k₀ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hc']
          nlinarith
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-! ### Microlocal elliptic regularity -/

variable [FiniteDimensional ℝ E]

/-- **Microlocal elliptic regularity for constant-coefficient operators** (Hörmander I,
Theorem 8.3.1). Let `P = ∑ i ∈ s, c i ∂^(m i)` have orders `k i ≤ M`, and let `ξ` be
noncharacteristic for `P`: the principal symbol `∑ i ∈ s with k i = M, c i ∏ₗ ⟪m i l, ξ⟫` does not
vanish. If `P T` is microlocally smooth at `(x, ξ)`, then so is `T`. -/
theorem IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp {ι : Type*} {s : Finset ι}
    {c : ι → ℂ} {k : ι → ℕ} {m : ∀ i, Fin (k i) → E} {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    {T : 𝓓'(Ω, ℂ)} {x ξ : E} (hP : (∑ i ∈ s, c i • ∂^{m i} T).IsMicrolocallySmoothAt x ξ)
    (hξ : ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) ≠ 0) :
    T.IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hP
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ₁, hΓ₁, hξ₁, hcone₁, hdecay⟩ := hP.exists_nhds_cone
  obtain ⟨Γ₂, hΓ₂, hξ₂, hcone₂, c₀, hc₀, hell⟩ := exists_cone_le_norm_principalSymbol hξ
  obtain ⟨R, c', hc', hp⟩ := exists_le_norm_symbol hk hc₀ hell
  -- A compact neighbourhood `K` of `x` on which `P T` is microlocally smooth along `Γ₁`.
  obtain ⟨K, hKx, hKsub, hKc⟩ := local_compact_nhds (inter_mem hU (Ω.isOpen.mem_nhds hx))
  obtain ⟨k₀, hk₀⟩ := exists_forall_norm_localFourier_le T (K := ⟨K, hKc⟩)
    (hKsub.trans inter_subset_right)
  -- By induction on `j`, every cutoff supported in `K` has localized Fourier transform
  -- `O((1 + ‖η‖) ^ k₀ / (1 + ‖η‖) ^ j)` on `Γ₁ ∩ Γ₂`.
  have hind (j : ℕ) : ∀ ψ : 𝓓(Ω, ℂ), tsupport ψ ⊆ K → ∃ C, ∀ η ∈ Γ₁ ∩ Γ₂,
      (1 + ‖η‖) ^ j * ‖T.localFourier ψ η‖ ≤ C * (1 + ‖η‖) ^ k₀ := by
    induction j with
    | zero =>
      intro ψ hψ
      obtain ⟨C, hC⟩ := hk₀ ψ hψ
      exact ⟨C, fun η _ ↦ by simpa using hC η⟩
    | succ j ih =>
      refine exists_localFourier_le_succ hk (fun ψ hψ N ↦ ?_) hc'
        (fun η (hη : η ∈ Γ₁ ∩ Γ₂) ↦ hp η hη.2) ih
      obtain ⟨C, hC⟩ := hdecay ψ (hψ.trans (hKsub.trans inter_subset_left)) N
      exact ⟨C, fun η hη ↦ hC η hη.1⟩
  obtain ⟨φ, hφK, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤) hKx
    (hKsub.trans inter_subset_right) (1 : ℂ)
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ₁ ∩ Γ₂, hΓ₁.inter hΓ₂, ⟨hξ₁, hξ₂⟩,
    fun t ht η hη ↦ ⟨hcone₁ t ht η hη.1, hcone₂ t ht η hη.2⟩, fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hind (k₀ + N) φ hφK
  refine ⟨C, fun η hη ↦ ?_⟩
  have hpos : 0 < (1 + ‖η‖) ^ k₀ := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (1 + ‖η‖) ^ k₀ * ((1 + ‖η‖) ^ N * ‖T.localFourier φ η‖)
      = (1 + ‖η‖) ^ (k₀ + N) * ‖T.localFourier φ η‖ := by ring
    _ ≤ C * (1 + ‖η‖) ^ k₀ := hC η hη
    _ = (1 + ‖η‖) ^ k₀ * C := mul_comm _ _

/-- **Microlocal elliptic regularity for constant-coefficient operators**:
`WF(T) ⊆ WF(P T) ∪ Char(P)` for `P = ∑ i ∈ s, c i ∂^(m i)` with orders `k i ≤ M`, where the
characteristic set is the zero set of the principal symbol
`∑ i ∈ s with k i = M, c i ∏ₗ ⟪m i l, ξ⟫`. -/
theorem waveFrontSet_subset_union_sum_smul_iteratedLineDerivOp {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (T : 𝓓'(Ω, ℂ)) :
    T.waveFrontSet ⊆ (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet ∪
      {p | ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, p.2⟫ : ℂ) = 0} := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hT⟩ := mem_waveFrontSet_iff.1 hp
  by_contra h
  rw [mem_union, not_or, mem_waveFrontSet_iff, mem_ofPred_eq] at h
  exact hT (IsMicrolocallySmoothAt.of_sum_smul_iteratedLineDerivOp hk
    (by simpa [hx, hξ] using h.1) h.2)

/-- **An elliptic constant-coefficient operator preserves the wave front set.** If the principal
symbol of `P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then
`WF(P T) = WF(T)`. -/
theorem waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E) {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).waveFrontSet = T.waveFrontSet := by
  refine subset_antisymm ((waveFrontSet_sum_subset s _).trans <| iUnion₂_subset fun i _ ↦
    (waveFrontSet_smul_subset _ _).trans (waveFrontSet_iteratedLineDerivOp_subset T (m i)))
    fun p hp ↦ ?_
  refine ((waveFrontSet_subset_union_sum_smul_iteratedLineDerivOp s c m hk T hp).resolve_right ?_)
  exact hσ p.2 (T.waveFrontSet_subset hp).2

/-- **Elliptic regularity for constant-coefficient operators.** If the principal symbol of
`P = ∑ i ∈ s, c i ∂^(m i)` of order `M` vanishes at no `ξ ≠ 0`, then `P T` and `T` have the same
singular support: `T` is a smooth function near every point near which `P T` is. -/
theorem singularSupport_sum_smul_iteratedLineDerivOp_of_forall_ne_zero [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} (s : Finset ι) (c : ι → ℂ) {k : ι → ℕ} (m : ∀ i, Fin (k i) → E)
    {M : ℕ} (hk : ∀ i ∈ s, k i ≤ M)
    (hσ : ∀ ξ : E, ξ ≠ 0 → ∑ i ∈ s with k i = M, c i * ∏ l, (⟪m i l, ξ⟫ : ℂ) ≠ 0)
    (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • ∂^{m i} T).singularSupport = T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet,
    waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero s c m hk hσ]

/-- **The Laplacian preserves the wave front set.** For an orthonormal basis `b` of `E`, the
Laplacian `Δ T = ∑ i, ∂_{b i} ∂_{b i} T` satisfies `WF(Δ T) = WF(T)`: its principal symbol
`∑ i, ⟪b i, ξ⟫ ^ 2 = ‖ξ‖ ^ 2` vanishes only at `ξ = 0`. -/
theorem waveFrontSet_sum_iteratedLineDerivOp_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i, ∂^{![b i, b i]} T).waveFrontSet = T.waveFrontSet := by
  have h := waveFrontSet_sum_smul_iteratedLineDerivOp_of_forall_ne_zero Finset.univ (fun _ ↦ 1)
    (k := fun _ ↦ 2) (fun i ↦ ![b i, b i]) (M := 2) (fun _ _ ↦ le_rfl) (fun ξ hξ ↦ ?_) T
  · simpa using h
  have hsum : ∑ i, ⟪b i, ξ⟫ * ⟪b i, ξ⟫ = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner ξ ξ]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]
  have hval : ∑ i ∈ Finset.univ with (2 : ℕ) = 2, (1 : ℂ) * ∏ l, (⟪![b i, b i] l, ξ⟫ : ℂ) =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hsum]
    simp [Fin.prod_univ_two]
  rw [hval]
  exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'

end Distribution
