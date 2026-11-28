/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.MvPowerSeries.HilbertSamuel

/-!
# Examples of formal power series Hilbert–Samuel functions

This file collects worked examples illustrating `Ideal.localQuotientHilbertSamuel` for ideals
in multivariate power series rings `MvPowerSeries σ K` and `TauCeti.hsLexStabilization`:

* the univariate fat point `K⟦X⟧ ⧸ (X²)` with Hilbert–Samuel function `(1, 2, 2, …)`;
* the ascending chain of univariate ideals `(X ^ max (N - j) 1)`, whose Hilbert–Samuel
  functions are pointwise nonincreasing (and hence lexicographically nonincreasing) and stabilize
  at `K⟦X⟧ ⧸ (X)`;
* in `K⟦X₀, X₁⟧`, the fat point `𝔪²` (`(1, 3, 3, …)`) and the smooth line `(X₀)`
  (`(1, 2, 3, 4, …)`), which are pointwise incomparable while the line is strictly smaller
  lexicographically;
* the counterexample sequence `f j ℓ = if j ≤ ℓ then 1 else 0`, which strictly decreases
  lexicographically without stabilizing, showing that realizability by ideals is essential in
  `TauCeti.hsLexStabilization`.
-/

namespace TauCeti

/-- For `K⟦X⟧ ⧸ (X²)`, the Hilbert–Samuel function takes value `1` at `0` and `2` for every
`ℓ ≥ 1`. -/
example (K : Type*) [Field K] :
    (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2} :
        Ideal (MvPowerSeries (Fin 1) K)).localQuotientHilbertSamuel 0 = 1 ∧
      ∀ ℓ, 1 ≤ ℓ →
        (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2} :
            Ideal (MvPowerSeries (Fin 1) K)).localQuotientHilbertSamuel ℓ = 2 := by
  refine ⟨by simp [localQuotientHilbertSamuel_span_singleton_X_pow_of_subsingleton],
    fun ℓ hℓ ↦ ?_⟩
  rw [localQuotientHilbertSamuel_span_singleton_X_pow_of_subsingleton,
    min_eq_right (by omega)]
  norm_num

/-- For `I_j = (X ^ max (N - j) 1) ⊆ K⟦X⟧`, the Hilbert–Samuel functions are pointwise
nonincreasing (and hence lexicographically nonincreasing) and stabilize at the constant function
`1` of `K⟦X⟧ ⧸ (X)` for `j ≥ N`. -/
example (K : Type*) [Field K] (N : ℕ) :
    let I : ℕ → Ideal (MvPowerSeries (Fin 1) K) :=
      fun j ↦ Ideal.span {MvPowerSeries.X 0 ^ max (N - j) 1}
    (∀ j ℓ, (I (j + 1)).localQuotientHilbertSamuel ℓ ≤ (I j).localQuotientHilbertSamuel ℓ) ∧
      ∀ j, N ≤ j →
        (I j).localQuotientHilbertSamuel =
          (Ideal.span {MvPowerSeries.X (0 : Fin 1)} :
            Ideal (MvPowerSeries (Fin 1) K)).localQuotientHilbertSamuel := by
  intro I
  refine ⟨fun j ℓ ↦ ?_, fun j hj ↦ ?_⟩
  · simp only [I, localQuotientHilbertSamuel_span_singleton_X_pow_of_subsingleton, Nat.cast_le]
    omega
  · have hmax : max (N - j) 1 = 1 := by omega
    simp [I, hmax]

/-- In `K⟦X₀, X₁⟧`, the length-three fat point `I₁ = 𝔪²` (`H = (1, 3, 3, 3, …)`) and the smooth
line `I₂ = (X₀)` (`H = (1, 2, 3, 4, …)`) have pointwise incomparable Hilbert–Samuel functions, yet
`H(I₂)` is strictly lexicographically smaller than `H(I₁)`. -/
example (K : Type*) [Field K] :
    let I₁ : Ideal (MvPowerSeries (Fin 2) K) :=
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) ^ 2
    let I₂ : Ideal (MvPowerSeries (Fin 2) K) := Ideal.span {MvPowerSeries.X 0}
    let H₁ := I₁.localQuotientHilbertSamuel
    let H₂ := I₂.localQuotientHilbertSamuel
    ¬ (H₂ ≤ H₁) ∧ ¬ (H₁ ≤ H₂) ∧ Pi.Lex (· < ·) (· < ·) H₂ H₁ := by
  intro I₁ I₂ H₁ H₂
  have hH₁ : ∀ n, 1 ≤ n → H₁ n = 3 := fun n hn ↦ by
    dsimp only [H₁, I₁]
    rw [Ideal.localQuotientHilbertSamuel_maximalIdeal_pow_succ 1 n,
      min_eq_left hn, MvPowerSeries.localQuotientHilbertSamuel_bot_eq_choose, Fintype.card_fin]
    norm_num
  have hH₂ : ∀ n, H₂ n = (n + 1 : ℕ∞) := fun n ↦ by
    simp [H₂, I₂, Nat.add_comm 1 n]
  have hH₁_0 : H₁ 0 = 1 :=
    Ideal.localQuotientHilbertSamuel_zero
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.pow_le_self two_ne_zero))
  refine ⟨fun hle ↦ ?_, fun hle ↦ ?_, ⟨1, fun j hj ↦ ?_, ?_⟩⟩
  · have h3 := hle 3
    rw [hH₂ 3, hH₁ 3 (by omega)] at h3
    norm_num at h3
  · have h1 := hle 1
    rw [hH₁ 1 le_rfl, hH₂ 1] at h1
    norm_num at h1
  · obtain rfl : j = 0 := by omega
    rw [hH₂ 0, hH₁_0]
    norm_num
  · rw [hH₂ 1, hH₁ 1 le_rfl]
    norm_num

/-- Realizability as Hilbert–Samuel functions is essential for `hsLexStabilization`: the sequence
`f j ℓ = if j ≤ ℓ then 1 else 0` decreases strictly in the lexicographic order at every step and
never stabilizes, and for `j ≥ 1` none of its terms is realized by any ideal of `A`. -/
example (A : Type*) [CommRing A] [IsLocalRing A] :
    let f : ℕ → ℕ → ℕ∞ := fun j ℓ ↦ if j ≤ ℓ then 1 else 0
    (∀ j, Pi.Lex (· < ·) (· < ·) (f (j + 1)) (f j)) ∧
      (∀ j₀, f (j₀ + 1) ≠ f j₀) ∧
      ∀ j, 1 ≤ j → ∀ I : Ideal A, I.localQuotientHilbertSamuel ≠ f j := by
  intro f
  refine ⟨fun j ↦ ⟨j, fun m hm ↦ ?_, ?_⟩, fun j₀ hEq ↦ ?_, fun j hj I hEq ↦ ?_⟩
  · simp [f, Nat.not_le_of_lt hm, Nat.not_le_of_lt (Nat.lt_succ_of_lt hm)]
  · simp [f]
  · have h := congr_fun hEq j₀
    simp [f] at h
  · have h0 : I.localQuotientHilbertSamuel 0 = 0 := by
      simpa [f, Nat.not_le_of_lt hj] using congr_fun hEq 0
    have htop : I = ⊤ := Ideal.localQuotientHilbertSamuel_eq_zero_iff.mp h0
    have hj_eq : I.localQuotientHilbertSamuel j = 1 := by
      simpa [f] using congr_fun hEq j
    rw [htop, Ideal.localQuotientHilbertSamuel_top] at hj_eq
    exact zero_ne_one hj_eq

end TauCeti
