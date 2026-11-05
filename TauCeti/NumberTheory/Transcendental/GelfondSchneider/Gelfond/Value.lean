/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.GelfondSchneider.Gelfond.Auxiliary

import TauCeti.NumberTheory.Height.House

/-!
# Liouville's lower bound for the value of Gelfond's auxiliary function

Let `K` be a number field of degree `h` and `α, β, γ ∈ K`. Gelfond's auxiliary function has
coefficients `η_{ab} ∈ 𝓞 K`, `a, b < q`, with `house η_{ab} ≤ c ^ n n ^ ((n + 1) / 2)`, where
`q ^ 2 = 2 m n` (`TauCeti.exists_gelfond_auxiliary_algebraic`). Its first nonvanishing derivative
at one of the points `t₀ ≤ m` (`RingHom.exists_iteratedDeriv_gelfond_auxiliary_ne_zero`), of order
`r ≥ n`, is `λ ^ r σ ρ` with

`ρ = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ r α ^ ((a + 1) t₀) γ ^ ((b + 1) t₀) ∈ K`.

This file bounds `|σ ρ|` from below for nonzero `ρ`, which is the arithmetic half of the final
contradiction in Gelfond's proof of the Gelfond–Schneider theorem. If `c₀ α`, `c₀ β`, `c₀ γ` are
algebraic integers, then `c₀ ^ (r + 2 q m) ρ` is a nonzero algebraic integer, of house at most
`X ^ r r ^ r` for a constant `X`, so Liouville's inequality
(`NumberField.one_le_norm_mul_house_pow`) gives

`1 ≤ c₂ ^ r r ^ ((h - 1) r) |σ ρ|`

for a constant `c₂` depending only on `K`, `α`, `β`, `γ`, `m` and `c`
(`TauCeti.exists_one_le_pow_mul_norm_gelfond_value`). The analytic upper bound for `|σ ρ|`,
which contradicts this for `m > 2 h + 1` and large `r`, is not part of this file.

## Main results

* `TauCeti.exists_one_le_pow_mul_norm_gelfond_value`: the lower bound above, uniform over the
  embeddings `σ : K →+* ℂ`.

## References

* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* K. Soundararajan (notes by I. Petrow), *Transcendental number theory*, Stanford Math 249A
  course notes (2011).
-/

public section

open Finset Module NumberField

namespace TauCeti

/-- The house bound for Gelfond's value `ρ`: if `q ^ 2 = 2 m n` with `m, n ≥ 1` and `n ≤ r`, the
bound `q ^ 2 (c ^ n n ^ ((n + 1) / 2)) (q ^ r H ^ (r + 2 q m))` is at most `X ^ r r ^ r` with
`X = 16 m ^ 2 max(1, |c|) H ^ (1 + 4 m ^ 2)`. -/
private theorem gelfond_value_bound_le {c H : ℝ} {m n q r : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hq : q * q = 2 * m * n) (hnr : n ≤ r) (hH : 1 ≤ H) :
    ((q * q : ℕ) : ℝ) * (c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) *
        ((q : ℝ) ^ r * H ^ (r + 2 * q * m)) ≤
      (16 * m ^ 2 * max 1 |c| * H ^ (1 + 4 * m ^ 2)) ^ r * (r : ℝ) ^ r := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hr : 1 ≤ r := hn.trans hnr
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  set c' := max 1 |c|
  have hc' : 1 ≤ c' := le_max_left _ _
  -- The five factors, each bounded in terms of `r`.
  have h₁ : ((q * q : ℕ) : ℝ) ≤ 2 * m * r := by
    rw [hq]
    push_cast
    gcongr
  have h₂ : c ^ n ≤ c' ^ r :=
    calc c ^ n ≤ |c| ^ n := (le_abs_self _).trans (abs_pow c n).le
      _ ≤ c' ^ n := pow_le_pow_left₀ (abs_nonneg c) (le_max_right _ _) n
      _ ≤ c' ^ r := pow_le_pow_right₀ hc' hnr
  have h₃ : (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ (r : ℝ) ^ (((r : ℝ) + 1) / 2) :=
    (Real.rpow_le_rpow (by positivity) hnr' (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hr' (by linarith))
  have h₄ : (q : ℝ) ^ r ≤ (2 * m) ^ r * (r : ℝ) ^ ((r : ℝ) / 2) :=
    (gelfond_natCast_pow_le (k := r) (j := r) hm hq (by omega)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hnr' (by positivity))
        (by positivity))
  have h₅ : H ^ (r + 2 * q * m) ≤ (H ^ (1 + 4 * m ^ 2)) ^ r := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ hH ?_
    have := gelfond_two_mul_mul_le hq hnr
    rw [add_mul, one_mul]
    omega
  -- The powers of `r`: `r r ^ ((r + 1) / 2) r ^ (r / 2) = r ^ (r + 3 / 2) ≤ 4 ^ r r ^ r`.
  have h₆ : (r : ℝ) * (r : ℝ) ^ (((r : ℝ) + 1) / 2) * (r : ℝ) ^ ((r : ℝ) / 2) ≤
      4 ^ r * (r : ℝ) ^ r := by
    have hr₀ : (0 : ℝ) < r := by linarith
    calc (r : ℝ) * (r : ℝ) ^ (((r : ℝ) + 1) / 2) * (r : ℝ) ^ ((r : ℝ) / 2)
        = (r : ℝ) ^ ((r : ℝ) + 3 / 2) := by
          nth_rewrite 1 [← Real.rpow_one (r : ℝ)]
          rw [← Real.rpow_add hr₀, ← Real.rpow_add hr₀]
          congr 1
          ring
      _ ≤ (r : ℝ) ^ ((r + 2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr' (by push_cast; linarith)
      _ = (r : ℝ) ^ 2 * (r : ℝ) ^ r := by
          rw [Real.rpow_natCast, pow_add, mul_comm]
      _ ≤ 4 ^ r * (r : ℝ) ^ r := by
          gcongr
          have : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast r.lt_two_pow_self.le
          calc (r : ℝ) ^ 2 ≤ (2 ^ r) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
            _ = 4 ^ r := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h₇ : (2 * m : ℝ) ≤ (2 * m) ^ r := le_self_pow₀ (by linarith) (by omega)
  calc ((q * q : ℕ) : ℝ) * (c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) *
        ((q : ℝ) ^ r * H ^ (r + 2 * q * m))
      ≤ (2 * m * r) * (c' ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) *
          ((2 * m) ^ r * (r : ℝ) ^ ((r : ℝ) / 2) * (H ^ (1 + 4 * m ^ 2)) ^ r) := by
        have hcn : c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤
            c' ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2) :=
          (mul_le_mul_of_nonneg_right h₂ (by positivity)).trans
            (mul_le_mul_of_nonneg_left h₃ (by positivity))
        have hq' : (0 : ℝ) ≤ ((q * q : ℕ) : ℝ) := by positivity
        calc ((q * q : ℕ) : ℝ) * (c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) *
              ((q : ℝ) ^ r * H ^ (r + 2 * q * m))
            ≤ ((q * q : ℕ) : ℝ) * (c' ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) *
                ((q : ℝ) ^ r * H ^ (r + 2 * q * m)) := by gcongr
          _ ≤ _ := by gcongr
    _ = (2 * m) * ((2 * m) ^ r * c' ^ r * (H ^ (1 + 4 * m ^ 2)) ^ r) *
          ((r : ℝ) * (r : ℝ) ^ (((r : ℝ) + 1) / 2) * (r : ℝ) ^ ((r : ℝ) / 2)) := by ring
    _ ≤ (2 * m) ^ r * ((2 * m) ^ r * c' ^ r * (H ^ (1 + 4 * m ^ 2)) ^ r) *
          (4 ^ r * (r : ℝ) ^ r) := by gcongr
    _ = (16 * m ^ 2 * c' * H ^ (1 + 4 * m ^ 2)) ^ r * (r : ℝ) ^ r := by
        have h16 : (16 : ℝ) ^ r = 2 ^ r * 2 ^ r * 4 ^ r := by
          rw [← mul_pow, ← mul_pow]
          norm_num
        simp only [mul_pow, h16]
        ring

variable {K : Type*} [Field K] [NumberField K]

/-- **Liouville's lower bound for Gelfond's values** (Karatarakis–Wiedijk, §3). Let `K` be a
number field of degree `h`, `α, β, γ ∈ K`, `m ∈ ℕ` and `c ∈ ℝ`. There is `c₂ ≥ 1` with the
following property. Let `n ≥ 1`, `q ^ 2 = 2 m n`, `r ≥ n` and `t₀ ≤ m`, and let
`η_{ab} ∈ 𝓞 K`, `a, b < q`, have house at most `c ^ n n ^ ((n + 1) / 2)`, as for Gelfond's
auxiliary function. If
`ρ = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ r α ^ ((a + 1) t₀) γ ^ ((b + 1) t₀)` is nonzero, then
`1 ≤ c₂ ^ r r ^ ((h - 1) r) |σ ρ|` for every embedding `σ : K →+* ℂ`. In particular
`|σ ρ| ≥ c₂ ^ (-r) r ^ (-(h - 1) (r + 1))`. -/
theorem exists_one_le_pow_mul_norm_gelfond_value (α β γ : K) (m : ℕ) (c : ℝ) :
    ∃ c₂ : ℝ, 1 ≤ c₂ ∧ ∀ (σ : K →+* ℂ) (n q r t₀ : ℕ) (η : Fin q → Fin q → 𝓞 K),
      1 ≤ n → q ^ 2 = 2 * m * n → n ≤ r → t₀ ≤ m →
      (∀ a b, NumberField.house (η a b : K) ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      ∑ a, ∑ b, (η a b : K) * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
          (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)) ≠ 0 →
      1 ≤ c₂ ^ r * (r : ℝ) ^ ((finrank ℚ K - 1) * r) *
        ‖σ (∑ a, ∑ b, (η a b : K) * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
          (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)))‖ := by
  obtain ⟨c₀, hc₀, H, hH, hc₀H, hterm⟩ := exists_intCast_pow_mul_gelfond_term α β γ
  set X := 16 * (m : ℝ) ^ 2 * max 1 |c| * H ^ (1 + 4 * m ^ 2)
  set H' := H ^ (1 + 4 * m ^ 2)
  have hH' : 1 ≤ H' := one_le_pow₀ hH
  refine ⟨H' * max 1 X ^ (finrank ℚ K - 1),
    one_le_mul_of_one_le_of_one_le hH' (one_le_pow₀ (le_max_left _ _)),
    fun σ n q r t₀ η hn hq hnr ht₀ hη hρ ↦ ?_⟩
  set ρ := ∑ a, ∑ b, (η a b : K) * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
    (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀))
  rw [sq] at hq
  have hq₀ : 1 ≤ q := Nat.pos_of_ne_zero fun h ↦ by subst h; simp [ρ] at hρ
  have hm : 1 ≤ m := Nat.pos_of_ne_zero fun h ↦ by subst h; nlinarith
  -- `x = c₀ ^ N ρ` is a nonzero algebraic integer, each of whose terms is `η_{ab}` times an
  -- algebraic integer of house at most `q ^ r H ^ N`.
  set N := r + 2 * q * m
  have ht (a b : Fin q) :=
    hterm r _ _ t₀ N q hq₀ a.is_lt b.is_lt (gelfond_index_le a b ht₀ le_rfl)
  have hx : (c₀ : K) ^ N * ρ = ∑ a, ∑ b, (η a b : K) * ((c₀ : K) ^ N *
      ((((a : ℕ) + 1 : ℕ) + (((b : ℕ) + 1 : ℕ) : K) * β) ^ r *
        (α ^ (((a : ℕ) + 1) * t₀) * γ ^ (((b : ℕ) + 1) * t₀)))) := by
    simp only [ρ, mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    push_cast
    ring
  have hxint : IsIntegral ℤ ((c₀ : K) ^ N * ρ) := by
    rw [hx]
    exact IsIntegral.sum _ fun a _ ↦ IsIntegral.sum _ fun b _ ↦
      (η a b).isIntegral_coe.mul (ht a b).1
  have hx0 : (c₀ : K) ^ N * ρ ≠ 0 := mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.2 hc₀)) hρ
  have hxhouse : NumberField.house ((c₀ : K) ^ N * ρ) ≤ X ^ r * (r : ℝ) ^ r := by
    refine le_trans ?_ (gelfond_value_bound_le hm hn hq hnr hH)
    rw [hx]
    refine (NumberField.house_sum_le_sum_house _ _).trans ?_
    refine (sum_le_sum fun a _ ↦ NumberField.house_sum_le_sum_house _ _).trans ?_
    refine (sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ (NumberField.house_mul_le _ _).trans
      (mul_le_mul (hη a b) (ht a b).2 (NumberField.house_nonneg _) ?_)).trans (le_of_eq ?_)
    · exact (NumberField.house_nonneg _).trans (hη a b)
    · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
  -- Liouville's inequality for `x`, and `|σ x| = |c₀| ^ N |σ ρ| ≤ H' ^ r |σ ρ|`.
  have hL := NumberField.one_le_norm_mul_house_pow hxint hx0 σ
  have hσx : ‖σ ((c₀ : K) ^ N * ρ)‖ ≤ H' ^ r * ‖σ ρ‖ := by
    rw [map_mul, norm_mul, map_pow, map_intCast, norm_pow, Complex.norm_intCast]
    gcongr
    calc |(c₀ : ℝ)| ^ N ≤ H ^ N := pow_le_pow_left₀ (abs_nonneg _) hc₀H N
      _ ≤ H' ^ r := by
        rw [← pow_mul]
        refine pow_le_pow_right₀ hH ?_
        have := gelfond_two_mul_mul_le hq hnr
        rw [add_mul, one_mul]
        omega
  have hX : X ^ r * (r : ℝ) ^ r ≤ max 1 X ^ r * (r : ℝ) ^ r :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (le_max_right _ _) r)
      (by positivity)
  calc (1 : ℝ) ≤ ‖σ ((c₀ : K) ^ N * ρ)‖ *
        NumberField.house ((c₀ : K) ^ N * ρ) ^ (finrank ℚ K - 1) := hL
    _ ≤ H' ^ r * ‖σ ρ‖ * (max 1 X ^ r * (r : ℝ) ^ r) ^ (finrank ℚ K - 1) :=
        mul_le_mul hσx (pow_le_pow_left₀ (NumberField.house_nonneg _) (hxhouse.trans hX) _)
          (pow_nonneg (NumberField.house_nonneg _) _) (by positivity)
    _ = (H' * max 1 X ^ (finrank ℚ K - 1)) ^ r * (r : ℝ) ^ ((finrank ℚ K - 1) * r) * ‖σ ρ‖ := by
        rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm r]
        ring

end TauCeti
