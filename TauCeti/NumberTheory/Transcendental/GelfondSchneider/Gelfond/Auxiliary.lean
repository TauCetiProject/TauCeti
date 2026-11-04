/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial
public import TauCeti.NumberTheory.Transcendental.GelfondSchneider.SchneiderAuxiliary

import TauCeti.Algebra.CharZero.RatCast
import TauCeti.LinearAlgebra.Vandermonde

/-!
# Gelfond's auxiliary function and its first nonvanishing derivative

Let `K` be a field of characteristic zero with an embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and let
`α, β, γ ∈ K` with `σ α = exp λ`, `σ γ = exp (σ β λ)` and `β` irrational. In Gelfond's proof of
the Gelfond–Schneider theorem the auxiliary function is the exponential sum

`R(z) = ∑_{a, b = 1}^{q} η_{ab} exp ((a + b σ β) λ z)`

with coefficients `η_{ab} ∈ K` (written `σ η_{ab}` once embedded in `ℂ`). Its derivatives at the
natural numbers lie in `σ(K)` after factoring out a power of `λ`: since `exp ((a + b σ β) λ t)` is
`σ (α ^ (a t) γ ^ (b t))`,

`R⁽ᵏ⁾(t) = λ ^ k σ (y_k(t))`, where `y_k(t) = ∑_{a, b} η_{ab} (a + b β) ^ k α ^ (a t) γ ^ (b t)`.

In the application, `K` is a number field containing the algebraic numbers `α, β, γ`, and the
coefficients `η` are algebraic integers chosen by Siegel's lemma so that `R` vanishes to a high
order `n` at the points `t = 1, …, m`. Gelfond's argument then uses the first derivative order `r`
at which `R` fails to vanish at one of these points, say at `t₀`: the number `ρ = y_r(t₀) ∈ K` is
nonzero, so in that number-field setting (after clearing the denominators of `α, β, γ`) it
satisfies Liouville's lower bound, while the vanishing of all lower derivatives gives an analytic
upper bound for `|R⁽ʳ⁾(t₀)| = |λ| ^ r |σ ρ|`.

**Construction.** For a number field `K` and `m ≥ 1`, the conditions `y_k(t) = 0` for `k < n`
and `1 ≤ t ≤ m` are `m n` linear equations in the `q ^ 2` unknowns `η_{ab}`. When `q ^ 2 = 2 m n`,
Mathlib's Siegel lemma over `𝓞 K` (`NumberField.house.exists_ne_zero_int_vec_house_le`), whose
exponent `m n / (q ^ 2 - m n)` is then `1`, solves them with algebraic integers of house at most
`c ^ n n ^ ((n + 1) / 2)`, for a constant `c` depending only on `K`, `α`, `β`, `γ` and `m`. To
apply it, each equation is multiplied by `c₀ ^ (n - 1 + 2 q m)` for a nonzero integer `c₀` such
that `c₀ α`, `c₀ β` and `c₀ γ` are algebraic integers; the entries of the resulting system have
house at most `q ^ (n - 1) H ^ (n - 1 + 2 q m)`.

**First nonvanishing derivative.** This part makes no arithmetic assumption on `K`: it proves
that such `r` and `t₀` exist, with `n ≤ r < q ^ 2`, as soon as `λ ≠ 0` and `η ≠ 0`. For each fixed
`t`, the values `y_k(t)` are the
power sums `∑ w_{ab} θ_{ab} ^ k` with weights `w_{ab} = η_{ab} α ^ (a t) γ ^ (b t)` and nodes
`θ_{ab} = a + b β`. The nodes are pairwise distinct because `β` is irrational, so the Vandermonde
matrix of the nodes is invertible and one of the first `q ^ 2` power sums is nonzero. In Lean the
indices `a, b` run over `Fin q`, and the frequencies are written `(a + 1) + (b + 1) β`.

## Main results

* `TauCeti.exists_intCast_pow_mul_gelfond_term`: a common denominator `c₀` and house bounds for
  the terms `(u + v β) ^ k α ^ (u j) γ ^ (v j)` of the values `y_k(t)`.
* `TauCeti.exists_gelfond_auxiliary_algebraic`: algebraic integers `η_{ab}`, not all zero, with
  `house η_{ab} ≤ c ^ n n ^ ((n + 1) / 2)`, such that `y_k(t) = 0` for `k < n` and `1 ≤ t ≤ m`.
* `RingHom.exists_gelfond_auxiliary`: the same coefficients make `R` vanish to order `n` at
  `1, …, m`.
* `TauCeti.exists_gelfond_value_ne_zero`: for `η ≠ 0` and a nonempty finite set `T ⊆ ℕ`, there
  are `r < q ^ 2` and `t₀ ∈ T` with `y_k(t) = 0` for all `k < r` and `t ∈ T`, and `y_r(t₀) ≠ 0`.
* `RingHom.iteratedDeriv_gelfond_auxiliary_natCast`: `R⁽ᵏ⁾(t) = λ ^ k σ (y_k(t))`.
* `RingHom.exists_iteratedDeriv_gelfond_auxiliary_ne_zero`: if `λ ≠ 0`, `η ≠ 0` and `R` vanishes
  to order `n` on `T`, then there are `r` with `n ≤ r < q ^ 2` and `t₀ ∈ T` such that `R`
  vanishes to order `r` on `T` and `R⁽ʳ⁾(t₀) ≠ 0`.

## References

* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* K. Soundararajan (notes by I. Petrow), *Transcendental number theory*, Stanford Math 249A
  course notes (2011).
-/

public section

open Finset

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K]

/-- **The first nonvanishing derivative of Gelfond's auxiliary function, algebraic form.** Let
`K` be a field of characteristic zero, let `α, γ ∈ K` be nonzero and `β ∈ K` irrational, and let
`η : Fin q → Fin q → K` be nonzero. Put
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)`. Then for every
nonempty finite set `T` of natural numbers there are `r < q ^ 2` and `t₀ ∈ T` such that
`y_k(t) = 0` for all `k < r` and `t ∈ T`, and `y_r(t₀) ≠ 0`. -/
theorem exists_gelfond_value_ne_zero {α β γ : K} (hα : α ≠ 0) (hγ : γ ≠ 0)
    (hβ : ∀ r : ℚ, (r : K) ≠ β) {q : ℕ} {η : Fin q → Fin q → K} (hη : η ≠ 0) {T : Finset ℕ}
    (hT : T.Nonempty) :
    ∃ r < q ^ 2, ∃ t₀ ∈ T,
      (∀ k < r, ∀ t ∈ T, ∑ a, ∑ b, η a b * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ k *
          (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) = 0) ∧
        ∑ a, ∑ b, η a b * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
          (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)) ≠ 0 := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℕ → K, ∀ k t, y k t = ∑ a, ∑ b, η a b *
      (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ k * (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) :=
    ⟨_, fun _ _ ↦ rfl⟩
  simp only [← hy]
  obtain ⟨t₁, ht₁⟩ := hT
  obtain ⟨a, b, hab⟩ : ∃ a b, η a b ≠ 0 := by
    by_contra! h
    exact hη (funext fun a ↦ funext (h a))
  -- At `t₁`, the values `y_k(t₁)` are power sums with distinct nodes and weights not all zero.
  obtain ⟨k, hk, hne⟩ := exists_lt_card_sum_mul_pow_ne_zero (s := univ)
    (θ := fun p : Fin q × Fin q ↦ ((p.1 + 1 : ℕ) : K) + (p.2 + 1 : ℕ) * β)
    (w := fun p ↦ η p.1 p.2 * (α ^ ((p.1 + 1 : ℕ) * t₁) * γ ^ ((p.2 + 1 : ℕ) * t₁)))
    (by
      rintro ⟨a, b⟩ - ⟨a', b'⟩ - h
      simpa [Fin.val_inj] using ratCast_add_ratCast_mul_injective hβ
        (a₁ := ((a + 1 : ℕ), (b + 1 : ℕ)))
        (a₂ := ((a' + 1 : ℕ), (b' + 1 : ℕ))) (by simpa using h))
    ⟨(a, b), mem_univ _, mul_ne_zero hab (mul_ne_zero (pow_ne_zero _ hα) (pow_ne_zero _ hγ))⟩
  have hk' : y k t₁ ≠ 0 := by
    rw [Fintype.sum_prod_type] at hne
    rw [hy]
    exact ne_of_eq_of_ne (sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring) hne
  have hex : ∃ k, ∃ t ∈ T, y k t ≠ 0 := ⟨k, t₁, ht₁, hk'⟩
  obtain ⟨t₀, ht₀, hr⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, t₀, ht₀, fun k' hk' t ht ↦ ?_, hr⟩
  · calc Nat.find hex ≤ k := Nat.find_min' hex ⟨t₁, ht₁, hk'⟩
      _ < q ^ 2 := by simpa [sq] using hk
  · by_contra h
    exact Nat.find_min hex hk' ⟨t, ht, h⟩

section NumberField

open Module NumberField

open scoped Matrix

/-- The coefficient bound of Gelfond's auxiliary function: if `q ^ 2 = 2 m n` with `m, n ≥ 1`,
then the bound `C (C q ^ 2 A)` of Siegel's lemma, for entries of house at most
`A = q ^ (n - 1) H ^ (n - 1 + 2 q m)`, is at most `c ^ n n ^ ((n + 1) / 2)` with
`c = max(1, C ^ 2) (2 m) H ^ (1 + 4 m ^ 2)`. -/
private theorem gelfond_siegel_bound_le {C H : ℝ} {m n q : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hq : q * q = 2 * m * n) (hH : 1 ≤ H) :
    C * (C * ((q * q : ℕ) : ℝ) * ((q : ℝ) ^ (n - 1) * H ^ (n - 1 + 2 * q * m))) ≤
      (max 1 (C ^ 2) * (2 * m) * H ^ (1 + 4 * m ^ 2)) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq₀ : 1 ≤ q := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hq; omega
  -- `q ^ (n + 1) = (2 m n) ^ ((n + 1) / 2) ≤ (2 m) ^ n n ^ ((n + 1) / 2)`.
  have hqpow : (q : ℝ) ^ (n + 1) ≤ (2 * m) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
    have hqq : ((q : ℝ) ^ (n + 1)) = ((2 * m : ℝ) * n) ^ (((n : ℝ) + 1) / 2) := by
      have : ((2 * m : ℝ) * n) = (q : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two, sq]
        exact_mod_cast hq.symm
      rw [this, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [hqq, Real.mul_rpow (by positivity) (by positivity)]
    gcongr
    calc (2 * m : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ (2 * m : ℝ) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (2 * m) ^ n := Real.rpow_natCast _ _
  -- `n - 1 + 2 q m ≤ (1 + 4 m ^ 2) n`, because `q ≤ q ^ 2 = 2 m n`.
  have hexp : n - 1 + 2 * q * m ≤ (1 + 4 * m ^ 2) * n := by
    have : q ≤ 2 * m * n := hq ▸ Nat.le_mul_of_pos_left q hq₀
    have : 2 * q * m ≤ 4 * m ^ 2 * n := by nlinarith
    rw [add_mul, one_mul]
    omega
  have hC : C * C ≤ max 1 (C ^ 2) ^ n := by
    rw [← sq]
    exact (le_max_right _ _).trans (le_self_pow₀ (le_max_left _ _) (by omega))
  calc C * (C * ((q * q : ℕ) : ℝ) * ((q : ℝ) ^ (n - 1) * H ^ (n - 1 + 2 * q * m)))
      = C * C * ((q : ℝ) ^ (n + 1) * H ^ (n - 1 + 2 * q * m)) := by
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
        push_cast
        ring
    _ ≤ max 1 (C ^ 2) ^ n * ((2 * m) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) *
          (H ^ (1 + 4 * m ^ 2)) ^ n) := by
        rw [← pow_mul]
        gcongr
    _ = (max 1 (C ^ 2) * (2 * m) * H ^ (1 + 4 * m ^ 2)) ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
        rw [mul_pow, mul_pow]
        ring

variable {K : Type*} [Field K] [NumberField K]

/-- A common denominator for the terms of Gelfond's values: there are a nonzero integer `c₀` and
`H ≥ 1` with `|c₀| ≤ H` such that for `u, v ≤ B` (`B ≥ 1`) and `k + u j + v j ≤ N` the multiple
`c₀ ^ N ((u + v β) ^ k α ^ (u j) γ ^ (v j))` is an algebraic integer of house at most
`B ^ k H ^ N`. -/
theorem exists_intCast_pow_mul_gelfond_term (α β γ : K) :
    ∃ c₀ : ℤ, c₀ ≠ 0 ∧ ∃ H : ℝ, 1 ≤ H ∧ |(c₀ : ℝ)| ≤ H ∧
      ∀ k u v j N B : ℕ, 1 ≤ B → u ≤ B → v ≤ B → k + u * j + v * j ≤ N →
        IsIntegral ℤ ((c₀ : K) ^ N * (((u : K) + v * β) ^ k * (α ^ (u * j) * γ ^ (v * j)))) ∧
        house ((c₀ : K) ^ N * (((u : K) + v * β) ^ k * (α ^ (u * j) * γ ^ (v * j)))) ≤
          (B : ℝ) ^ k * H ^ N := by
  classical
  -- A nonzero integer `c₀` such that `c₀ α`, `c₀ β` and `c₀ γ` are algebraic integers.
  obtain ⟨c₀, hc₀, hc₀S⟩ := exists_integral_multiples ℤ ℚ ({α, β, γ} : Finset K)
  have hint (x) (hx : x ∈ ({α, β, γ} : Finset K)) : IsIntegral ℤ ((c₀ : K) * x) := by
    simpa only [zsmul_eq_mul] using hc₀S x hx
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ,
      H = |(c₀ : ℝ)| + house ((c₀ : K) * α) + house ((c₀ : K) * β) + house ((c₀ : K) * γ) :=
    ⟨_, rfl⟩
  have h₀ := abs_nonneg (c₀ : ℝ)
  have h₁ := house_nonneg ((c₀ : K) * α)
  have h₂ := house_nonneg ((c₀ : K) * β)
  have h₃ := house_nonneg ((c₀ : K) * γ)
  have hc₀H : |(c₀ : ℝ)| ≤ H := by linarith
  have hH : 1 ≤ H := le_trans (by exact_mod_cast Int.one_le_abs hc₀) hc₀H
  refine ⟨c₀, hc₀, H, hH, hc₀H, fun k u v j N B hB hu hv hN ↦ ⟨?_, ?_⟩⟩
  · exact isIntegral_intCast_pow_mul_schneider_term (hint α (by simp)) (hint β (by simp))
      (hint γ (by simp)) hN
  -- `c₀ (u + v β) = u c₀ + v (c₀ β)` has house at most `B H`.
  have hwH : house ((c₀ : K) * ((u : K) + v * β)) ≤ B * H := by
    have hu' : (u : ℝ) ≤ B := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ B := by exact_mod_cast hv
    have hcw : (c₀ : K) * ((u : K) + v * β) = ((u * c₀ : ℤ) : K) + (v : K) * ((c₀ : K) * β) := by
      push_cast
      ring
    rw [hcw]
    refine (house_add_le _ _).trans ?_
    rw [house_intCast, house_nat_mul]
    push_cast
    rw [abs_mul, Nat.abs_cast]
    have hβH : |(c₀ : ℝ)| + house ((c₀ : K) * β) ≤ H := by linarith
    nlinarith
  have hc₀H' : house (c₀ : K) ≤ H := by rwa [house_intCast, Int.cast_abs]
  have hαH : house ((c₀ : K) * α) ≤ H := by linarith
  have hγH : house ((c₀ : K) * γ) ≤ H := by linarith
  have h := house_schneider_entry_le (s := u * j) (t := v * j) (n := N) hc₀H' hwH hαH hγH
    (by exact_mod_cast hB) (by linarith) (le_refl k) hN
  refine le_of_eq_of_le ?_ h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left]
  congr 1
  simp only [mul_pow]
  ring

/-- **Gelfond's auxiliary function, algebraic form** (Karatarakis–Wiedijk, §3). Let `K` be a
number field, `α, β, γ ∈ K` and `m ≥ 1`. There is `c ≥ 1` such that for all positive integers `n`
and `q` with `q ^ 2 = 2 m n` there are algebraic integers `η_{ab} ∈ 𝓞 K`, `a, b < q`, not all
zero, with `house η_{ab} ≤ c ^ n n ^ ((n + 1) / 2)`, such that
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)` vanishes for
all `k < n` and `1 ≤ t ≤ m`. -/
theorem exists_gelfond_auxiliary_algebraic (α β γ : K) {m : ℕ} (hm : 1 ≤ m) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ n q : ℕ, 1 ≤ n → q ^ 2 = 2 * m * n →
      ∃ η : Fin q → Fin q → 𝓞 K, η ≠ 0 ∧
        (∀ a b, house (η a b : K) ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) ∧
        ∀ k < n, ∀ t ∈ Icc 1 m,
          ∑ a, ∑ b, (η a b : K) * (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ k *
            (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) = 0 := by
  classical
  obtain ⟨c₀, hc₀, H, hH, -, hterm⟩ := exists_intCast_pow_mul_gelfond_term α β γ
  -- Siegel's lemma over `𝓞 K` (Mathlib). Its constant depends only on `K` but is not exported by
  -- name, so it is quantified here before `n` and `q` are chosen.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (n q : ℕ) (e : Matrix (Fin n × Fin m) (Fin q × Fin q) (𝓞 K))
      (A : ℝ), e ≠ 0 → 0 < n * m → n * m < q * q →
      (∀ i j, house (algebraMap (𝓞 K) K (e i j)) ≤ A) →
      ∃ ξ : Fin q × Fin q → 𝓞 K, ξ ≠ 0 ∧ e *ᵥ ξ = 0 ∧
        ∀ j, house (ξ j : K) ≤ C * (C * (q * q : ℕ) * A) ^ ((n * m : ℕ) / ((q * q : ℕ) -
          (n * m : ℕ)) : ℝ) :=
    ⟨_, fun n q e A he h0 hlt hA ↦ house.exists_ne_zero_int_vec_house_le K e he h0 hlt
      (by simp) hA (by simp)⟩
  set c := max 1 (C ^ 2) * (2 * m) * H ^ (1 + 4 * m ^ 2)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : 1 ≤ c := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)) (one_le_pow₀ hH)
  refine ⟨c, hc, fun n q hn hq ↦ ?_⟩
  rw [sq] at hq
  have hq₀ : 1 ≤ q := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hq; omega
  -- The equation `(k, t + 1)`, multiplied by `c₀ ^ N`, has coefficient `e p u` at the unknown
  -- `η_u`, an algebraic integer of house at most `q ^ (n - 1) H ^ N`.
  set N := n - 1 + 2 * q * m
  let e : Fin n × Fin m → Fin q × Fin q → K := fun p u ↦
    (c₀ : K) ^ N * ((((u.1 : ℕ) + 1 : ℕ) + (((u.2 : ℕ) + 1 : ℕ) : K) * β) ^ (p.1 : ℕ) *
      (α ^ (((u.1 : ℕ) + 1) * ((p.2 : ℕ) + 1)) * γ ^ (((u.2 : ℕ) + 1) * ((p.2 : ℕ) + 1))))
  have hs (p : Fin n × Fin m) (u : Fin q × Fin q) :
      (p.1 : ℕ) + ((u.1 : ℕ) + 1) * ((p.2 : ℕ) + 1) + ((u.2 : ℕ) + 1) * ((p.2 : ℕ) + 1) ≤ N := by
    have h₁ : ((u.1 : ℕ) + 1) * ((p.2 : ℕ) + 1) ≤ q * m := Nat.mul_le_mul u.1.is_lt p.2.is_lt
    have h₂ : ((u.2 : ℕ) + 1) * ((p.2 : ℕ) + 1) ≤ q * m := Nat.mul_le_mul u.2.is_lt p.2.is_lt
    have := p.1.is_lt
    simp only [N]
    rw [mul_assoc, two_mul]
    omega
  have he (p u) := hterm p.1 _ _ _ N q hq₀ u.1.is_lt u.2.is_lt (hs p u)
  have heA (p u) : house (e p u) ≤ (q : ℝ) ^ (n - 1) * H ^ N :=
    (he p u).2.trans (by gcongr; exacts [by exact_mod_cast hq₀, by have := p.1.is_lt; omega])
  let e' : Matrix (Fin n × Fin m) (Fin q × Fin q) (𝓞 K) := fun p u ↦ ⟨e p u, (he p u).1⟩
  -- A nonzero solution `ξ` of the system with the required house bound. If the system is
  -- trivial, the constant vector `1` will do.
  obtain ⟨ξ, hξ0, hξ, hξle⟩ : ∃ ξ : Fin q × Fin q → 𝓞 K, ξ ≠ 0 ∧ e' *ᵥ ξ = 0 ∧
      ∀ u, house (ξ u : K) ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) := by
    by_cases he' : e' = 0
    · refine ⟨fun _ ↦ 1, fun h ↦ ?_, by rw [he', Matrix.zero_mulVec], fun _ ↦ ?_⟩
      · exact one_ne_zero (congr_fun h (⟨0, hq₀⟩, ⟨0, hq₀⟩))
      · have hone : house ((1 : 𝓞 K) : K) = 1 := by simpa using house_intCast (K := K) 1
        rw [hone]
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hc)
          (Real.one_le_rpow hn' (by positivity))
    obtain ⟨ξ, hξ0, hξ, hξle⟩ := hC n q e' ((q : ℝ) ^ (n - 1) * H ^ N) he'
      (Nat.mul_pos hn hm) (by nlinarith) heA
    refine ⟨ξ, hξ0, hξ, fun u ↦ (hξle u).trans ?_⟩
    -- Siegel's exponent is `n m / (q ^ 2 - n m) = 1`, since `q ^ 2 = 2 n m`.
    have hexp : (((n * m : ℕ) : ℝ) / ((q * q : ℕ) - (n * m : ℕ)) : ℝ) = 1 := by
      have : ((q * q : ℕ) : ℝ) = 2 * ((n * m : ℕ) : ℝ) := by
        rw [hq]
        push_cast
        ring
      rw [this, two_mul, add_sub_cancel_right, div_self (by positivity)]
    rw [hexp, Real.rpow_one]
    exact gelfond_siegel_bound_le hm hn hq hH
  refine ⟨fun a b ↦ ξ (a, b), fun h ↦ hξ0 (funext fun u ↦ congr_fun₂ h u.1 u.2),
    fun a b ↦ hξle (a, b), fun k hk t ht ↦ ?_⟩
  -- The equation of `(k, t)`, divided by `c₀ ^ N`.
  obtain ⟨ht₁, htm⟩ := mem_Icc.mp ht
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' ht₁
  set p : Fin n × Fin m := (⟨k, hk⟩, ⟨t, by omega⟩)
  have hrow (a : Matrix (Fin n × Fin m) (Fin q × Fin q) (𝓞 K)) (ha : a *ᵥ ξ = 0) :
      ∑ u, (a p u : K) * (ξ u : K) = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrArg (algebraMap (𝓞 K) K) (congrFun ha p)
  -- The coercion of the algebraic integer `e' p u = ⟨e p u, _⟩` to `K` is `e p u`
  -- (`RingOfIntegers.coe_mk`, which `simp` does not apply through the subtype structure).
  replace hrow : ∑ u, e p u * (ξ u : K) = 0 := hrow e' hξ
  simp only [e, Fintype.sum_prod_type] at hrow
  have hc₀N : (c₀ : K) ^ N ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.2 hc₀)
  refine (mul_eq_zero.mp ?_).resolve_left hc₀N
  rw [← hrow, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [p]
  push_cast
  ring


end NumberField

end TauCeti

namespace RingHom

/-- If `σ α = exp λ` and `σ γ = exp (σ β λ)`, then the `k`-th derivative of Gelfond's auxiliary
function `R(z) = ∑_{a, b} σ η_{ab} exp (((a + 1) + (b + 1) σ β) λ z)` at a natural number `t` is
`λ ^ k` times the image under `σ` of
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)`. -/
theorem iteratedDeriv_gelfond_auxiliary_natCast {R : Type*} [Ring R] (σ : R →+* ℂ) {l : ℂ}
    {α β γ : R} (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l)) {q : ℕ}
    (η : Fin q → Fin q → R) (k t : ℕ) :
    iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t =
      l ^ k * σ (∑ a, ∑ b, η a b * (((a + 1 : ℕ) : R) + (b + 1 : ℕ) * β) ^ k *
        (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t))) := by
  have hR : (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) =
      fun z ↦ ∑ p : Fin q × Fin q, σ (η p.1 p.2) *
        Complex.exp ((((p.1 + 1 : ℕ) : ℂ) + (p.2 + 1 : ℕ) * σ β) * l * z) := by
    funext z
    rw [Fintype.sum_prod_type]
  rw [hR, Finset.iteratedDeriv_sum_mul_cexp]
  dsimp only
  rw [Fintype.sum_prod_type, map_sum, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun b _ ↦ ?_
  rw [map_mul, σ.map_pow_mul_pow_eq_exp hα hγ]
  simp only [map_mul, map_pow, map_add, map_natCast, mul_pow]
  rw [mul_comm ((t : ℂ) * l), mul_comm (t : ℂ) l, ← mul_assoc _ l]
  ring

/-- **The first nonvanishing derivative of Gelfond's auxiliary function.** Let `K` be a field with
an embedding `σ : K →+* ℂ`, let `λ ≠ 0`, and let `α, β, γ ∈ K` with `β` irrational,
`σ α = exp λ` and `σ γ = exp (σ β λ)`. Let `η : Fin q → Fin q → K` be nonzero, and suppose that
`R(z) = ∑_{a, b} σ η_{ab} exp (((a + 1) + (b + 1) σ β) λ z)` vanishes to order `n` at every point
of a nonempty finite set `T` of natural numbers. Then there are `r` with `n ≤ r < q ^ 2` and
`t₀ ∈ T` such that `R` vanishes to order `r` at every point of `T` and `R⁽ʳ⁾(t₀) ≠ 0`. -/
theorem exists_iteratedDeriv_gelfond_auxiliary_ne_zero {K : Type*} [Field K] (σ : K →+* ℂ)
    {l : ℂ} (hl : l ≠ 0) {α β γ : K} (hα : σ α = Complex.exp l)
    (hγ : σ γ = Complex.exp (σ β * l)) (hβ : ∀ r : ℚ, (r : K) ≠ β) {q : ℕ}
    {η : Fin q → Fin q → K} (hη : η ≠ 0) {T : Finset ℕ} (hT : T.Nonempty) {n : ℕ}
    (hn : ∀ k < n, ∀ t ∈ T, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t = 0) :
    ∃ r, n ≤ r ∧ r < q ^ 2 ∧ ∃ t₀ ∈ T,
      (∀ k < r, ∀ t ∈ T, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t = 0) ∧
      iteratedDeriv r (fun z ↦ ∑ a, ∑ b, σ (η a b) *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t₀ ≠ 0 := by
  have := σ.charZero
  have hα₀ : α ≠ 0 := fun h ↦ Complex.exp_ne_zero l (by rw [← hα, h, map_zero])
  have hγ₀ : γ ≠ 0 := fun h ↦ Complex.exp_ne_zero (σ β * l) (by rw [← hγ, h, map_zero])
  obtain ⟨r, hrq, t₀, ht₀, hzero, hr⟩ := TauCeti.exists_gelfond_value_ne_zero hα₀ hγ₀ hβ hη hT
  have hr' : iteratedDeriv r (fun z ↦ ∑ a, ∑ b, σ (η a b) *
      Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t₀ ≠ 0 := by
    rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ]
    exact mul_ne_zero (pow_ne_zero _ hl) ((map_ne_zero σ).2 hr)
  refine ⟨r, ?_, hrq, t₀, ht₀, fun k hk t ht ↦ ?_, hr'⟩
  · by_contra! h
    exact hr' (hn r h t₀ ht₀)
  · rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ, hzero k hk t ht, map_zero, mul_zero]

open NumberField in
/-- **Gelfond's auxiliary function** (Karatarakis–Wiedijk, §3). Let `K` be a number field with an
embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and `α, β, γ ∈ K` with `σ α = exp λ` and
`σ γ = exp (σ β λ)`, and let `m ≥ 1`. There is `c ≥ 1` such that for all positive integers `n` and
`q` with `q ^ 2 = 2 m n` there are algebraic integers `η_{ab} ∈ 𝓞 K`, `a, b < q`, not all zero,
with `house η_{ab} ≤ c ^ n n ^ ((n + 1) / 2)`, such that
`R(z) = ∑_{a, b} σ η_{ab} exp (((a + 1) + (b + 1) σ β) λ z)` vanishes to order `n` at each of the
points `1, …, m`. -/
theorem exists_gelfond_auxiliary {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) {l : ℂ}
    {α β γ : K} (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l)) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ n q : ℕ, 1 ≤ n → q ^ 2 = 2 * m * n →
      ∃ η : Fin q → Fin q → 𝓞 K, η ≠ 0 ∧
        (∀ a b, house (η a b : K) ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) ∧
        ∀ k < n, ∀ t ∈ Icc 1 m, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, σ (η a b) *
          Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * σ β) * l * z)) t = 0 := by
  obtain ⟨c, hc, h⟩ := TauCeti.exists_gelfond_auxiliary_algebraic α β γ hm
  refine ⟨c, hc, fun n q hn hq ↦ ?_⟩
  obtain ⟨η, hη, hbound, hzero⟩ := h n q hn hq
  refine ⟨η, hη, hbound, fun k hk t ht ↦ ?_⟩
  rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ (fun a b ↦ (η a b : K)), hzero k hk t ht,
    map_zero, mul_zero]

end RingHom
