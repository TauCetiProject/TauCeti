/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.NumberField.SiegelsLemma

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Schneider's auxiliary function

Let `K ⊂ ℂ` be a number field of degree `d`, given by an embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and
let `α, β, γ ∈ K` with `σ α = exp λ` and `σ γ = exp (σ β λ)`. In Schneider's proof of the
Gelfond–Schneider theorem the auxiliary function is the exponential polynomial

`F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j λ z)`,

whose integer coefficients are chosen so that `F` vanishes at the points `u + v σ β` of the grid
`1 ≤ u, v ≤ L`. Since `exp (j λ (u + v σ β)) = σ (α ^ (u j) γ ^ (v j))`
(`RingHom.map_pow_mul_pow_eq_exp`), the value `F(u + v σ β)` is the image under `σ` of

`y_{uv} = ∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j) ∈ K`,

so the vanishing conditions are `L²` linear equations over `K` in the `D₁ D₂` integer unknowns
`a_{ij}`. When `D₁ D₂ ≥ 2 d L²`, Siegel's lemma with rational integer unknowns
(`NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`) solves them with
`|a_{ij}| ≤ exp (c (D₁ log L + D₂ L))`, where `c` depends only on `K`, `α`, `β` and `γ`. To apply
it, each equation is multiplied by `m ^ (D₁ + 2 L D₂)` for a nonzero integer `m` such that
`m α`, `m β` and `m γ` are algebraic integers.

Schneider's proof then evaluates `F` on the larger grid `u, v ≤ c L`. The values `y_{uv}` there
have house `exp (O (D₁ log L + D₂ L))`, which is `exp (O (L ^ (3 / 2) log L))` for Schneider's
parameters `L = 2 d M²`, `D₁ = (2 d)² M³`, `D₂ = 2 d M`, and `m ^ (D₁ + 2 c L D₂) y_{uv}` is an
algebraic integer, where `m ^ (D₁ + 2 c L D₂) ≤ exp (O (L ^ (3 / 2)))`. These are the arithmetic
inputs to Liouville's lower bound for a nonzero `σ y_{uv}`. The analytic upper bound for
`|F(u + v σ β)|`, from the zero estimate for exponential polynomials and Schwarz's lemma with
prescribed zeros, is not part of this file.

## Main results

* `TauCeti.exists_schneider_auxiliary_algebraic`: a nonzero integer coefficient matrix with the
  bound above for which every `y_{uv}`, `1 ≤ u, v ≤ L`, vanishes in `K`.
* `RingHom.map_pow_mul_pow_eq_exp`: `σ (α ^ (u j) γ ^ (v j)) = exp (j λ (u + v σ β))`.
* `RingHom.exists_schneider_auxiliary`: the auxiliary function `F` vanishes at the grid points
  `u + v σ β`, `1 ≤ u, v ≤ L`.
* `TauCeti.house_schneider_value_le`: an explicit bound for the house of `y_{uv}`, `u, v ≤ B`.
* `TauCeti.isIntegral_intCast_pow_mul_schneider_value`: `m ^ (D₁ + 2 B D₂) y_{uv}` is an algebraic
  integer for `u, v ≤ B` when `m α`, `m β` and `m γ` are.
* `TauCeti.exists_house_schneider_value_le_exp`: on the grid `u, v ≤ c L`, the house of `y_{uv}`
  is at most `exp (C (D₁ log L + D₂ L))`.
* `TauCeti.exists_house_schneider_value_le_exp_rpow`,
  `TauCeti.exists_abs_pow_schneider_exponent_le_exp_rpow`: for Schneider's parameters, the house of
  `y_{uv}` is at most `exp (c₅ L ^ (3 / 2) log L)` and the denominator `m ^ (D₁ + 2 c L D₂)` is at
  most `exp (c₆ L ^ (3 / 2))`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Lemmas 4.22
  and 4.27.
-/

public section

open Finset Module NumberField

namespace TauCeti

/-- The coefficient bound of Schneider's auxiliary function: with `N = D₁ D₂` unknowns and
entries of house at most `L ^ D₁ H ^ (D₁ + 2 L D₂)`, the quantity `3 N A` of Siegel's lemma is at
most `exp ((4 + 2 log H) (D₁ log L + D₂ L))`. -/
private theorem schneider_siegel_bound_le {L D₁ D₂ : ℕ} {H : ℝ} (hL : 3 ≤ L) (hD₁ : 1 ≤ D₁)
    (hD₂ : 1 ≤ D₂) (hH : 1 ≤ H) :
    3 * ((D₁ * D₂ : ℕ) : ℝ) * ((L : ℝ) ^ D₁ * H ^ (D₁ + 2 * L * D₂)) ≤
      Real.exp ((4 + 2 * Real.log H) * (D₁ * Real.log L + D₂ * L)) := by
  have hL₁ : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hD₁' : (1 : ℝ) ≤ D₁ := by exact_mod_cast hD₁
  have hD₂' : (1 : ℝ) ≤ D₂ := by exact_mod_cast hD₂
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_three]
  have hlogH := Real.log_nonneg hH
  have hlog₃ : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlog₁ : Real.log D₁ ≤ D₁ := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < D₁)]
  have hlog₂ : Real.log D₂ ≤ D₂ := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < D₂)]
  have hpos : 0 < 3 * ((D₁ * D₂ : ℕ) : ℝ) * ((L : ℝ) ^ D₁ * H ^ (D₁ + 2 * L * D₂)) := by
    have : (0 : ℝ) < D₁ * D₂ := by positivity
    have : (0 : ℝ) < H := by linarith
    push_cast
    positivity
  rw [← Real.exp_log hpos, Real.exp_le_exp]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by positivity) (by positivity), Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  have h₁ : (D₁ : ℝ) ≤ D₁ * Real.log L := le_mul_of_one_le_right (by linarith) hlogL
  have h₂ : (D₂ : ℝ) ≤ D₂ * L := le_mul_of_one_le_right (by linarith) (by linarith)
  have h₃ : (D₁ : ℝ) * Real.log H ≤ D₁ * Real.log L * Real.log H :=
    mul_le_mul_of_nonneg_right h₁ hlogH
  nlinarith

/-- Siegel's exponent `n / (N - n)` is at most `1` when `2 n ≤ N`, so for a base `B ≥ 1` the
bound `B ^ (n / (N - n))` of Siegel's lemma is at most `B`. -/
private theorem rpow_div_sub_le_self {B n N : ℝ} (hB : 1 ≤ B) (hn : 0 ≤ n) (h : 2 * n ≤ N) :
    B ^ (n / (N - n)) ≤ B :=
  (Real.rpow_le_rpow_of_exponent_le hB (div_le_one_of_le₀ (by linarith) (by linarith))).trans_eq
    (Real.rpow_one B)

/-- For `i < D₁`, `j < D₂` and `u, v ≤ B`, the total degree `i + u j + v j` of a term of
Schneider's value `y_{uv}` in `u + v β`, `α` and `γ` is at most `D₁ + 2 B D₂`. -/
private theorem schneider_exponent_le {D₁ D₂ B : ℕ} (i : Fin D₁) (j : Fin D₂) {u v : ℕ}
    (hu : u ≤ B) (hv : v ≤ B) : (i : ℕ) + u * j + v * j ≤ D₁ + 2 * B * D₂ := by
  have h₁ : u * (j : ℕ) ≤ B * D₂ := Nat.mul_le_mul hu j.is_lt.le
  have h₂ : v * (j : ℕ) ≤ B * D₂ := Nat.mul_le_mul hv j.is_lt.le
  have := i.is_lt
  linarith

section CommRing

variable {K : Type*} [CommRing K]

/-- One term of Schneider's value `y_{uv}`, multiplied by `m ^ N` with `i + u j + v j ≤ N`, is an
algebraic integer when `m α`, `m β` and `m γ` are. -/
private theorem isIntegral_intCast_pow_mul_schneider_term {m : ℤ} {α β γ : K}
    (hα : IsIntegral ℤ ((m : K) * α)) (hβ : IsIntegral ℤ ((m : K) * β))
    (hγ : IsIntegral ℤ ((m : K) * γ)) {i j u v N : ℕ} (h : i + u * j + v * j ≤ N) :
    IsIntegral ℤ ((m : K) ^ N * (((u : K) + v * β) ^ i * (α ^ (u * j) * γ ^ (v * j)))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  have hw : IsIntegral ℤ ((m : K) * ((u : K) + v * β)) := by
    rw [mul_add, mul_left_comm]
    exact ((isIntegral_intCast m).mul (isIntegral_natCast u)).add
      ((isIntegral_natCast v).mul hβ)
  have key : (m : K) ^ (i + u * j + v * j + r) *
      (((u : K) + v * β) ^ i * (α ^ (u * j) * γ ^ (v * j))) =
      (m : K) ^ r * ((m : K) * ((u : K) + v * β)) ^ i *
        (((m : K) * α) ^ (u * j) * ((m : K) * γ) ^ (v * j)) := by
    rw [mul_pow, mul_pow, mul_pow]
    ring
  rw [key]
  exact (((isIntegral_intCast m).pow r).mul (hw.pow i)).mul ((hα.pow _).mul (hγ.pow _))

/-- **Denominators of Schneider's values.** If `m α`, `m β` and `m γ` are algebraic integers,
then for `u, v ≤ B` the multiple
`m ^ (D₁ + 2 B D₂) ∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j)` is an algebraic integer for
all integers `a_{ij}`, `i < D₁`, `j < D₂`. -/
theorem isIntegral_intCast_pow_mul_schneider_value {m : ℤ} {α β γ : K}
    (hα : IsIntegral ℤ ((m : K) * α)) (hβ : IsIntegral ℤ ((m : K) * β))
    (hγ : IsIntegral ℤ ((m : K) * γ)) {D₁ D₂ B : ℕ} (a : Fin D₁ → Fin D₂ → ℤ) {u v : ℕ}
    (hu : u ≤ B) (hv : v ≤ B) :
    IsIntegral ℤ ((m : K) ^ (D₁ + 2 * B * D₂) *
      ∑ i, ∑ j, (a i j : K) * ((u : K) + v * β) ^ (i : ℕ) * (α ^ (u * j) * γ ^ (v * j))) := by
  rw [mul_sum]
  refine IsIntegral.sum _ fun i _ ↦ ?_
  rw [mul_sum]
  refine IsIntegral.sum _ fun j _ ↦ ?_
  have hk := schneider_exponent_le i j hu hv
  rw [show (m : K) ^ (D₁ + 2 * B * D₂) * ((a i j : K) * ((u : K) + v * β) ^ (i : ℕ) *
      (α ^ (u * j) * γ ^ (v * j))) = (a i j : K) * ((m : K) ^ (D₁ + 2 * B * D₂) *
      (((u : K) + v * β) ^ (i : ℕ) * (α ^ (u * j) * γ ^ (v * j)))) by ring]
  exact (isIntegral_intCast _).mul (isIntegral_intCast_pow_mul_schneider_term hα hβ hγ hk)

end CommRing

variable {K : Type*} [Field K] [NumberField K]

/-- Bounds on the houses of two factors bound the house of their product. -/
private theorem house_mul_le_of_le {x y : K} {X Y : ℝ} (hx : house x ≤ X) (hy : house y ≤ Y) :
    house (x * y) ≤ X * Y :=
  (house_mul_le x y).trans (mul_le_mul hx hy (house_nonneg y) ((house_nonneg x).trans hx))

/-- A bound on the house of `x` bounds the house of its powers. -/
private theorem house_pow_le_of_le {x : K} {X : ℝ} (hx : house x ≤ X) (n : ℕ) :
    house (x ^ n) ≤ X ^ n := by
  rw [house_pow]
  exact pow_le_pow_left₀ (house_nonneg x) hx n

/-- The house bound for an entry of Schneider's linear system: if `x`, `z`, `w` have house at
most `H` and `y` has house at most `L H`, then for `i ≤ D` and `i + s + t ≤ n` the entry
`x ^ (n - (i + s + t)) y ^ i z ^ s w ^ t` has house at most `L ^ D H ^ n`. -/
private theorem house_schneider_entry_le {x y z w : K} {L H : ℝ} (hx : house x ≤ H)
    (hy : house y ≤ L * H) (hz : house z ≤ H) (hw : house w ≤ H) (hL : 1 ≤ L) (hH : 0 ≤ H)
    {i s t n D : ℕ} (hi : i ≤ D) (hn : i + s + t ≤ n) :
    house (x ^ (n - (i + s + t)) * y ^ i * (z ^ s * w ^ t)) ≤ L ^ D * H ^ n := by
  have h := house_mul_le_of_le (house_mul_le_of_le (house_pow_le_of_le hx (n - (i + s + t)))
      (house_pow_le_of_le hy i)) (house_mul_le_of_le (house_pow_le_of_le hz s)
      (house_pow_le_of_le hw t))
  refine h.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ hL hi) (by positivity)))
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, mul_pow]
  ring

/-- **Schneider's auxiliary function, algebraic form** (Evertse, Lemma 4.22). Let `K` be a number
field of degree `d` and `α, β, γ ∈ K`. There is `c > 0` such that for all integers `L ≥ 3` and
`D₁, D₂` with `D₁ D₂ ≥ 2 d L²` there are integers `a_{ij}`, `i < D₁`, `j < D₂`, not all zero,
with `|a_{ij}| ≤ exp (c (D₁ log L + D₂ L))`, such that
`∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j) = 0` for all `1 ≤ u, v ≤ L`. -/
theorem exists_schneider_auxiliary_algebraic (α β γ : K) :
    ∃ c : ℝ, 0 < c ∧ ∀ L D₁ D₂ : ℕ, 3 ≤ L → 2 * finrank ℚ K * L ^ 2 ≤ D₁ * D₂ →
      ∃ a : Fin D₁ → Fin D₂ → ℤ, a ≠ 0 ∧
        (∀ i j, |(a i j : ℝ)| ≤ Real.exp (c * (D₁ * Real.log L + D₂ * L))) ∧
        ∀ u v : ℕ, 1 ≤ u → u ≤ L → 1 ≤ v → v ≤ L →
          ∑ i, ∑ j, (a i j : K) * ((u : K) + v * β) ^ (i : ℕ) *
            (α ^ (u * j) * γ ^ (v * j)) = 0 := by
  classical
  -- A nonzero integer `m` such that `m α`, `m β` and `m γ` are algebraic integers.
  obtain ⟨m, hm, hmS⟩ := exists_integral_multiples ℤ ℚ ({α, β, γ} : Finset K)
  have hint (x) (hx : x ∈ ({α, β, γ} : Finset K)) : IsIntegral ℤ ((m : K) * x) := by
    simpa only [zsmul_eq_mul] using hmS x hx
  have hmα := hint α (by simp)
  have hmβ := hint β (by simp)
  have hmγ := hint γ (by simp)
  set H : ℝ := |(m : ℝ)| + house ((m : K) * α) + house ((m : K) * β) + house ((m : K) * γ)
  have hmH : |(m : ℝ)| ≤ H := by
    linarith [house_nonneg ((m : K) * α), house_nonneg ((m : K) * β),
      house_nonneg ((m : K) * γ)]
  have hαH : house ((m : K) * α) ≤ H := by
    linarith [abs_nonneg (m : ℝ), house_nonneg ((m : K) * β), house_nonneg ((m : K) * γ)]
  have hβH : |(m : ℝ)| + house ((m : K) * β) ≤ H := by
    linarith [house_nonneg ((m : K) * α), house_nonneg ((m : K) * γ)]
  have hγH : house ((m : K) * γ) ≤ H := by
    linarith [abs_nonneg (m : ℝ), house_nonneg ((m : K) * α), house_nonneg ((m : K) * β)]
  have hH : 1 ≤ H := le_trans (by exact_mod_cast Int.one_le_abs hm) hmH
  have hH₀ : 0 ≤ H := by linarith
  refine ⟨4 + 2 * Real.log H, by linarith [Real.log_nonneg hH], fun L D₁ D₂ hL hD ↦ ?_⟩
  have hd : 0 < finrank ℚ K := finrank_pos
  have hD₁D₂ : 0 < D₁ * D₂ := lt_of_lt_of_le (by positivity) hD
  have hD₁ : 1 ≤ D₁ := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hD₁D₂
  have hD₂ : 1 ≤ D₂ := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hD₁D₂
  -- The equation of the grid point `(u, v) = (p.1 + 1, p.2 + 1)`, multiplied by `m ^ N`, has
  -- coefficient `e p q` at the unknown `a_q`; each factor is an algebraic integer.
  set N := D₁ + 2 * L * D₂
  let k : Fin L × Fin L → Fin D₁ × Fin D₂ → ℕ := fun p q ↦
    q.1 + (p.1 + 1) * q.2 + (p.2 + 1) * q.2
  have hk (p : Fin L × Fin L) (q : Fin D₁ × Fin D₂) : k p q ≤ N :=
    schneider_exponent_le q.1 q.2 p.1.is_lt p.2.is_lt
  -- Name the exponent `r = N - k p q` of the power of `m`, so that `N = k p q + r` can be
  -- substituted and `ring` can combine the powers of `m`.
  have hNk (p q) : ∃ r, N - k p q = r ∧ N = k p q + r := ⟨N - k p q, rfl, by have := hk p q; omega⟩
  let w : Fin L × Fin L → K := fun p ↦ (((p.1 : ℕ) + 1 : ℕ) : K) + (((p.2 : ℕ) + 1 : ℕ) : K) * β
  let e : Fin L × Fin L → Fin D₁ × Fin D₂ → K := fun p q ↦
    (m : K) ^ (N - k p q) * ((m : K) * w p) ^ (q.1 : ℕ) *
      (((m : K) * α) ^ (((p.1 : ℕ) + 1) * q.2) * ((m : K) * γ) ^ (((p.2 : ℕ) + 1) * q.2))
  -- `m w_p = (p.1 + 1) m + (p.2 + 1) (m β)`.
  have hmw_eq (p : Fin L × Fin L) : (m : K) * w p =
      ((((p.1 : ℕ) + 1 : ℕ) * m : ℤ) : K) + (((p.2 : ℕ) + 1 : ℕ) : K) * ((m : K) * β) := by
    simp only [w]
    push_cast
    ring
  have hep (p q) : e p q = (m : K) ^ N * (w p ^ (q.1 : ℕ) *
      (α ^ (((p.1 : ℕ) + 1) * q.2) * γ ^ (((p.2 : ℕ) + 1) * q.2))) := by
    obtain ⟨r, hNr, hr⟩ := hNk p q
    simp only [e]
    rw [hNr, hr]
    simp only [k, mul_pow]
    ring
  have he (p q) : IsIntegral ℤ (e p q) := by
    rw [hep]
    exact isIntegral_intCast_pow_mul_schneider_term hmα hmβ hmγ (hk p q)
  have hwH (p : Fin L × Fin L) : house ((m : K) * w p) ≤ L * H := by
    have hu : ((p.1 : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast p.1.is_lt
    have hv : ((p.2 : ℕ) + 1 : ℝ) ≤ L := by exact_mod_cast p.2.is_lt
    rw [hmw_eq]
    refine (house_add_le _ _).trans ?_
    rw [house_intCast, house_nat_mul]
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 : ℕ) + 1)]
    have := house_nonneg ((m : K) * β)
    have := abs_nonneg (m : ℝ)
    nlinarith
  -- Every entry has house at most `A = L ^ D₁ H ^ N`.
  set A : ℝ := (L : ℝ) ^ D₁ * H ^ N
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))) (one_le_pow₀ hH)
  have hmH' : house (m : K) ≤ H := ((house_intCast m).trans Int.cast_abs).trans_le hmH
  have heA (p q) : house (e p q) ≤ A :=
    house_schneider_entry_le hmH' (hwH p) hαH hγH (by exact_mod_cast (by omega : 1 ≤ L)) hH₀
      q.1.is_lt.le (hk p q)
  let a' : Matrix (Fin L × Fin L) (Fin D₁ × Fin D₂) (𝓞 K) := fun p q ↦ ⟨e p q, he p q⟩
  have hcard : finrank ℚ K * Fintype.card (Fin L × Fin L) < Fintype.card (Fin D₁ × Fin D₂) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith
  obtain ⟨x, hx0, hax, hxle⟩ := exists_ne_zero_int_vec_abs_le_of_house_le a' hA hcard heA
  refine ⟨fun i j ↦ x (i, j), fun h ↦ hx0 (funext fun q ↦ congr_fun₂ h q.1 q.2), fun i j ↦ ?_,
    fun u v hu₁ hu hv₁ hv ↦ ?_⟩
  · -- Siegel's exponent is at most `1`, since `2 d L² ≤ D₁ D₂`.
    refine (hxle (i, j)).trans ?_
    simp only [Fintype.card_prod, Fintype.card_fin]
    have hbase : 1 ≤ 3 * ((D₁ * D₂ : ℕ) : ℝ) * A := by
      have : (1 : ℝ) ≤ ((D₁ * D₂ : ℕ) : ℝ) := by exact_mod_cast hD₁D₂
      nlinarith
    have h2 : (2 * (finrank ℚ K * (L * L) : ℕ) : ℝ) ≤ (D₁ * D₂ : ℕ) := by
      exact_mod_cast (by nlinarith : 2 * (finrank ℚ K * (L * L)) ≤ D₁ * D₂)
    push_cast at hbase h2 ⊢
    have hbound := schneider_siegel_bound_le hL hD₁ hD₂ hH
    push_cast at hbound
    exact (rpow_div_sub_le_self hbase (by positivity) h2).trans hbound
  · -- The equation of the grid point `(u, v)`, divided by `m ^ N`.
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' hu₁
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le' hv₁
    set p : Fin L × Fin L := (⟨u, by omega⟩, ⟨v, by omega⟩)
    have hrow := sum_mul_intCast_eq_zero_of_mulVec_eq_zero hax p
    -- The coercion of the algebraic integer `a' p q = ⟨e p q, _⟩` to `K` is `e p q`.
    have ha'p (q) : (a' p q : K) = (m : K) ^ N * (w p ^ (q.1 : ℕ) *
        (α ^ ((u + 1) * q.2) * γ ^ ((v + 1) * q.2))) := hep p q
    simp only [ha'p, Fintype.sum_prod_type] at hrow
    have hm0 : (m : K) ^ N ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.2 hm)
    refine (mul_eq_zero.mp ?_).resolve_left hm0
    rw [← hrow, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [w, p]
    push_cast
    ring

/-! ### Size and denominators of the values `y_{uv}`

Schneider's proof evaluates `F` at the points `u + v σ β` of a grid larger than the one on which
it was made to vanish. The value there is the image under `σ` of
`y_{uv} = ∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j) ∈ K`, and the final contradiction
plays an upper bound for `|σ y_{uv}|` against Liouville's lower bound, which needs the house and
a denominator of `y_{uv}`. -/

/-- **The house of Schneider's values.** If `α`, `β`, `γ` have house at most `H ≥ 1` and the
integers `a_{ij}`, `i < D₁`, `j < D₂`, have absolute value at most `A`, then for `u, v ≤ B` with
`B ≥ 1` the house of `∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j)` is at most
`D₁ D₂ A (2 B) ^ D₁ H ^ (D₁ + 2 B D₂)`. -/
theorem house_schneider_value_le {α β γ : K} {H A : ℝ} (hH : 1 ≤ H) (hα : house α ≤ H)
    (hβ : house β ≤ H) (hγ : house γ ≤ H) {D₁ D₂ B : ℕ} (hB : 1 ≤ B)
    {a : Fin D₁ → Fin D₂ → ℤ} (ha : ∀ i j, |(a i j : ℝ)| ≤ A) {u v : ℕ} (hu : u ≤ B)
    (hv : v ≤ B) :
    house (∑ i, ∑ j, (a i j : K) * ((u : K) + v * β) ^ (i : ℕ) * (α ^ (u * j) * γ ^ (v * j))) ≤
      D₁ * D₂ * A * (2 * B) ^ D₁ * H ^ (D₁ + 2 * B * D₂) := by
  have hu' : (u : ℝ) ≤ B := by exact_mod_cast hu
  have hv' : (v : ℝ) ≤ B := by exact_mod_cast hv
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hw : house ((u : K) + v * β) ≤ (2 * B : ℕ) * H := by
    refine (house_add_le _ _).trans ?_
    rw [← mul_one (u : K), house_nat_mul, house_nat_mul, ← Int.cast_one, house_intCast]
    push_cast
    rw [abs_one, mul_one]
    nlinarith [house_nonneg β]
  -- Each term is `a_{ij}` times an entry of house at most `(2 B) ^ D₁ H ^ (D₁ + 2 B D₂)`.
  have hterm (i : Fin D₁) (j : Fin D₂) :
      house ((a i j : K) * ((u : K) + v * β) ^ (i : ℕ) * (α ^ (u * j) * γ ^ (v * j))) ≤
        A * ((2 * B : ℕ) ^ D₁ * H ^ (D₁ + 2 * B * D₂)) := by
    have hk := schneider_exponent_le i j hu hv
    have h1 : house (1 : K) ≤ H := by
      rw [← Int.cast_one, house_intCast]
      simpa using hH
    have he := house_schneider_entry_le h1 hw hα hγ
      (by exact_mod_cast (by omega : 1 ≤ 2 * B)) (by linarith) i.is_lt.le hk
    rw [one_pow, one_mul] at he
    rw [mul_assoc]
    exact house_mul_le_of_le (by rw [house_intCast, Int.cast_abs]; exact ha i j) he
  refine (house_sum_le_sum_house _ _).trans ?_
  refine (sum_le_sum fun i _ ↦ house_sum_le_sum_house _ _).trans ?_
  refine (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hterm i j).trans (le_of_eq ?_)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- The explicit bound of `house_schneider_value_le` with `A = exp (c₁ E)` and `B = c L + 1`,
where `E = D₁ log L + D₂ L`, is at most `exp (C E)` for a constant `C` depending only on `c₁`, `c`
and `H`, as soon as `L ≥ 2`. -/
private theorem schneider_value_bound_le_exp {c₁ H : ℝ} {c L D₁ D₂ : ℕ} (hH : 1 ≤ H)
    (hL : 2 ≤ L) :
    (D₁ : ℝ) * D₂ * Real.exp (c₁ * (D₁ * Real.log L + D₂ * L)) * (2 * ((c : ℝ) * L + 1)) ^ D₁ *
        H ^ (D₁ + 2 * (c * L + 1) * D₂) ≤
      Real.exp ((3 + |c₁| + 2 * Real.log (2 * c + 2) + (2 * c + 2) * Real.log H) *
        (D₁ * Real.log L + D₂ * L)) := by
  set E : ℝ := D₁ * Real.log L + D₂ * L
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hlogL : 1 / 2 ≤ Real.log L := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hL']
  have hD₁ : (0 : ℝ) ≤ D₁ := D₁.cast_nonneg
  have hD₂ : (0 : ℝ) ≤ D₂ := D₂.cast_nonneg
  have hlogH := Real.log_nonneg hH
  have hlogc : 0 ≤ Real.log (2 * c + 2) := Real.log_nonneg (by linarith [c.cast_nonneg' (α := ℝ)])
  have hE : 0 ≤ E := by positivity
  -- Each factor of the explicit bound is the exponential of a multiple of at most `E`.
  have h2B : 0 < 2 * ((c : ℝ) * L + 1) := by positivity
  have hlog2B : Real.log (2 * ((c : ℝ) * L + 1)) ≤ Real.log (2 * c + 2) + Real.log L := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log h2B (by nlinarith)
  have hfac₁ : (D₁ : ℝ) * D₂ ≤ Real.exp (D₁ + D₂) := by
    rw [Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (D₁ : ℝ)])
      (by linarith [Real.add_one_le_exp (D₂ : ℝ)]) hD₂ (Real.exp_pos _).le
  have hfac₂ : (2 * ((c : ℝ) * L + 1)) ^ D₁ = Real.exp (D₁ * Real.log (2 * ((c : ℝ) * L + 1))) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hfac₃ : H ^ (D₁ + 2 * (c * L + 1) * D₂) =
      Real.exp (((D₁ + 2 * (c * L + 1) * D₂ : ℕ) : ℝ) * Real.log H) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  push_cast at hfac₃
  rw [hfac₂, hfac₃]
  calc (D₁ : ℝ) * D₂ * Real.exp (c₁ * E) * Real.exp (D₁ * Real.log (2 * ((c : ℝ) * L + 1))) *
        Real.exp ((D₁ + 2 * ((c : ℝ) * L + 1) * D₂) * Real.log H)
      ≤ Real.exp (D₁ + D₂) * Real.exp (c₁ * E) *
          Real.exp (D₁ * Real.log (2 * ((c : ℝ) * L + 1))) *
          Real.exp ((D₁ + 2 * ((c : ℝ) * L + 1) * D₂) * Real.log H) := by
        gcongr
    _ = Real.exp (D₁ + D₂ + c₁ * E + D₁ * Real.log (2 * ((c : ℝ) * L + 1)) +
          (D₁ + 2 * ((c : ℝ) * L + 1) * D₂) * Real.log H) := by
        simp only [Real.exp_add]
    _ ≤ Real.exp ((3 + |c₁| + 2 * Real.log (2 * c + 2) + (2 * c + 2) * Real.log H) * E) := by
        rw [Real.exp_le_exp]
        -- `D₁ ≤ 2 D₁ log L`, `D₂ ≤ D₂ L` and `D₁ + 2 (c L + 1) D₂ ≤ (2 c + 2) E`.
        have h₁ : (D₁ : ℝ) ≤ 2 * (D₁ * Real.log L) := by nlinarith
        have h₂ : (D₂ : ℝ) ≤ D₂ * L := by nlinarith
        have h₃ : c₁ * E ≤ |c₁| * E := mul_le_mul_of_nonneg_right (le_abs_self c₁) hE
        have h₄ : D₁ * Real.log (2 * ((c : ℝ) * L + 1)) ≤
            (1 + 2 * Real.log (2 * c + 2)) * E := by
          have : (D₁ : ℝ) * Real.log (2 * c + 2) ≤
              2 * Real.log (2 * c + 2) * (D₁ * Real.log L) := by
            nlinarith
          have : (D₁ : ℝ) * Real.log L ≤ E := by simp only [E]; nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hlog2B hD₁]
        have h₅ : (D₁ + 2 * ((c : ℝ) * L + 1) * D₂) * Real.log H ≤
            (2 * c + 2) * Real.log H * E := by
          have : (D₁ + 2 * ((c : ℝ) * L + 1) * D₂) ≤ (2 * c + 2) * E := by
            simp only [E]
            have hc : (0 : ℝ) ≤ c := c.cast_nonneg
            nlinarith
          nlinarith
        nlinarith

/-- **Schneider's values on an extended grid.** Let `α, β, γ ∈ K`, `c₁ ∈ ℝ` and `c ∈ ℕ`. There
is `C ≥ 0` such that for all integers `L ≥ 2`, `D₁` and `D₂`, all integers `a_{ij}`, `i < D₁`,
`j < D₂`, with `|a_{ij}| ≤ exp (c₁ (D₁ log L + D₂ L))`, and all `u, v ≤ c L`, the house of
`∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j)` is at most `exp (C (D₁ log L + D₂ L))`. -/
theorem exists_house_schneider_value_le_exp (α β γ : K) (c₁ : ℝ) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L D₁ D₂ : ℕ, 2 ≤ L → ∀ a : Fin D₁ → Fin D₂ → ℤ,
      (∀ i j, |(a i j : ℝ)| ≤ Real.exp (c₁ * (D₁ * Real.log L + D₂ * L))) →
      ∀ u v : ℕ, u ≤ c * L → v ≤ c * L →
        house (∑ i, ∑ j, (a i j : K) * ((u : K) + v * β) ^ (i : ℕ) *
          (α ^ (u * j) * γ ^ (v * j))) ≤ Real.exp (C * (D₁ * Real.log L + D₂ * L)) := by
  set H : ℝ := 1 + house α + house β + house γ
  have hα := house_nonneg α
  have hβ := house_nonneg β
  have hγ := house_nonneg γ
  have hH : 1 ≤ H := by linarith
  have hlogc : 0 ≤ Real.log (2 * c + 2) := Real.log_nonneg (by linarith [c.cast_nonneg' (α := ℝ)])
  refine ⟨3 + |c₁| + 2 * Real.log (2 * c + 2) + (2 * c + 2) * Real.log H,
    by have := Real.log_nonneg hH; positivity,
    fun L D₁ D₂ hL a ha u v hu hv ↦ ?_⟩
  -- The explicit bound with `B = c L + 1`.
  refine (house_schneider_value_le (B := c * L + 1) hH (by linarith : house α ≤ H)
    (by linarith : house β ≤ H) (by linarith : house γ ≤ H) (by omega) ha
    (by omega : u ≤ c * L + 1) (by omega : v ≤ c * L + 1)).trans ?_
  push_cast
  exact schneider_value_bound_le_exp hH hL

/-- The parameters `L = 2 d M ²`, `D₁ = (2 d) ² M ³` and `D₂ = 2 d M` of Schneider's proof satisfy
`D₁ = √(2 d) L ^ (3 / 2)` and `D₂ L = √(2 d) L ^ (3 / 2)`. -/
private theorem schneider_params {d M L D₁ D₂ : ℕ} (hL : L = 2 * d * M ^ 2)
    (hD₁ : D₁ = (2 * d) ^ 2 * M ^ 3) (hD₂ : D₂ = 2 * d * M) :
    (D₁ : ℝ) = √(2 * d) * (L : ℝ) ^ (3 / 2 : ℝ) ∧
      (D₂ : ℝ) * L = √(2 * d) * (L : ℝ) ^ (3 / 2 : ℝ) := by
  have hpow : (L : ℝ) ^ (3 / 2 : ℝ) = L * √L := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' L.cast_nonneg (by norm_num),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hsqrt : √(L : ℝ) = √(2 * d) * M := by
    rw [hL]
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq M.cast_nonneg]
  have hs : √(2 * d : ℝ) * √(2 * d) = 2 * d := Real.mul_self_sqrt (by positivity)
  rw [hpow, hsqrt]
  subst hL hD₁ hD₂
  push_cast
  constructor <;> linear_combination (-(2 * (d : ℝ) * M ^ 3)) * hs

/-- **The house of Schneider's values** (Evertse, Lemma 4.27(ii)). Let `K` be a number field of
degree `d`, let `α, β, γ ∈ K`, `c₁ ∈ ℝ` and `c ∈ ℕ`. There is `c₅` such that, for every integer
`M ≥ 1` with `L = 2 d M²`, `D₁ = (2 d)² M³` and `D₂ = 2 d M`, all integers `a_{ij}`, `i < D₁`,
`j < D₂`, with `|a_{ij}| ≤ exp (c₁ (D₁ log L + D₂ L))` (the bound of
`exists_schneider_auxiliary_algebraic`) and all `u, v ≤ c L`, the value
`y_{uv} = ∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j)` has house at most
`exp (c₅ L ^ (3 / 2) log L)`. In particular `‖σ y_{uv}‖` satisfies the same bound for every
embedding `σ : K →+* ℂ` (`NumberField.norm_embedding_le_house`). Evertse takes
`c = 1 + ⌊√(2 d)⌋`. -/
theorem exists_house_schneider_value_le_exp_rpow (α β γ : K) (c₁ : ℝ) (c : ℕ) :
    ∃ c₅ : ℝ, ∀ M L D₁ D₂ : ℕ, 1 ≤ M → L = 2 * finrank ℚ K * M ^ 2 →
      D₁ = (2 * finrank ℚ K) ^ 2 * M ^ 3 → D₂ = 2 * finrank ℚ K * M →
      ∀ a : Fin D₁ → Fin D₂ → ℤ,
      (∀ i j, |(a i j : ℝ)| ≤ Real.exp (c₁ * (D₁ * Real.log L + D₂ * L))) →
      ∀ u v : ℕ, u ≤ c * L → v ≤ c * L →
        house (∑ i, ∑ j, (a i j : K) * ((u : K) + v * β) ^ (i : ℕ) *
          (α ^ (u * j) * γ ^ (v * j))) ≤
          Real.exp (c₅ * (L : ℝ) ^ (3 / 2 : ℝ) * Real.log L) := by
  obtain ⟨C, hC, h⟩ := exists_house_schneider_value_le_exp α β γ c₁ c
  refine ⟨3 * √(2 * finrank ℚ K) * C, fun M L D₁ D₂ hM hL hD₁ hD₂ a ha u v hu hv ↦ ?_⟩
  have hd : 1 ≤ finrank ℚ K := finrank_pos
  have hL₂ : 2 ≤ L := by
    rw [hL]
    nlinarith [Nat.one_le_pow 2 M hM]
  refine (h L D₁ D₂ hL₂ a ha u v hu hv).trans (Real.exp_le_exp.2 ?_)
  obtain ⟨h₁, h₂⟩ := schneider_params hL hD₁ hD₂
  have hlogL : 1 / 2 ≤ Real.log L := by
    linarith [Real.log_two_gt_d9,
      Real.log_le_log (by norm_num) (by exact_mod_cast hL₂ : (2 : ℝ) ≤ L)]
  have hQ : 0 ≤ √(2 * finrank ℚ K : ℝ) * (L : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [h₁, h₂]
  -- `D₁ log L + D₂ L = √(2 d) L ^ (3 / 2) (log L + 1) ≤ 3 √(2 d) L ^ (3 / 2) log L`.
  nlinarith [mul_le_mul_of_nonneg_left hlogL (mul_nonneg hC hQ)]

/-- **The size of the denominator of Schneider's values** (Evertse, Lemma 4.27). For
`d, c ∈ ℕ` and `m ∈ ℝ` there is `c₆` such that, for `L = 2 d M²`, `D₁ = (2 d)² M³` and
`D₂ = 2 d M`, the denominator `m ^ (D₁ + 2 c L D₂)` of the values `y_{uv}`, `u, v ≤ c L`
(`isIntegral_intCast_pow_mul_schneider_value`), satisfies
`|m| ^ (D₁ + 2 c L D₂) ≤ exp (c₆ L ^ (3 / 2))`. -/
theorem exists_abs_pow_schneider_exponent_le_exp_rpow (d c : ℕ) (m : ℝ) :
    ∃ c₆ : ℝ, ∀ M L D₁ D₂ : ℕ, L = 2 * d * M ^ 2 → D₁ = (2 * d) ^ 2 * M ^ 3 →
      D₂ = 2 * d * M → |m| ^ (D₁ + 2 * (c * L) * D₂) ≤ Real.exp (c₆ * (L : ℝ) ^ (3 / 2 : ℝ)) := by
  refine ⟨(1 + 2 * c) * √(2 * d) * Real.log (max 1 |m|), fun M L D₁ D₂ hL hD₁ hD₂ ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := schneider_params hL hD₁ hD₂
  have hN : ((D₁ + 2 * (c * L) * D₂ : ℕ) : ℝ) =
      (1 + 2 * c) * (√(2 * d) * (L : ℝ) ^ (3 / 2 : ℝ)) := by
    push_cast
    linear_combination h₁ + 2 * (c : ℝ) * h₂
  calc |m| ^ (D₁ + 2 * (c * L) * D₂) ≤ max 1 |m| ^ (D₁ + 2 * (c * L) * D₂) :=
        pow_le_pow_left₀ (abs_nonneg m) (le_max_right 1 |m|) _
    _ = Real.exp ((D₁ + 2 * (c * L) * D₂ : ℕ) * Real.log (max 1 |m|)) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
    _ = _ := by
        rw [hN]
        ring_nf

end TauCeti

namespace RingHom

/-- If `σ α = exp λ` and `σ γ = exp (σ β λ)`, then
`σ (α ^ (u j) γ ^ (v j)) = exp (j λ (u + v σ β))`: the value of the exponential `exp (j λ z)` at
`z = u + v σ β` lies in the image of `σ`. -/
theorem map_pow_mul_pow_eq_exp {R : Type*} [Semiring R] (σ : R →+* ℂ) {l : ℂ} {α β γ : R}
    (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l)) (u v j : ℕ) :
    σ (α ^ (u * j) * γ ^ (v * j)) = Complex.exp (j * l * (u + v * σ β)) := by
  rw [map_mul, map_pow, map_pow, hα, hγ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {K : Type*} [Field K] [NumberField K]

/-- **Schneider's auxiliary function** (Evertse, Lemma 4.22). Let `K` be a number field of degree
`d` with an embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and `α, β, γ ∈ K` with `σ α = exp λ` and
`σ γ = exp (σ β λ)`. There is `c > 0` such that for all integers `L ≥ 3` and `D₁, D₂` with
`D₁ D₂ ≥ 2 d L²` there are integers `a_{ij}`, `i < D₁`, `j < D₂`, not all zero, with
`|a_{ij}| ≤ exp (c (D₁ log L + D₂ L))`, such that
`F(z) = ∑_{i, j} a_{ij} z ^ i exp (j λ z)` vanishes at `z = u + v σ β` for all `1 ≤ u, v ≤ L`. -/
theorem exists_schneider_auxiliary (σ : K →+* ℂ) {l : ℂ} {α β γ : K} (hα : σ α = Complex.exp l)
    (hγ : σ γ = Complex.exp (σ β * l)) :
    ∃ c : ℝ, 0 < c ∧ ∀ L D₁ D₂ : ℕ, 3 ≤ L → 2 * finrank ℚ K * L ^ 2 ≤ D₁ * D₂ →
      ∃ a : Fin D₁ → Fin D₂ → ℤ, a ≠ 0 ∧
        (∀ i j, |(a i j : ℝ)| ≤ Real.exp (c * (D₁ * Real.log L + D₂ * L))) ∧
        ∀ u v : ℕ, 1 ≤ u → u ≤ L → 1 ≤ v → v ≤ L →
          ∑ i, ∑ j, (a i j : ℂ) * ((u : ℂ) + v * σ β) ^ (i : ℕ) *
            Complex.exp (j * l * (u + v * σ β)) = 0 := by
  obtain ⟨c, hc, h⟩ := TauCeti.exists_schneider_auxiliary_algebraic α β γ
  refine ⟨c, hc, fun L D₁ D₂ hL hD ↦ ?_⟩
  obtain ⟨a, ha, hbound, hzero⟩ := h L D₁ D₂ hL hD
  refine ⟨a, ha, hbound, fun u v hu₁ hu hv₁ hv ↦ ?_⟩
  have := congr_arg σ (hzero u v hu₁ hu hv₁ hv)
  simpa only [map_sum, map_mul, map_pow, map_add, map_intCast, map_natCast, map_zero,
    map_pow_mul_pow_eq_exp σ hα hγ] using this

end RingHom
