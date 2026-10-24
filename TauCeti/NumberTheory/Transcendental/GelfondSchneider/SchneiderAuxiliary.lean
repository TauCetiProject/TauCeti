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
(`TauCeti.map_pow_mul_pow_eq_exp`), the value `F(u + v σ β)` is the image under `σ` of

`y_{uv} = ∑_{i, j} a_{ij} (u + v β) ^ i α ^ (u j) γ ^ (v j) ∈ K`,

so the vanishing conditions are `L²` linear equations over `K` in the `D₁ D₂` integer unknowns
`a_{ij}`. When `D₁ D₂ ≥ 2 d L²`, Siegel's lemma with rational integer unknowns
(`NumberField.exists_ne_zero_int_vec_abs_le_of_house_le`) solves them with
`|a_{ij}| ≤ exp (c (D₁ log L + D₂ L))`, where `c` depends only on `K`, `α`, `β` and `γ`. To apply
it, each equation is multiplied by `m ^ (D₁ + 2 L D₂)` for a nonzero integer `m` such that
`m α`, `m β` and `m γ` are algebraic integers.

The zero estimate for real exponential polynomials and Schwarz's lemma with prescribed zeros then
show that such an `F` cannot vanish at too many further grid points when `α` and `β` are real.

## Main results

* `TauCeti.exists_schneider_auxiliary_algebraic`: a nonzero integer coefficient matrix with the
  bound above for which every `y_{uv}`, `1 ≤ u, v ≤ L`, vanishes in `K`.
* `TauCeti.map_pow_mul_pow_eq_exp`: `σ (α ^ (u j) γ ^ (v j)) = exp (j λ (u + v σ β))`.
* `TauCeti.exists_schneider_auxiliary`: the auxiliary function `F` vanishes at the grid points
  `u + v σ β`, `1 ≤ u, v ≤ L`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Lemma 4.22.
-/

public section

open Finset Module NumberField

namespace TauCeti

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

variable {K : Type*} [Field K] [NumberField K]

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
  have hk (p : Fin L × Fin L) (q : Fin D₁ × Fin D₂) : k p q ≤ N := by
    have h₁ := q.1.is_lt
    have h₂ : ((p.1 : ℕ) + 1) * q.2 ≤ L * D₂ := Nat.mul_le_mul p.1.is_lt q.2.is_lt.le
    have h₃ : ((p.2 : ℕ) + 1) * q.2 ≤ L * D₂ := Nat.mul_le_mul p.2.is_lt q.2.is_lt.le
    simp only [k, N]
    linarith
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
  have he (p q) : IsIntegral ℤ (e p q) := by
    have hmw : IsIntegral ℤ ((m : K) * w p) := by
      rw [hmw_eq]
      exact (isIntegral_intCast _).add ((isIntegral_natCast _).mul hmβ)
    exact (((isIntegral_intCast _).pow _).mul (hmw.pow _)).mul ((hmα.pow _).mul (hmγ.pow _))
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
  have heA (p q) : house (e p q) ≤ A := by
    have hmul {x y : K} {X Y : ℝ} (hx : house x ≤ X) (hy : house y ≤ Y) (hY : 0 ≤ Y) :
        house (x * y) ≤ X * Y :=
      (house_mul_le x y).trans (mul_le_mul hx hy (house_nonneg y) ((house_nonneg x).trans hx))
    have hpow {x : K} {X : ℝ} (hx : house x ≤ X) (n : ℕ) : house (x ^ n) ≤ X ^ n := by
      rw [house_pow]
      exact pow_le_pow_left₀ (house_nonneg x) hx n
    have hmH' : house (m : K) ≤ H := ((house_intCast m).trans Int.cast_abs).trans_le hmH
    have h := hmul (hmul (hpow hmH' (N - k p q)) (hpow (hwH p) q.1) (by positivity))
      (hmul (hpow hαH (((p.1 : ℕ) + 1) * q.2)) (hpow hγH (((p.2 : ℕ) + 1) * q.2)) (by positivity))
      (by positivity)
    refine h.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ L)) q.1.is_lt.le) (by positivity)))
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (hk p q)
    rw [show N - k p q = r by omega, hr, mul_pow]
    simp only [k]
    ring
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
    have hexp : ((finrank ℚ K * (L * L) : ℕ) : ℝ) / ((D₁ * D₂ : ℕ) - (finrank ℚ K * (L * L) : ℕ))
        ≤ 1 := by
      have h2 : (2 * (finrank ℚ K * (L * L) : ℕ) : ℝ) ≤ (D₁ * D₂ : ℕ) := by
        exact_mod_cast (by nlinarith : 2 * (finrank ℚ K * (L * L)) ≤ D₁ * D₂)
      have h0 : (0 : ℝ) ≤ (finrank ℚ K * (L * L) : ℕ) := Nat.cast_nonneg _
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    push_cast at hexp hbase ⊢
    calc _ ≤ (3 * ((D₁ : ℝ) * D₂) * A) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ = 3 * ((D₁ * D₂ : ℕ) : ℝ) * A := by push_cast; exact Real.rpow_one _
      _ ≤ _ := schneider_siegel_bound_le hL hD₁ hD₂ hH
  · -- The equation of the grid point `(u, v)`, divided by `m ^ N`.
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le' hu₁
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le' hv₁
    set p : Fin L × Fin L := (⟨u, by omega⟩, ⟨v, by omega⟩)
    have hrow := sum_mul_intCast_eq_zero_of_mulVec_eq_zero hax p
    have hep (q) : (a' p q : K) = (m : K) ^ N * (w p ^ (q.1 : ℕ) *
        (α ^ ((u + 1) * q.2) * γ ^ ((v + 1) * q.2))) := by
      -- The coercion of the algebraic integer `a' p q = ⟨e p q, _⟩` to `K` is `e p q`.
      change e p q = _
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (hk p q)
      simp only [e]
      rw [show N - k p q = r by omega, hr]
      simp only [k, p, mul_pow]
      ring
    simp only [hep, Fintype.sum_prod_type] at hrow
    have hm0 : (m : K) ^ N ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.2 hm)
    refine (mul_eq_zero.mp ?_).resolve_left hm0
    rw [← hrow, mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [w, p]
    push_cast
    ring

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
  obtain ⟨c, hc, h⟩ := exists_schneider_auxiliary_algebraic α β γ
  refine ⟨c, hc, fun L D₁ D₂ hL hD ↦ ?_⟩
  obtain ⟨a, ha, hbound, hzero⟩ := h L D₁ D₂ hL hD
  refine ⟨a, ha, hbound, fun u v hu₁ hu hv₁ hv ↦ ?_⟩
  have := congr_arg σ (hzero u v hu₁ hu hv₁ hv)
  simpa only [map_sum, map_mul, map_pow, map_add, map_intCast, map_natCast, map_zero,
    map_pow_mul_pow_eq_exp σ hα hγ] using this

end TauCeti
