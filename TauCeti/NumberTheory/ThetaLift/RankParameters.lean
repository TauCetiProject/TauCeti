/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Degree and rank bounds for a chain of theta lifts

A degree large enough to generate integral forms increases the rank of the ambient Hermitian
space. The polynomial rank windows leave room for both requirements: a lower bound on the
chosen degree and an upper bound on the resulting rank. The estimates are uniform in the
host degree, the two chosen ranks, and the density of the distinguished places.

The parameters are those of Levent Alpöge's construction of theta chains in his
[formalization of the Riemann hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
notably `Formalism.MainNotions.Lnk.Win_at` and `Formalism.BasicNotions.Ranks`.
-/

public section

open Filter Real

namespace TauCeti.ThetaLift

private theorem degreeBudget_le {x F K M ε C f r k m δ : ℝ}
    (hx : 0 < x) (hf₀ : 0 ≤ f) (hr₁ : 1 ≤ r) (hk₀ : 0 ≤ k)
    (hf : f ≤ 4 * x ^ F) (hr : r ≤ 4 * x ^ K) (hk : k ≤ 2 * x ^ K)
    (hm : x ^ M ≤ m) (hδ : x ^ (-ε) ≤ δ) :
    (C * (f * r * x ^ ε) ^ 12) ^ 4 * (f * r * (r - 1) / 2) ^ 3 * k * f * x / (m * δ) ≤
      (C ^ 4 * 16 ^ 48 * 32 ^ 3 * 8) * x ^ (48 * (F + K + ε) + 3 * (F + 2 * K) +
        K + F + 1 - (M - ε)) := by
  have hD : f * r * (r - 1) / 2 ≤ 32 * x ^ (F + 2 * K) := calc
    _ ≤ (4 * x ^ F) * (4 * x ^ K) * (4 * x ^ K) / 2 := by
      gcongr; linarith
    _ = _ := by
      have hpow : x ^ (2 * K) = (x ^ K) ^ (2 : ℕ) := by
        rw [mul_comm]
        exact rpow_mul_natCast hx.le K 2
      rw [rpow_add hx, hpow]
      ring
  have hP : f * r * x ^ ε ≤ 16 * x ^ (F + K + ε) := calc
    _ ≤ (4 * x ^ F) * (4 * x ^ K) * x ^ ε := by gcongr
    _ = _ := by simp only [rpow_add hx]; ring
  have hm₀ := (rpow_pos_of_pos hx M).trans_le hm
  rw [mul_pow]
  calc
    _ ≤ C ^ 4 * ((16 * x ^ (F + K + ε)) ^ 12) ^ (4 : ℕ) *
        (32 * x ^ (F + 2 * K)) ^ 3 * (2 * x ^ K) * (4 * x ^ F) * x /
          (x ^ M * x ^ (-ε)) := by gcongr
    _ = _ := by
      rw [← pow_mul]
      norm_num only [Nat.reduceMul]
      simp only [mul_pow, ← rpow_mul_natCast hx.le, Nat.cast_ofNat]
      rw [rpow_sub hx, rpow_sub hx]
      simp only [rpow_add hx, rpow_one, rpow_neg hx.le, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring_nf

private theorem rowSize_le {x F K M ε : ℝ} {f r k m : ℕ}
    (hx : 1 ≤ x) (hf : (f : ℝ) ≤ 4 * x ^ F) (hr : (r : ℝ) ≤ 4 * x ^ K)
    (hk : (k : ℝ) ≤ 2 * x ^ K) (hm : x ^ M ≤ m)
    (hdom : F + K ≤ K + 2 * F + 3 * K + 2 * ε - M)
    (hexp : 0 ≤ K + 2 * F + 3 * K + 2 * ε - M) :
    ((8 * ⌈10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ) ^ 3 * x ^ (2 * ε) / m) / 8⌉₊
      : ℕ) : ℝ) ≤ 5300 * x ^ (K + 2 * F + 3 * K + 2 * ε - M) := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hmk : (0 : ℝ) < m := (rpow_pos_of_pos hx₀ _).trans_le hm
  have hf' : 10 * (r : ℝ) * f ≤ 160 * x ^ (K + F) := calc
    _ ≤ 10 * (4 * x ^ K) * (4 * x ^ F) := by gcongr
    _ = _ := by rw [rpow_add hx₀]; ring
  have hk' : ((k - 1 : ℕ) : ℝ) ≤ 2 * x ^ K :=
    (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hk
  have hterm : 10 * (r : ℝ) * ((f : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ) ^ 3 * x ^ (2 * ε) / m) ≤
      5120 * x ^ (K + 2 * F + 3 * K + 2 * ε - M) := calc
    _ ≤ 10 * (4 * x ^ K) * ((4 * x ^ F) ^ 2 * (2 * x ^ K) ^ 3 * x ^ (2 * ε) / x ^ M) := by
      gcongr
    _ = _ := by
      have h₂ : x ^ (2 * F) = (x ^ F) ^ (2 : ℕ) := by
        rw [mul_comm]
        exact rpow_mul_natCast hx₀.le F 2
      have h₃ : x ^ (3 * K) = (x ^ K) ^ (3 : ℕ) := by
        rw [mul_comm]
        exact rpow_mul_natCast hx₀.le K 3
      simp only [rpow_sub hx₀, rpow_add hx₀, h₂, h₃]
      ring
  have hp := rpow_le_rpow_of_exponent_le hx hdom
  rw [add_comm] at hp
  have hsum := add_le_add (hf'.trans (mul_le_mul_of_nonneg_left hp (by norm_num))) hterm
  have hone : 1 ≤ x ^ (K + 2 * F + 3 * K + 2 * ε - M) := one_le_rpow hx hexp
  push_cast
  have hceil := Nat.ceil_lt_add_one (by positivity :
    0 ≤ 10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ) ^ 3 * x ^ (2 * ε) / m) / 8)
  linarith only [hceil, hsum, hone]

private theorem ambientRank_le {x F K E c : ℝ} {f r nW t : ℕ}
    (hx : 1 ≤ x) (hc : 0 ≤ c) (hE : F + K ≤ E)
    (hf : (f : ℝ) ≤ 4 * x ^ F) (hr : (r : ℝ) ≤ 4 * x ^ K) (hn : (nW : ℝ) ≤ 5300 * x ^ E)
    (h : r + t = 8 * f * r + 4 + ⌈x ^ c⌉₊ * nW) (hE₀ : 0 ≤ E) :
    (t : ℝ) ≤ 11000 * x ^ (c + E) := by
  have hx₀ := zero_lt_one.trans_le hx
  have hfr : (f : ℝ) * r ≤ 16 * x ^ (c + E) := calc
    _ ≤ (4 * x ^ F) * (4 * x ^ K) := by gcongr
    _ = 16 * x ^ (F + K) := by rw [rpow_add hx₀]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hx (by linarith)) (by norm_num)
  have hT : (⌈x ^ c⌉₊ : ℝ) ≤ 2 * x ^ c :=
    (Nat.ceil_lt_add_one (by positivity)).le.trans (by linarith [one_le_rpow hx hc])
  have hprod : (⌈x ^ c⌉₊ : ℝ) * nW ≤ 10600 * x ^ (c + E) := calc
    _ ≤ (2 * x ^ c) * (5300 * x ^ E) := by gcongr
    _ = _ := by rw [rpow_add hx₀]; ring
  have ht : t ≤ 8 * f * r + 4 + ⌈x ^ c⌉₊ * nW := (Nat.le_add_left _ _).trans_eq h
  have ht' : (t : ℝ) ≤ 8 * ((f : ℝ) * r) + 4 + (⌈x ^ c⌉₊ : ℝ) * nW := by
    have hh : t ≤ 8 * (f * r) + 4 + ⌈x ^ c⌉₊ * nW := by simpa only [mul_assoc] using ht
    exact_mod_cast hh
  linarith only [ht', hfr, hprod, one_le_rpow hx (add_nonneg hc hE₀)]

/-- For every sufficiently large scale and every choice of ranks in the prescribed windows,
`T = ⌈x ^ c⌉` meets the integral-generation degree bound with a factor `x` to spare. The
corresponding ambient rank `r + t` has `t ≤ x ^ C` and odd `t` when `k + m` is even. Here `f`
is the number of places and `δ` is the positive density entering the generation bound. -/
theorem eventually_exists_thetaChainRank_with_degree_bound {ε c C : ℝ} (hε : 0 ≤ ε)
    (hc : 352 + (16241 / 16) * ε < c) (hC : c + 43 / 2 + (929 / 16) * ε < C) (Cp : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ (f k m : ℕ) (δ : ℝ),
      0 < f → (f : ℝ) ≤ 4 * x ^ (2 + 8 * ε) →
      (k : ℝ) ≤ 2 * x ^ (9 / 2 + 10 * ε) →
      x ^ (1 / 2 - ε / 16) ≤ (m : ℝ) → (m : ℝ) ≤ 2 * x ^ (1 / 2 - ε / 16) →
      x ^ (-ε) ≤ δ → Even (k + m) →
      let r := k + m - 1
      let nW := 8 * ⌈10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ) ^ 3 *
        x ^ (2 * ε) / m) / 8⌉₊
      let T := ⌈x ^ c⌉₊
      (Cp * ((f : ℝ) * r * x ^ ε) ^ 12) ^ 4 * ((f : ℝ) * r * (r - 1 : ℝ) / 2) ^ 3 *
        k * f * x / (m * δ) ≤ T ∧
      ∃ t : ℕ, Odd t ∧ r + t = 8 * f * r + 4 + T * nW ∧ (t : ℝ) ≤ x ^ C := by
  have hc₀ : 0 ≤ c := by linarith
  let F : ℝ := 2 + 8 * ε
  let K : ℝ := 9 / 2 + 10 * ε
  let M : ℝ := 1 / 2 - ε / 16
  -- `E` bounds the rounded row size, while `B` bounds the generation budget before rounding.
  let E : ℝ := K + 2 * F + 3 * K + 2 * ε - M
  let B : ℝ := 48 * (F + K + ε) + 3 * (F + 2 * K) + K + F + 1 - (M - ε)
  have hB : B < c := by dsimp [B, F, K, M]; linarith
  have hE : c + E < C := by dsimp [E, F, K, M]; linarith
  have hdom : F + K ≤ E := by dsimp [E, F, K, M]; linarith
  have hE₀ : 0 ≤ E := by dsimp [E, F, K, M]; linarith
  have hMK : M ≤ K := by dsimp [M, K]; linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    ((isLittleO_rpow_rpow_atTop hB).const_mul_left (Cp ^ 4 * 16 ^ 48 * 32 ^ 3 * 8)).bound one_pos,
    ((isLittleO_rpow_rpow_atTop hE).const_mul_left 11000).bound one_pos] with x hx hb he
  intro f k m δ hf₀ hf hk hm₁ hm hδ hpar r nW T
  have hx₀ := zero_lt_one.trans_le hx
  have hm' : 1 ≤ m := Nat.cast_pos.mp ((rpow_pos_of_pos hx₀ M).trans_le hm₁)
  have hr₁ : 1 ≤ r := by
    have := Nat.even_iff.mp hpar
    dsimp only [r]
    omega
  have hr : (r : ℝ) ≤ 4 * x ^ K := by
    have hrs : (r : ℝ) ≤ (k : ℝ) + m := by exact_mod_cast (Nat.sub_le (k + m) 1)
    have hmK := hm.trans <| mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_exponent_le hx hMK) (by norm_num)
    linarith only [hrs, hmK, hk]
  refine ⟨(degreeBudget_le hx₀ (by positivity) (by exact_mod_cast hr₁) (by positivity)
    hf hr hk hm₁ hδ).trans ((le_abs_self _).trans ?_) |>.trans (Nat.le_ceil _), ?_⟩
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx₀.le c), one_mul] using hb
  · have hle : r ≤ 8 * f * r + 4 + T * nW := by
      have : r ≤ 8 * f * r := by simpa using Nat.mul_le_mul_right r (show 1 ≤ 8 * f by omega)
      omega
    have heq : r + (8 * f * r + 4 + T * nW - r) = 8 * f * r + 4 + T * nW := by omega
    have hodd : Odd r := (Nat.odd_sub' (by omega : 1 ≤ k + m)).mpr (iff_of_true odd_one hpar)
    have hn : Even nW := Nat.even_mul.mpr (Or.inl (by decide : Even (8 : ℕ)))
    have h8 : Even (8 * f * r) := (show Even (8 : ℕ) by decide).mul_right f |>.mul_right r
    have htot := (h8.add (by decide : Even (4 : ℕ))).add (hn.mul_left T)
    refine ⟨_, (Nat.odd_sub' hle).mpr (iff_of_true hodd htot), heq, ?_⟩
    refine (ambientRank_le hx hc₀ hdom hf hr
      (rowSize_le hx hf hr hk hm₁ hdom hE₀) heq hE₀).trans ((le_abs_self _).trans ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx₀.le C), one_mul] using he

end TauCeti.ThetaLift
