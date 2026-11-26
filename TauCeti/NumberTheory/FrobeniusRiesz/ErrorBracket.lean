/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The error bracket for Frobenius-restricted Riesz sums

The averaged Frobenius inequality has a main coefficient `P * m * b * (T / N) / 2`,
where `P` counts the tops, `T` counts the thick set, and `N` is the size of the ambient
group. Dividing by this coefficient makes the first two costs involving the scale term `a`
proportional to `a / (m * b)` and `a * m / (k * b)`. The term that already contains `T`
does not incur a reciprocal thick-set density. With `m` near the square root of the scale `x`,
the resulting upper bound is `x ^ (1/2)` times a small power of `x`.

The bracket is from Levent Alpöge's formalization of the Riemann hypothesis for Dirichlet
L-functions (`Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_size_bound`
in [`LipschitzWeightAndMinimum.lean`][alpoege-rh]).

[alpoege-rh]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/LipschitzWeightAndMinimum.lean
-/

public section

namespace TauCeti

open Real

/-- The normalized bracket, with the thick-set count cancelled from the term that contains it. -/
private theorem le_frobeniusErrorBracket_normalized {x C ε N P T m b a k Y : ℝ}
    (hmass : 0 < P * m * b * (T / N / 2))
    (h : P * m * b * (T / N / 2) * (Y - 4 * x ^ (1 / 2 + ε)) ≤
      x ^ (C * ε) * (P * a * (1 + m ^ 2 / k) +
        m * (2 * N * m * b * x ^ ε + T * k * b * x ^ (2 * ε) / N ^ 2)) +
      2 * P * m * b / x) :
    Y ≤ 4 * x ^ (1 / 2 + ε) +
      (2 * (N / T)) * (x ^ (C * ε) * (a / (m * b) + a * m / (k * b) +
        2 * (N / P) * m * x ^ ε) + 2 / x) +
      x ^ (C * ε) * (2 * (N / P) * (k / N ^ 2) * x ^ (2 * ε)) := by
  have hP : P ≠ 0 := by intro he; simp [he] at hmass
  have hm : m ≠ 0 := by intro he; simp [he] at hmass
  have hb : b ≠ 0 := by intro he; simp [he] at hmass
  have hT : T ≠ 0 := by intro he; simp [he] at hmass
  have hN : N ≠ 0 := by intro he; simp [he] at hmass
  have hY := (le_div_iff₀ hmass).2 (mul_comm (P * m * b * (T / N / 2)) _ ▸ h)
  calc
    Y = 4 * x ^ (1 / 2 + ε) + (Y - 4 * x ^ (1 / 2 + ε)) := by ring
    _ ≤ _ := add_le_add_right hY _
    _ = _ := by
      by_cases hk : k = 0 <;> (field_simp [hk, hN, hP, hT, hm, hb]; ring)

/-- Bounds on the first three terms of the Frobenius bracket after dividing by `P * m * b`. -/
private theorem frobeniusErrorBracket_core_le {x ε N P m b a k : ℝ}
    (hx : 1 ≤ x) (hb : 0 ≤ b)
    (hmlo : x ^ (1 / 2 - ε) ≤ m) (hmhi : m ≤ x ^ (1 / 2 + ε / 2))
    (hk : x * m ≤ k) (hP' : N / P ≤ 2 * x ^ (ε / 8)) (ha : a ≤ 2 * x * b) :
    a / (m * b) + a * m / (k * b) + 2 * (N / P) * m * x ^ ε ≤
      8 * x ^ (1 / 2 + 13 * ε / 8) := by
  have hx' : 0 < x := by positivity
  have hm : 0 < m := (rpow_pos_of_pos hx' _).trans_le hmlo
  have hk' : 0 < k := (mul_pos hx' hm).trans_le hk
  have hfirst : a / (m * b) ≤ 2 * x ^ (1 / 2 + ε) := by
    rcases eq_or_lt_of_le hb with rfl | hb'
    · simpa using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (rpow_nonneg hx'.le (1 / 2 + ε)))
    calc
      _ ≤ 2 * (x / m) := by
        apply (div_le_iff₀ (mul_pos hm hb')).2
        convert ha using 1
        field_simp [hm.ne']
      _ ≤ 2 * (x / x ^ (1 / 2 - ε)) := by gcongr
      _ = _ := by
        have he := rpow_sub hx' 1 (1 / 2 - ε)
        rw [rpow_one] at he
        rw [← he]
        ring_nf
  have hsecond : a * m / (k * b) ≤ 2 := by
    rcases eq_or_lt_of_le hb with rfl | hb'
    · norm_num
    apply (div_le_iff₀ (mul_pos hk' hb')).2
    calc
      a * m ≤ (2 * x * b) * m := mul_le_mul_of_nonneg_right ha hm.le
      _ = (2 * b) * (x * m) := by ring
      _ ≤ (2 * b) * k := by gcongr
      _ = 2 * (k * b) := by ring
  have hthird : 2 * (N / P) * m * x ^ ε ≤ 4 * x ^ (1 / 2 + 13 * ε / 8) := calc
    _ ≤ 2 * (2 * x ^ (ε / 8)) * x ^ (1 / 2 + ε / 2) * x ^ ε := by gcongr
    _ = 4 * (x ^ (ε / 8) * x ^ (1 / 2 + ε / 2) * x ^ ε) := by ring
    _ = _ := by rw [← rpow_add hx', ← rpow_add hx']; ring_nf
  rcases eq_or_lt_of_le hx with he | hxgt
  · simp only [← he, one_rpow] at hfirst hthird ⊢
    linarith
  · have hexp := (rpow_le_rpow_left_iff hxgt).1 (hmlo.trans hmhi)
    have hle : x ^ (1 / 2 + ε) ≤ x ^ (1 / 2 + 13 * ε / 8) :=
      rpow_le_rpow_of_exponent_le hx (by linarith)
    have hone : 1 ≤ x ^ (1 / 2 + 13 * ε / 8) := one_le_rpow hx (by linarith)
    linarith

/-- A lower bound `x ^ (-e) * N / c ≤ P` on a count is an upper bound `c * x ^ e` on the
reciprocal density `N / P`. -/
private theorem div_le_mul_rpow_of_rpow_neg_mul_div_le {x e c N P : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hP : 0 < P) (h : x ^ (-e) * N / c ≤ P) :
    N / P ≤ c * x ^ e := by
  rw [div_le_iff₀ hP]
  calc
    N = x ^ e * (x ^ (-e) * N) := by
      rw [← mul_assoc, ← rpow_add hx, add_neg_cancel, rpow_zero, one_mul]
    _ ≤ x ^ e * (P * c) := mul_le_mul_of_nonneg_left ((div_le_iff₀ hc).1 h) (by positivity)
    _ = c * x ^ e * P := by ring

/-- Absorb the costs of the normalized bracket into a single power of the scale. -/
private theorem frobeniusErrorBracket_absorb {x C ε Y D B F R : ℝ}
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hC : 0 ≤ C) (hD₀ : 0 ≤ D) (hD : D ≤ x ^ ε)
    (hB : B ≤ 8 * x ^ (1 / 2 + 13 * ε / 8)) (hF : F ≤ 4 * x ^ (1 / 2 + 13 * ε / 8))
    (hR : R ≤ x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8))
    (hY : Y ≤ 4 * x ^ (1 / 2 + ε) + 2 * D * (x ^ (C * ε) * B + R) + x ^ (C * ε) * F) :
    Y ≤ 26 * x ^ (1 / 2 + (C + 21 / 8) * ε) := by
  have hx' : 0 < x := by positivity
  have hpower : x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8) * x ^ ε =
      x ^ (1 / 2 + (C + 21 / 8) * ε) := by rw [← rpow_add hx', ← rpow_add hx']; ring_nf
  have hdom : x ^ (1 / 2 + ε) ≤ x ^ (1 / 2 + (C + 21 / 8) * ε) :=
    rpow_le_rpow_of_exponent_le hx (by nlinarith [mul_nonneg hC hε])
  have hle : x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8) ≤
      x ^ (1 / 2 + (C + 21 / 8) * ε) := by
    rw [← hpower]
    exact le_mul_of_one_le_right (by positivity) (one_le_rpow hx hε)
  calc
    Y ≤ 4 * x ^ (1 / 2 + ε) +
        (2 * x ^ ε) * (x ^ (C * ε) * (8 * x ^ (1 / 2 + 13 * ε / 8)) +
          x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8)) +
        x ^ (C * ε) * (4 * x ^ (1 / 2 + 13 * ε / 8)) := by
      refine hY.trans (add_le_add (add_le_add_right ?_ _) (by gcongr))
      -- Bound the signed inner sum before increasing its coefficient.
      exact (mul_le_mul_of_nonneg_left (add_le_add (by gcongr) hR) (by positivity)).trans
        (mul_le_mul_of_nonneg_right (by gcongr) (by positivity))
    _ ≤ _ := by linarith

/-- If `Y` satisfies the error bracket `h` of the averaged Frobenius inequality, then
`Y ≤ x ^ (1/2 + (C + 3) ε)`: a square-root bound in the scale `x`, up to a loss of
`x ^ ((C + 3) ε)`.

The bracket `h` bounds `Y - 4 x ^ (1/2 + ε)`, weighted by the main coefficient
`P * m * b * (T / N) / 2`, by the costs on its right-hand side, with `x ^ (C * ε)` the power of
the scale lost in those costs. Here `P` counts the tops, `T` counts the thick set and `N` is the
ambient group size; `hP` and `hT` bound their densities from below. The chain length `m` lies
near `x ^ (1/2)` (`hmlo`, `hmhi`), the auxiliary parameter `k` lies between `x * m` and
`N ^ 2 * x ^ (1/2 - ε)` (`hklo`, `hkhi`), and the scale term `a` is at most `2 * x * b` for its
positive normalizer `b` (`ha`). The largeness condition `hlarge` absorbs the numerical
constants into `x ^ (3 ε / 8)`. The theorem only uses these sizes, so no group structure or
integrality of the parameters is required. -/
theorem le_rpow_of_frobenius_error_bracket {x C ε N P T m b a k Y : ℝ}
    (hx : 1 ≤ x) (hlarge : 26 ≤ x ^ (3 * ε / 8)) (hC : 0 ≤ C)
    (hN : 0 < N) (hb : 0 < b)
    (hmlo : x ^ (1 / 2 - ε) ≤ m) (hmhi : m ≤ x ^ (1 / 2 + ε / 2))
    (hklo : x * m ≤ k) (hkhi : k ≤ N ^ 2 * x ^ (1 / 2 - ε))
    (hP : x ^ (-ε / 8) * N / 2 ≤ P) (hT : x ^ (-ε) * N ≤ T) (ha : a ≤ 2 * x * b)
    (h : P * m * b * (T / N / 2) * (Y - 4 * x ^ (1 / 2 + ε)) ≤
      x ^ (C * ε) * (P * a * (1 + m ^ 2 / k) +
        m * (2 * N * m * b * x ^ ε + T * k * b * x ^ (2 * ε) / N ^ 2)) +
      2 * P * m * b / x) :
    Y ≤ x ^ (1 / 2 + (C + 3) * ε) := by
  have hx' : 0 < x := by positivity
  have hε : 0 ≤ ε := by
    by_contra! hneg
    have hexp : 3 * ε / 8 ≤ 0 := by linarith
    have hle := rpow_le_rpow_of_exponent_le hx hexp
    rw [rpow_zero] at hle
    linarith
  have hp : 0 < P := (by positivity : 0 < x ^ (-ε / 8) * N / 2).trans_le hP
  have ht : 0 < T := (by positivity : 0 < x ^ (-ε) * N).trans_le hT
  have hm : 0 < m := (rpow_pos_of_pos hx' _).trans_le hmlo
  have hk : 0 < k := (mul_pos hx' hm).trans_le hklo
  have hP' : N / P ≤ 2 * x ^ (ε / 8) :=
    div_le_mul_rpow_of_rpow_neg_mul_div_le hx' two_pos hp (by rwa [← neg_div])
  have hT' : N / T ≤ x ^ ε := by
    simpa only [one_mul] using
      div_le_mul_rpow_of_rpow_neg_mul_div_le hx' one_pos ht (by rwa [div_one])
  have hcore := frobeniusErrorBracket_core_le hx hb.le hmlo hmhi hklo hP' ha
  have hkw : k / N ^ 2 ≤ x ^ (1 / 2 - ε) :=
    (div_le_iff₀ (sq_pos_of_pos hN)).2 (by rwa [mul_comm])
  have hfourth : 2 * (N / P) * (k / N ^ 2) * x ^ (2 * ε) ≤ 4 * x ^ (1 / 2 + 13 * ε / 8) := calc
    _ ≤ 2 * (2 * x ^ (ε / 8)) * x ^ (1 / 2 - ε) * x ^ (2 * ε) := by gcongr
    _ = 4 * (x ^ (ε / 8) * x ^ (1 / 2 - ε) * x ^ (2 * ε)) := by ring
    _ = 4 * x ^ (1 / 2 + 9 * ε / 8) := by rw [← rpow_add hx', ← rpow_add hx']; ring_nf
    _ ≤ _ := by gcongr; linarith
  have hsmall : 2 / x ≤ x ^ (C * ε) * x ^ (1 / 2 + 13 * ε / 8) := by
    have htwo := hlarge.trans (rpow_le_rpow_of_exponent_le hx (by linarith :
      3 * ε / 8 ≤ 1 / 2 + 13 * ε / 8))
    have hscale : 1 ≤ x ^ (C * ε) := one_le_rpow hx (mul_nonneg hC hε)
    calc
      2 / x ≤ 2 := div_le_self (by norm_num) hx
      _ ≤ 1 * x ^ (1 / 2 + 13 * ε / 8) := by linarith
      _ ≤ _ := by gcongr
  have hY := le_frobeniusErrorBracket_normalized (by positivity) h
  calc
    Y ≤ 26 * x ^ (1 / 2 + (C + 21 / 8) * ε) :=
      frobeniusErrorBracket_absorb hx hε hC (by positivity) hT' hcore hfourth hsmall hY
    _ ≤ x ^ (3 * ε / 8) * x ^ (1 / 2 + (C + 21 / 8) * ε) := by gcongr
    _ = _ := by rw [← rpow_add hx']; ring_nf

end TauCeti
