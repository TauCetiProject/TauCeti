/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.NNReal.Defs
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The exponent arithmetic for iterating the Sobolev embedding

In dimension `n`, the Sobolev embedding `W^{1,p} ⊂ L^s` holds for `p ≤ s` with
`1/p - 1/s ≤ 1/n`. Applied to the weak derivatives, it lowers the derivative order by one while
raising the integrability exponent from `p` to `s`. This file records the exponent arithmetic of
one step of the resulting iteration towards Morrey's condition: if `p ≤ n` and `(k + 1) p > n`,
some admissible `s` satisfies `k s > n`. For `p < n` the critical exponent `1/s = 1/p - 1/n` is
such a witness, and for `p = n` so is `2 n`. This is the exponent arithmetic only, not an
embedding theorem.

The same arithmetic is also recorded for exponents in `ℝ≥0∞`, the form used by the Sobolev
embeddings of exact exponent `1/q + r/n = 1/p` for Sobolev sections of vector bundles, which
require `q < ∞`:

* for `1 < p ≤ n` and `(k + 1) p > n`, after lowering `p` to some `p₀ < n` if `p = n`, the critical
  exponent `1/q = 1/p₀ - 1/n` is finite, larger than `1`, and satisfies `k q > n`;
* for `r p < n < (r + 1) p` with `r ≥ 1`, the exponent `1/q = 1/p - r/n` is finite and larger
  than `n`, and the Morrey exponents agree: `1 - n/q = (r + 1) - n/p`;
* at an integer margin `(k - 1) p = n` with `n ≥ 1`, every `0 < β < 1` is the Morrey exponent
  `k - n/p₀` of an exponent `1 < p₀ ≤ p` with `(k - 1) p₀ < n < k p₀`, namely `p₀ = n / (k - β)`.

## Main declarations

* `TauCeti.exists_le_and_inv_sub_inv_le_and_lt_mul`: one step of the exponent iteration.
* `TauCeti.exists_ne_top_and_inv_add_inv_eq_and_lt_mul`,
  `TauCeti.exists_le_and_ne_top_and_inv_add_inv_eq_and_lt_mul`: one step of the iteration with
  the critical exponent, in `ℝ≥0∞`.
* `TauCeti.exists_inv_add_mul_inv_eq_and_lt_and_sub_div_eq`: `r` steps at once, with the Morrey
  exponent.
* `TauCeti.exists_mul_lt_and_lt_mul_and_sub_div_eq`: every exponent below `1` at an integer
  margin.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

/-- One step of the exponent iteration for Morrey's condition `kp > n`: if `p ≤ n` and
`(k + 1) p > n`, there is an exponent `s` admissible for the Sobolev embedding `W^{1,p} ⊂ L^s` in
dimension `n`, that is `p ≤ s` and `1/p - 1/s ≤ 1/n`, with `k s > n`. -/
theorem exists_le_and_inv_sub_inv_le_and_lt_mul {k : ℕ} {p n : ℝ≥0} (hpn : p ≤ n)
    (hkp : n < ((k + 1 : ℕ) : ℝ≥0) * p) :
    ∃ s : ℝ≥0, p ≤ s ∧ (p : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ ∧ n < (k : ℝ≥0) * s := by
  have hkp' : (n : ℝ) < ((k : ℝ) + 1) * p := by exact_mod_cast hkp
  have hpn' : (p : ℝ) ≤ n := hpn
  have hp0 : (0 : ℝ) < p :=
    pos_of_mul_pos_right ((NNReal.coe_nonneg n).trans_lt hkp') (by positivity)
  have hn0 : (0 : ℝ) < n := hp0.trans_le hpn'
  rcases hpn.lt_or_eq with hlt | rfl
  · have hlt' : (p : ℝ) < n := hlt
    have ha : 0 < (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := sub_pos.2 (inv_strictAnti₀ hp0 hlt')
    obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, (s : ℝ) = ((p : ℝ)⁻¹ - (n : ℝ)⁻¹)⁻¹ :=
      ⟨⟨_, (inv_pos.2 ha).le⟩, rfl⟩
    have hs0 : (0 : ℝ) < s := hs ▸ inv_pos.2 ha
    have hsa : (s : ℝ)⁻¹ = (p : ℝ)⁻¹ - (n : ℝ)⁻¹ := by rw [hs, inv_inv]
    have hn' : 0 < (n : ℝ)⁻¹ := inv_pos.2 hn0
    refine ⟨s, ?_, by linarith, ?_⟩
    · rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hs0 hp0]
      linarith
    · have h1 : (n : ℝ) / p < k + 1 := (div_lt_iff₀ hp0).2 hkp'
      have h2 : (n : ℝ) / s < k := by
        have : (n : ℝ) / s = n / p - 1 := by rw [div_eq_mul_inv, hsa]; field_simp
        linarith
      rw [← NNReal.coe_lt_coe]
      push_cast
      exact (div_lt_iff₀ hs0).1 h2
  · have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hkp'
      · exact hk
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    refine ⟨2 * p, by rw [two_mul]; exact le_self_add, ?_, ?_⟩
    · have : 0 < (p : ℝ)⁻¹ := inv_pos.2 hp0
      push_cast
      rw [mul_inv]
      linarith
    · rw [← NNReal.coe_lt_coe]
      push_cast
      nlinarith

/-! ### Exponents in `ℝ≥0∞` -/

/-- The exponent `q = p n / (n - r p)` satisfies `1/q + r/n = 1/p` in `ℝ≥0∞`. -/
private theorem inv_add_mul_inv_eq_of_eq_div {n r : ℕ} {p q : ℝ≥0} (hp : 0 < p)
    (hrp : (r : ℝ) * p < n) (hq : (q : ℝ) = p * n / (n - r * p)) :
    (q : ℝ≥0∞)⁻¹ + r * (n : ℝ≥0∞)⁻¹ = (p : ℝ≥0∞)⁻¹ := by
  have hN0 : (0 : ℝ) < n := (by positivity : (0 : ℝ) ≤ r * p).trans_lt hrp
  have hq0 : q ≠ 0 := by rw [← NNReal.coe_ne_zero, hq]; positivity
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hN0.ne'
  rw [← ENNReal.coe_natCast n, ← ENNReal.coe_inv hq0, ← ENNReal.coe_inv hp.ne',
    ← ENNReal.coe_inv hn0]
  norm_cast
  ext
  push_cast
  rw [hq]
  field_simp
  ring

/-- Moves the Morrey exponent `a - n/q` of a positive exponent `q` from `ℝ≥0∞` to `ℝ`. -/
private theorem natCast_sub_div_eq_ofReal {a n : ℕ} {q : ℝ≥0} (hq : 0 < q) :
    (a : ℝ≥0∞) - n / q = ENNReal.ofReal (a - n / q) := by
  rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_div_of_pos (by exact_mod_cast hq), ENNReal.ofReal_natCast,
    ENNReal.ofReal_coe_nnreal]

/-- One step of the exponent iteration for Morrey's condition with the critical exponent: if
`1 ≤ p < n` and `(k + 1) p > n`, the Sobolev conjugate `q` of `p` in dimension `n`,
`1/q + 1/n = 1/p`, is finite, larger than `1` and satisfies `k q > n`. -/
theorem exists_ne_top_and_inv_add_inv_eq_and_lt_mul {n k : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hpn : p < n) (hkp : (n : ℝ≥0∞) < (k + 1 : ℕ) * p) :
    ∃ q : ℝ≥0∞, q ≠ ⊤ ∧ q⁻¹ + (n : ℝ≥0∞)⁻¹ = p⁻¹ ∧ 1 < q ∧ (n : ℝ≥0∞) < k * q := by
  lift p to ℝ≥0 using (hpn.trans (ENNReal.natCast_lt_top n)).ne
  have hP1 : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hPN : (p : ℝ) < n := by exact_mod_cast hpn
  have hkP : (n : ℝ) < (k + 1) * p := by exact_mod_cast hkp
  have hP0 : (0 : ℝ) < p := zero_lt_one.trans_le hP1
  have hNP : (0 : ℝ) < n - p := sub_pos.2 hPN
  -- The conjugate exponent is `q = p n / (n - p)`.
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = p * n / (n - p) := ⟨⟨_, by positivity⟩, rfl⟩
  refine ⟨q, ENNReal.coe_ne_top, ?_, ?_, ?_⟩
  · simpa using inv_add_mul_inv_eq_of_eq_div (r := 1) (by exact_mod_cast hP0)
      (by rwa [Nat.cast_one, one_mul]) (by rwa [Nat.cast_one, one_mul])
  · exact_mod_cast show (1 : ℝ) < q by rw [hq, lt_div_iff₀ hNP]; nlinarith
  · exact_mod_cast show (n : ℝ) < k * q by rw [hq, mul_div_assoc', lt_div_iff₀ hNP]; nlinarith

/-- One step of the exponent iteration for Morrey's condition, allowing `p = n`: if `1 < p ≤ n` and
`(k + 1) p > n`, there are an exponent `1 ≤ p₀ ≤ p` and its finite Sobolev conjugate `q` in
dimension `n`, `1/q + 1/n = 1/p₀`, with `1 < q` and `k q > n`. For `p < n` take `p₀ = p`; for
`p = n` take `p₀ = 3 n / 4`. -/
theorem exists_le_and_ne_top_and_inv_add_inv_eq_and_lt_mul {n k : ℕ} {p : ℝ≥0∞} (hp1 : 1 < p)
    (hpn : p ≤ n) (hkp : (n : ℝ≥0∞) < (k + 1 : ℕ) * p) :
    ∃ p₀ q : ℝ≥0∞, 1 ≤ p₀ ∧ p₀ ≤ p ∧ q ≠ ⊤ ∧ q⁻¹ + (n : ℝ≥0∞)⁻¹ = p₀⁻¹ ∧ 1 < q ∧
      (n : ℝ≥0∞) < k * q := by
  rcases hpn.lt_or_eq with hlt | rfl
  · obtain ⟨q, hq⟩ := exists_ne_top_and_inv_add_inv_eq_and_lt_mul hp1.le hlt hkp
    exact ⟨p, q, hp1.le, le_rfl, hq⟩
  have hN1 : (2 : ℝ) ≤ n := by exact_mod_cast (by exact_mod_cast hp1 : 1 < n)
  have hkN : (n : ℝ) < (k + 1) * n := by exact_mod_cast hkp
  have hk : (1 : ℝ) ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.cast_zero, zero_add, one_mul, lt_self_iff_false] at hkN
    · exact_mod_cast hk
  -- Lower `p = n` to `p₀ = 3 n / 4`.
  have h1 : (1 : ℝ≥0∞) ≤ (3 * n / 4 : ℝ≥0) := by
    have : (1 : ℝ) ≤ 3 * n / 4 := by linarith
    exact_mod_cast this
  have h2 : ((3 * n / 4 : ℝ≥0) : ℝ≥0∞) < n := by
    have : (3 * n / 4 : ℝ) < n := by linarith
    exact_mod_cast this
  have h3 : (n : ℝ≥0∞) < (k + 1 : ℕ) * (3 * n / 4 : ℝ≥0) := by
    have : (n : ℝ) < (k + 1 : ℕ) * (3 * n / 4) := by push_cast; nlinarith
    exact_mod_cast this
  obtain ⟨q, hq⟩ := exists_ne_top_and_inv_add_inv_eq_and_lt_mul h1 h2 h3
  exact ⟨_, q, h1, h2.le, hq⟩

/-- The exponent arithmetic of `r` steps of the Sobolev embedding in dimension `n` at once: if
`r ≥ 1` and `r p < n < (r + 1) p`, the exponent `q` with `1/q + r/n = 1/p` is finite and larger
than `n`, and the Morrey exponent `1 - n/q` of `W^{1,q}` is the Morrey exponent `(r + 1) - n/p` of
`W^{r+1,p}`. -/
theorem exists_inv_add_mul_inv_eq_and_lt_and_sub_div_eq {n r : ℕ} {p : ℝ≥0∞} (hr : r ≠ 0)
    (hrp : (r : ℝ≥0∞) * p < n) (hnp : (n : ℝ≥0∞) < (r + 1 : ℕ) * p) :
    ∃ q : ℝ≥0∞, q ≠ ⊤ ∧ q⁻¹ + r * (n : ℝ≥0∞)⁻¹ = p⁻¹ ∧ (n : ℝ≥0∞) < q ∧
      (1 : ℝ≥0∞) - n / q = (r + 1 : ℕ) - n / p := by
  have hr1 : (1 : ℝ≥0∞) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
  lift p to ℝ≥0 using ne_top_of_le_ne_top (hrp.trans (ENNReal.natCast_lt_top n)).ne
    (by simpa using mul_le_mul_left hr1 p)
  have hrP : (r : ℝ) * p < n := by exact_mod_cast hrp
  have hnP : (n : ℝ) < (r + 1) * p := by exact_mod_cast hnp
  have hr0 : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hr
  have hP0 : (0 : ℝ) < p := by
    refine p.coe_nonneg.lt_of_ne fun h ↦ ?_
    rw [← h, mul_zero] at hnP
    exact (Nat.cast_nonneg n).not_gt hnP
  have hN0 : (0 : ℝ) < n := by nlinarith
  have hD : (0 : ℝ) < n - r * p := sub_pos.2 hrP
  -- The exponent is `q = p n / (n - r p)`.
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0, (q : ℝ) = p * n / (n - r * p) := ⟨⟨_, by positivity⟩, rfl⟩
  have hq0 : (0 : ℝ) < q := by rw [hq]; positivity
  refine ⟨q, ENNReal.coe_ne_top, inv_add_mul_inv_eq_of_eq_div (by exact_mod_cast hP0) hrP hq,
    ?_, ?_⟩
  · exact_mod_cast show (n : ℝ) < q by rw [hq, lt_div_iff₀ hD]; nlinarith
  · rw [← Nat.cast_one, natCast_sub_div_eq_ofReal (by exact_mod_cast hq0),
      natCast_sub_div_eq_ofReal (by exact_mod_cast hP0)]
    congr 1
    rw [hq]
    field_simp
    push_cast
    ring

/-- **Exponents below `1` at an integer margin.** If `(k - 1) p = n` with `n ≥ 1` and `1 < p`, so
that the Morrey exponent `k - n/p` of `W^{k,p}` in dimension `n` is the integer `1`, then every
`0 < β < 1` is the Morrey exponent `k - n/p₀` of some exponent `1 < p₀ ≤ p` with
`(k - 1) p₀ < n < k p₀`, namely `p₀ = n / (k - β)`. -/
theorem exists_mul_lt_and_lt_mul_and_sub_div_eq {n k : ℕ} {p : ℝ≥0∞} {β : ℝ≥0} (hn : n ≠ 0)
    (hp1 : 1 < p) (hkp : ((k - 1 : ℕ) : ℝ≥0∞) * p = n) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ p₀ : ℝ≥0∞, 1 < p₀ ∧ p₀ ≤ p ∧ ((k - 1 : ℕ) : ℝ≥0∞) * p₀ < n ∧ (n : ℝ≥0∞) < k * p₀ ∧
      (k : ℝ≥0∞) - n / p₀ = β := by
  have hk1 : k - 1 ≠ 0 := by
    rintro h
    rw [h, Nat.cast_zero, zero_mul] at hkp
    exact hn (by exact_mod_cast hkp.symm)
  lift p to ℝ≥0 using fun hp ↦ by
    rw [hp, ENNReal.mul_top (by exact_mod_cast hk1)] at hkp
    exact ENNReal.natCast_ne_top n hkp.symm
  have hkR : ((k - 1 : ℕ) : ℝ) = k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hkP : ((k : ℝ) - 1) * p = n := by
    have h := congrArg ((↑) : ℝ≥0 → ℝ) (by exact_mod_cast hkp : ((k - 1 : ℕ) : ℝ≥0) * p = n)
    rw [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast] at h
    rwa [← hkR]
  have hP1 : (1 : ℝ) < p := by exact_mod_cast hp1
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
  have hβ0' : (0 : ℝ) < β := hβ0
  have hβ1' : (β : ℝ) < 1 := hβ1
  -- The integer `n = (k - 1) p` exceeds `k - 1`, so `n ≥ k`.
  have hkn : (k : ℝ) ≤ n := by
    have h : (k - 1 : ℕ) < n := by
      have : ((k : ℝ) - 1) < n := by rw [← hkP]; nlinarith
      exact_mod_cast hkR ▸ this
    exact_mod_cast (by omega : k ≤ n)
  have hD : (0 : ℝ) < k - β := by linarith
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ≥0, (p₀ : ℝ) = n / (k - β) := ⟨⟨_, by positivity⟩, rfl⟩
  have hp₀0 : (0 : ℝ) < p₀ := by rw [hp₀]; positivity
  refine ⟨p₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast show (1 : ℝ) < p₀ by rw [hp₀, lt_div_iff₀ hD]; linarith
  · exact_mod_cast show (p₀ : ℝ) ≤ p by rw [hp₀, div_le_iff₀ hD]; nlinarith
  · exact_mod_cast show ((k - 1 : ℕ) : ℝ) * p₀ < n by
      rw [hkR, hp₀, mul_div_assoc', div_lt_iff₀ hD]; nlinarith
  · exact_mod_cast show (n : ℝ) < k * p₀ by rw [hp₀, mul_div_assoc', lt_div_iff₀ hD]; nlinarith
  · rw [natCast_sub_div_eq_ofReal (by exact_mod_cast hp₀0), ← ENNReal.ofReal_coe_nnreal]
    congr 1
    rw [hp₀]
    field_simp
    ring

end TauCeti
