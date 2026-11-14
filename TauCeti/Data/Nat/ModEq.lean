/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Natural-number congruences

Two distinct residues `a, b < p` never differ by a multiple of `p`: if `b ≤ p * m + a`, so that
the natural subtraction does not truncate, the difference `p * m + a - b` is not divisible by `p`.
This is the arithmetic behind the uniqueness of the decomposition of an exponent as `p • μ + ν`
with `ν i < p`. Likewise, since `(p - 1) a ≡ -a` modulo `p`, two residues `a, b < p` with
`p ∣ (p - 1) a + b` are equal. Multiplication by a unit modulo `n` permutes the residues
`0, …, n - 1`, so a sum or product of `f (a * r % n)` over `r < n` equals that of `f r`.

## Main results

* `Nat.not_dvd_mul_add_sub`: for distinct `a, b < p` with `b ≤ p * m + a`, `p` does not divide
  `p * m + a - b`.
* `Nat.eq_of_dvd_sub_one_mul_add`: for residues `a, b < p`, `p ∣ (p - 1) * a + b` forces `b = a`.
* `Nat.Coprime.prod_range_mul_mod`, `Nat.Coprime.sum_range_mul_mod`: for `a` coprime to `n`,
  reindexing a product or sum over `range n` along `r ↦ a * r % n`.
* `TauCeti.sq_sub_one_eq_four_mul_of_mod_four_eq_three`: for `q ≡ 3 (mod 4)`, factor `q² - 1`
  with the factor `4` made explicit.
-/

public section

namespace Nat

/-- Two distinct residues modulo `p` do not differ by a multiple of `p`. -/
theorem not_dvd_mul_add_sub {p m a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b)
    (hle : b ≤ p * m + a) : ¬ p ∣ p * m + a - b := by
  intro h
  have h' : b ≡ p * m + a [MOD p] := (modEq_iff_dvd' hle).mpr h
  have h'' : b ≡ a [MOD p] := h'.trans (by simp [ModEq])
  exact hab (ModEq.eq_of_lt_of_lt h''.symm ha hb)

/-- Two residues `a, b < p` with `p ∣ (p - 1) * a + b` are equal, since `(p - 1) * a ≡ -a`
modulo `p`. -/
theorem eq_of_dvd_sub_one_mul_add {p a b : ℕ} (ha : a < p) (hb : b < p)
    (h : p ∣ (p - 1) * a + b) : b = a := by
  obtain ⟨q, hq⟩ := h
  have hab : p * a + b = p * q + a := by
    rw [← hq, add_right_comm, ← add_one_mul, Nat.sub_add_cancel (by omega)]
  have := congrArg (· % p) hab
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

open Finset in
/-- Multiplication by a unit modulo `n` permutes the residues `0, …, n - 1`: for `a` coprime to
`n`, the product of `f (a * r % n)` over `r < n` is the product of `f r`. -/
@[to_additive Coprime.sum_range_mul_mod
  /-- Multiplication by a unit modulo `n` permutes the residues `0, …, n - 1`: for `a` coprime
  to `n`, the sum of `f (a * r % n)` over `r < n` is the sum of `f r`. -/]
theorem Coprime.prod_range_mul_mod {M : Type*} [CommMonoid M] {a n : ℕ} (h : a.Coprime n)
    (f : ℕ → M) : ∏ r ∈ range n, f (a * r % n) = ∏ r ∈ range n, f r := by
  have hinj : Set.InjOn (fun r ↦ a * r % n) (range n) := fun x hx y hy hxy ↦
    (ModEq.cancel_left_of_coprime h.symm hxy).eq_of_lt_of_lt
      (mem_range.1 hx) (mem_range.1 hy)
  have himage : (range n).image (fun r ↦ a * r % n) = range n := by
    refine eq_of_subset_of_card_le (fun x hx ↦ ?_) (card_image_of_injOn hinj).ge
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (mod_lt _ (pos_of_ne_zero fun hn ↦ by simp [hn] at hr))
  conv_rhs => rw [← himage]
  exact (prod_image hinj).symm

end Nat

namespace TauCeti

/-- For `q ≡ 3 (mod 4)`, factor `q² - 1` with the factor `4` made explicit. -/
theorem sq_sub_one_eq_four_mul_of_mod_four_eq_three {q : ℕ} (hq : q % 4 = 3) :
    q ^ 2 - 1 = (4 * (q - 1)) * ((q + 1) / 4) := by
  rw [← Nat.one_pow 2, Nat.sq_sub_sq, Nat.one_pow]
  have h4 : 4 ∣ q + 1 := by omega
  calc
    (q + 1) * (q - 1) = (4 * ((q + 1) / 4)) * (q - 1) := by
      rw [Nat.mul_div_cancel' h4]
    _ = (4 * (q - 1)) * ((q + 1) / 4) := by ring

end TauCeti
