/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CharP.Lemmas
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Orders of `y ^ n - y` at a pole

For a discrete valuation and `n > 1`, a pole of `y` is a pole of `y ^ n - y` of order
multiplied by `n`. Conversely, `y ^ n - y` cannot have a pole unless `y` does. Thus an
element with negative order not divisible by `n` is not of the form `y ^ n - y`.

More generally, if no `n`-th power `y ^ n` agrees with `u` beyond the leading order of `u`,
then `TauCeti.ord_sub_pow_sub_self_eq_min` computes the order of every representative
`u - (w ^ n - w)` as `min (ord u) (n * ord w)`. Such a substitution can only create a deeper pole.
The hypothesis holds automatically when `n` does not divide the order of `u`, so a prime-to-`n`
pole is maximal among representatives. In prime characteristic, this also gives uniqueness of
the reduced Artin–Schreier pole order. When `n` does divide the negative order of `u`,
`TauCeti.ord_sub_pow_sub_self_neg_and_dvd` shows that every representative keeps a pole of order
divisible by `n`. This is the obstruction to reducing Artin–Schreier representatives over an
imperfect residue field.

The pole and maximality results need no characteristic hypothesis. In characteristic `p`,
with `n = p`, they give the local nontriviality criterion for an Artin–Schreier equation:
a pole of order prime to `p` rules out a root in the base field.
`TauCeti.ne_pow_sub_self_of_exists_reduced_artinSchreier_pole` applies this criterion
when a translated representative has such a pole.

The order computations hold for a `ℤᵐ⁰`-valued valuation on any ring; only the two
Artin–Schreier statements, which expand `(a - b) ^ p`, assume commutativity. The order has
its junk value zero on the valuation support.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open scoped WithZero

namespace Valuation

variable {R : Type*} [Ring R] (v : Valuation R ℤᵐ⁰)

/-- At a pole, the power term dominates `y ^ n - y` when `n > 1`. -/
theorem ord_pow_sub_self_of_ord_neg {n : ℕ} (hn : 1 < n) {y : R}
    (hy : v.ord y < 0) : v.ord (y ^ n - y) = (n : ℤ) * v.ord y := by
  have hy0 : v y ≠ 0 := v.valuation_ne_zero_of_ord_ne_zero hy.ne
  have hlt : (n : ℤ) * v.ord y < v.ord y := by
    have _ : (1 : ℤ) < n := by exact_mod_cast hn
    nlinarith
  rw [sub_eq_add_neg, ord_add_eq_min_of_ord_ne v (by rw [map_pow]; exact pow_ne_zero _ hy0)
    (by rwa [v.map_neg]) (by rw [ord_pow, ord_neg]; omega), ord_pow, ord_neg,
    min_eq_left hlt.le]

/-- For `n > 1`, `y ^ n - y` has a pole exactly when `y` has a pole. -/
@[simp]
theorem ord_pow_sub_self_neg_iff {n : ℕ} (hn : 1 < n) (y : R) :
    v.ord (y ^ n - y) < 0 ↔ v.ord y < 0 := by
  constructor
  · intro h
    have hne : v (y ^ n - y) ≠ 0 := v.valuation_ne_zero_of_ord_ne_zero h.ne
    have hmin := v.min_ord_le_ord_add (by rwa [← sub_eq_add_neg])
    rw [ord_pow, ord_neg, ← sub_eq_add_neg] at hmin
    by_contra hy
    have hnonneg : 0 ≤ v.ord y := by omega
    have hpow : 0 ≤ (n : ℤ) * v.ord y := mul_nonneg (Int.natCast_nonneg n) hnonneg
    have := le_min hpow hnonneg
    linarith
  · intro hy
    rw [v.ord_pow_sub_self_of_ord_neg hn hy]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast (by omega : 0 < n)) hy

/-- A pole whose order is not divisible by `n` cannot be a value of `y ↦ y ^ n - y`.
For prime `n` in characteristic `n`, this proves nontriviality of the Artin–Schreier class. -/
theorem ne_pow_sub_self_of_ord_neg_of_not_dvd {n : ℕ} (hn : 1 < n) {u : R}
    (hu : v.ord u < 0) (hdiv : ¬(n : ℤ) ∣ v.ord u) (y : R) : u ≠ y ^ n - y := by
  intro heq
  have hy : v.ord y < 0 := (v.ord_pow_sub_self_neg_iff hn y).mp (heq ▸ hu)
  apply hdiv
  rw [heq, v.ord_pow_sub_self_of_ord_neg hn hy]
  exact dvd_mul_right _ _

end Valuation

namespace TauCeti

section Ring

variable {R : Type*} [Ring R] {v : _root_.Valuation R ℤᵐ⁰}

/-- If `n` does not divide the order of `u`, then no `n`-th power agrees with `u` beyond the
leading order of `u`. -/
theorem ord_sub_pow_le_of_not_dvd {n : ℕ} {u : R} (hdiv : ¬(n : ℤ) ∣ v.ord u) (y : R) :
    v.ord (u - y ^ n) ≤ v.ord u := by
  have hu0 : v u ≠ 0 := v.valuation_ne_zero_of_ord_ne_zero (by
    intro h
    simp [h] at hdiv)
  rcases eq_or_ne (v (y ^ n)) 0 with hy | hy
  · rw [v.ord_sub_of_map_right_eq_zero hy]
  rw [sub_eq_add_neg, v.ord_add_eq_min_of_ord_ne hu0 (by rwa [v.map_neg])
    (by rw [v.ord_neg, v.ord_pow]; exact fun h ↦ hdiv ⟨v.ord y, h⟩)]
  exact min_le_left _ _

/-- Let `u` have a pole, and suppose that `w ^ n` does not agree with `u` beyond the
leading order of `u`. Then for `n > 1` the representative `u - (w ^ n - w)` has order
`min (ord u) (n * ord w)`. This substitution cannot cancel the pole of `u`; it can only replace
it by the deeper pole of `w ^ n`. No characteristic hypothesis is needed. -/
theorem ord_sub_pow_sub_self_eq_min {n : ℕ} (hn : 1 < n) {u : R} (hu : v.ord u < 0)
    (w : R) (hroot : v.ord (u - w ^ n) ≤ v.ord u) :
    v.ord (u - (w ^ n - w)) = min (v.ord u) (n * v.ord w) := by
  have hu0 : v u ≠ 0 := v.valuation_ne_zero_of_ord_ne_zero hu.ne
  rcases eq_or_ne (v w) 0 with hw0 | hw0
  · have hsub : v (w ^ n - w) = 0 := by
      rw [v.map_sub_of_right_eq_zero hw0, map_pow, hw0, zero_pow (by omega)]
    rw [v.ord_eq_zero_of_map_eq_zero hw0, mul_zero, min_eq_left hu.le,
      v.ord_sub_of_map_right_eq_zero hsub]
  have hwn : v (w ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hw0
  have ha0 : v (u - w ^ n) ≠ 0 :=
    v.valuation_ne_zero_of_ord_ne_zero (hroot.trans_lt hu).ne
  -- The power term: `u - w ^ n` has order `min (ord u) (n * ord w)`.
  have ha : v.ord (u - w ^ n) = min (v.ord u) (n * v.ord w) := by
    rcases lt_or_ge ((n : ℤ) * v.ord w) (v.ord u) with hlt | hge
    · rw [sub_eq_add_neg, v.ord_add_eq_min_of_ord_ne hu0 (by rwa [v.map_neg])
        (by rw [v.ord_neg, v.ord_pow]; omega), v.ord_neg, v.ord_pow]
    · have hmin := v.min_ord_le_ord_add (f := u) (g := -w ^ n)
        (by rwa [← sub_eq_add_neg])
      rw [v.ord_neg, v.ord_pow, ← sub_eq_add_neg, min_eq_left hge] at hmin
      rw [min_eq_left hge]
      exact le_antisymm hroot hmin
  -- The linear term `w` has strictly larger order, so it does not change the order.
  have hlt : min (v.ord u) (n * v.ord w) < v.ord w := by
    rcases lt_or_ge (v.ord w) 0 with hneg | hnonneg
    · have : (1 : ℤ) < n := by exact_mod_cast hn
      exact (min_le_right _ _).trans_lt (by nlinarith)
    · exact (min_le_left _ _).trans_lt (hu.trans_le hnonneg)
  -- Expose the additive regrouping so abel can normalize it in a noncommutative ring.
  rw [show u - (w ^ n - w) = (u - w ^ n) + w by abel,
    v.ord_add_eq_min_of_ord_ne ha0 hw0 (by rw [ha]; exact hlt.ne), ha, min_eq_left hlt.le]

/-- A negative order not divisible by `n > 1` is maximal among all representatives
`u - (w ^ n - w)`. No perfection or characteristic hypothesis is needed for this
obstruction to improving a pole. -/
theorem ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd {n : ℕ} (hn : 1 < n) {u : R}
    (hu : v.ord u < 0) (hdiv : ¬(n : ℤ) ∣ v.ord u) (w : R) :
    v.ord (u - (w ^ n - w)) ≤ v.ord u :=
  (ord_sub_pow_sub_self_eq_min hn hu w (ord_sub_pow_le_of_not_dvd hdiv w)).trans_le
    (min_le_left _ _)

/-- Let `n > 1` divide the negative order of `u`, and suppose that `w ^ n` does not agree
with `u` beyond the leading order of `u`. Then the representative `u - (w ^ n - w)` has a pole
whose order is divisible by `n`: this substitution neither makes `u` integral nor produces a
pole of order prime to `n`. -/
theorem ord_sub_pow_sub_self_neg_and_dvd {n : ℕ} (hn : 1 < n) {u : R} (hu : v.ord u < 0)
    (hdvd : (n : ℤ) ∣ v.ord u) (w : R) (hroot : v.ord (u - w ^ n) ≤ v.ord u) :
    v.ord (u - (w ^ n - w)) < 0 ∧ (n : ℤ) ∣ v.ord (u - (w ^ n - w)) := by
  rw [ord_sub_pow_sub_self_eq_min hn hu w hroot]
  refine ⟨(min_le_left _ _).trans_lt hu, ?_⟩
  rcases min_choice (v.ord u) (n * v.ord w) with h | h <;> rw [h]
  · exact hdvd
  · exact dvd_mul_right _ _

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : _root_.Valuation R ℤᵐ⁰}

/-- A supplied reduced Artin–Schreier pole makes the class of `u` nontrivial.
Only exponential characteristic `p` is needed; the pole hypothesis forces `p > 1`.
No perfection or function-field hypothesis is needed. -/
theorem ne_pow_sub_self_of_exists_reduced_artinSchreier_pole
    (p : ℕ) [ExpChar R p] {u : R}
    (hpole : ∃ w₀ : R, v.ord (u - (w₀ ^ p - w₀)) < 0 ∧
      ¬ (p : ℤ) ∣ v.ord (u - (w₀ ^ p - w₀))) :
    ∀ w : R, w ^ p - w ≠ u := by
  obtain ⟨w₀, hneg, hdiv⟩ := hpole
  have hp := one_lt_expChar_of_not_dvd R hdiv
  intro w hw
  apply v.ne_pow_sub_self_of_ord_neg_of_not_dvd
    hp hneg hdiv (w - w₀)
  rw [← hw, sub_pow_expChar]
  ring

/-- Two representatives of an Artin–Schreier class with prime-to-`p` poles have the
same order. Thus the reduced pole order is independent of the substitution used to
obtain it. Only exponential characteristic `p` is needed; the pole hypothesis forces `p > 1`.
No perfect residue field hypothesis is needed. -/
theorem ord_reduced_artinSchreier_representative_eq (p : ℕ) [ExpChar R p]
    {u w z : R} (hw : v.ord (u - (w ^ p - w)) < 0)
    (hwdiv : ¬(p : ℤ) ∣ v.ord (u - (w ^ p - w)))
    (hz : v.ord (u - (z ^ p - z)) < 0)
    (hzdiv : ¬(p : ℤ) ∣ v.ord (u - (z ^ p - z))) :
    v.ord (u - (w ^ p - w)) = v.ord (u - (z ^ p - z)) := by
  have hp := one_lt_expChar_of_not_dvd R hwdiv
  have heq (a b : R) : (u - (a ^ p - a)) - ((b - a) ^ p - (b - a)) =
      u - (b ^ p - b) := by
    rw [sub_pow_expChar]
    ring
  apply le_antisymm
  · simpa only [heq] using ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd
      hp hz hzdiv (w - z)
  · simpa only [heq] using ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd
      hp hw hwdiv (z - w)

end CommRing

end TauCeti
