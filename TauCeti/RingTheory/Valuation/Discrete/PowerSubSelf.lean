/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Orders of `y ^ n - y` at a pole

For a discrete valuation and `n > 1`, a pole of `y` is a pole of `y ^ n - y` of order
multiplied by `n`. Conversely, `y ^ n - y` cannot have a pole unless `y` does. Thus an
element with negative order not divisible by `n` is not of the form `y ^ n - y`.

A prime-to-`n` pole is maximal among representatives `u - (w ^ n - w)`. In prime
characteristic, this also gives uniqueness of the reduced Artin–Schreier pole order.

The pole and maximality results need no characteristic hypothesis. In characteristic `p`,
with `n = p`, they give the local nontriviality criterion for an Artin–Schreier equation:
a pole of order prime to `p` rules out a root in the base field.
`TauCeti.ne_pow_sub_self_of_exists_reduced_artinSchreier_pole` applies this criterion
when a translated representative has such a pole.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.7.8.
-/

public section

open scoped WithZero

namespace Valuation

variable {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)

/-- At a pole, the power term dominates `y ^ n - y` when `n > 1`. -/
theorem ord_pow_sub_self_of_ord_neg {n : ℕ} (hn : 1 < n) {y : F}
    (hy : v.ord y < 0) : v.ord (y ^ n - y) = (n : ℤ) * v.ord y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hlt : (n : ℤ) * v.ord y < v.ord y := by
    have _ : (1 : ℤ) < n := by exact_mod_cast hn
    nlinarith
  rw [sub_eq_add_neg, ord_add_eq_min_of_ord_ne v (pow_ne_zero _ hy0) (neg_ne_zero.mpr hy0)
    (by rw [ord_pow, ord_neg]; omega), ord_pow, ord_neg, min_eq_left hlt.le]

/-- For `n > 1`, `y ^ n - y` has a pole exactly when `y` has a pole. -/
@[simp]
theorem ord_pow_sub_self_neg_iff {n : ℕ} (hn : 1 < n) (y : F) :
    v.ord (y ^ n - y) < 0 ↔ v.ord y < 0 := by
  constructor
  · intro h
    have hne : y ^ n - y ≠ 0 := by
      intro hzero
      simp [hzero] at h
    have hmin := v.min_ord_le_ord_add (by simpa [sub_eq_add_neg] using hne)
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
theorem ne_pow_sub_self_of_ord_neg_of_not_dvd {n : ℕ} (hn : 1 < n) {u : F}
    (hu : v.ord u < 0) (hdiv : ¬(n : ℤ) ∣ v.ord u) (y : F) : u ≠ y ^ n - y := by
  intro heq
  have hy : v.ord y < 0 := (v.ord_pow_sub_self_neg_iff hn y).mp (heq ▸ hu)
  apply hdiv
  rw [heq, v.ord_pow_sub_self_of_ord_neg hn hy]
  exact dvd_mul_right _ _

end Valuation

namespace TauCeti

variable {F : Type*} [Field F] {v : _root_.Valuation F ℤᵐ⁰}

/-- A supplied reduced Artin–Schreier pole makes the class of `u` nontrivial.
Only exponential characteristic `p > 1` is needed; no perfection or function-field
hypothesis is needed. -/
theorem ne_pow_sub_self_of_exists_reduced_artinSchreier_pole
    (p : ℕ) (hp : 1 < p) [ExpChar F p] {u : F}
    (hpole : ∃ w₀ : F, v.ord (u - (w₀ ^ p - w₀)) < 0 ∧
      ¬ (p : ℤ) ∣ v.ord (u - (w₀ ^ p - w₀))) :
    ∀ w : F, w ^ p - w ≠ u := by
  obtain ⟨w₀, hneg, hdiv⟩ := hpole
  intro w hw
  apply v.ne_pow_sub_self_of_ord_neg_of_not_dvd
    hp hneg hdiv (w - w₀)
  rw [← hw, sub_pow_expChar]
  ring

/-- A negative order not divisible by `n > 1` is maximal among all representatives
`u - (w ^ n - w)`. No perfection or characteristic hypothesis is needed for this
obstruction to improving a pole. -/
theorem ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd {n : ℕ} (hn : 1 < n) {u : F}
    (hu : v.ord u < 0) (hdiv : ¬(n : ℤ) ∣ v.ord u) (w : F) :
    v.ord (u - (w ^ n - w)) ≤ v.ord u := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rcases eq_or_ne (w ^ n - w) 0 with hw0 | hw0
  · simp [hw0]
  have hne : v.ord (w ^ n - w) ≠ v.ord u := by
    intro heq
    have hwneg : v.ord w < 0 :=
      (v.ord_pow_sub_self_neg_iff hn w).mp (heq ▸ hu)
    have horder : v.ord (w ^ n - w) = (n : ℤ) * v.ord w :=
      v.ord_pow_sub_self_of_ord_neg hn hwneg
    exact hdiv ⟨v.ord w, heq.symm.trans horder⟩
  rw [sub_eq_add_neg, v.ord_add_eq_min_of_ord_ne hu0 (neg_ne_zero.mpr hw0)
    (by simpa only [v.ord_neg] using hne.symm), v.ord_neg]
  exact min_le_left _ _

/-- Two representatives of an Artin–Schreier class with prime-to-`p` poles have the
same order. Thus the reduced pole order is independent of the substitution used to
obtain it. This uniqueness statement does not need a perfect residue field. -/
theorem ord_reduced_artinSchreier_representative_eq (p : ℕ) [Fact p.Prime] [CharP F p]
    {u w z : F} (hw : v.ord (u - (w ^ p - w)) < 0)
    (hwdiv : ¬(p : ℤ) ∣ v.ord (u - (w ^ p - w)))
    (hz : v.ord (u - (z ^ p - z)) < 0)
    (hzdiv : ¬(p : ℤ) ∣ v.ord (u - (z ^ p - z))) :
    v.ord (u - (w ^ p - w)) = v.ord (u - (z ^ p - z)) := by
  have heq (a b : F) : (u - (a ^ p - a)) - ((b - a) ^ p - (b - a)) =
      u - (b ^ p - b) := by
    rw [sub_pow_char]
    ring
  apply le_antisymm
  · simpa only [heq] using ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd
      (Fact.out : p.Prime).one_lt hz hzdiv (w - z)
  · simpa only [heq] using ord_sub_pow_sub_self_le_of_ord_neg_of_not_dvd
      (Fact.out : p.Prime).one_lt hw hwdiv (z - w)

end TauCeti
