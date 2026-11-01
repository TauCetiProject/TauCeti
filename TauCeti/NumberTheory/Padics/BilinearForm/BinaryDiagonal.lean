/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Binary diagonal forms with two scales over `ℤ_[2]`

Let `a`, `b` be units of `ℤ_[2]` and `k ≥ 1`. The diagonal form `⟨a, 2ᵏ b⟩` is the orthogonal sum
of two rank-one Jordan constituents of different scales, `⟨a⟩` of scale `1` and `⟨2ᵏ b⟩` of scale
`2ᵏ`. Over `ℤ_[2]` such a splitting is not unique, and the constituents are not isometry
invariants: unlike at odd primes, the two scales interact. This file classifies these forms
completely:

```text
⟨a, 2ᵏ b⟩ ≅ ⟨a', 2ᵏ b'⟩  ↔  a b a' b' is a square, and a' ≡ a or a' ≡ a + 2ᵏ b (mod 8).
```

The first condition compares the determinant square classes. The second says that `a'` is, up to
a unit square, a unit represented by `⟨a, 2ᵏ b⟩`: modulo `8` these are exactly `a` and `a + 2ᵏ b`.
Conversely the vectors `(1, 1)` and `(-2ᵏ b, a)` form an orthogonal basis exhibiting
`⟨a, 2ᵏ b⟩ ≅ ⟨a + 2ᵏ b, 2ᵏ a b (a + 2ᵏ b)⟩`
(`LinearMap.BilinForm.equivalent_toBilin'_diagonal_fin_two`), and a unit of `ℤ_[2]` is determined
up to squares by its residue modulo `8`.

The answer depends on the gap `k` between the scales:

* for `k = 1` both constituents may change, `⟨a, 2b⟩ ≅ ⟨a + 2b, 2ab(a + 2b)⟩`; in the language of
  Conway and Sloane's `2`-adic symbols, this either moves oddity from one constituent to the
  other, keeping both signs and the total oddity, or changes both signs and the total oddity
  by `4`;
* for `k = 2` the only change is **sign walking**, `⟨a, 4b⟩ ≅ ⟨5a, 20b⟩`, which multiplies both
  constituents by the nonsquare unit `5`;
* for `k ≥ 3` nothing changes: the constituents are invariants up to unit squares.

## Main results

* `TauCeti.equivalent_toBilin'_diagonal_two_pow_mul_iff`: the classification of `⟨a, 2ᵏ b⟩`.
* `TauCeti.equivalent_toBilin'_diagonal_four_mul_five_mul`: sign walking at distance `2`.
* `TauCeti.equivalent_toBilin'_diagonal_two_pow_mul_iff_of_three_le`: for `k ≥ 3` the two
  constituents are invariants.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Matrix (diagonal toBilin')
open PadicInt

namespace TauCeti

variable {a b a' b' : ℤ_[2]}

/-- If `a ≡ a'` modulo `8` and the determinants agree up to squares, then `⟨a, 2ᵏ b⟩` and
`⟨a', 2ᵏ b'⟩` have coefficients in the same unit square classes, hence are isometric. -/
private theorem equivalent_toBilin'_diagonal_two_pow_mul_of_eight_dvd (ha : IsUnit a)
    (hb : IsUnit b) (ha' : IsUnit a') (hb' : IsUnit b') (k : ℕ)
    (hsq : IsSquare (a * b * (a' * b'))) (h8 : (8 : ℤ_[2]) ∣ a' - a) :
    (toBilin' (diagonal ![a, 2 ^ k * b])).Equivalent
      (toBilin' (diagonal ![a', 2 ^ k * b'])) := by
  have hA := eight_dvd_sub_iff_toZModPow_three_eq.mp h8
  have hAB := (isSquare_mul_iff_toZModPow_three_eq (ha.mul hb) (ha'.mul hb')).mp hsq
  rw [map_mul, map_mul, ← hA] at hAB
  have hAu := isUnit_iff_toZModPow_three_mul_self.mp ha
  have hB : toZModPow 3 b = toZModPow 3 b' := by
    calc toZModPow 3 b = toZModPow 3 a * toZModPow 3 a * toZModPow 3 b := by rw [hAu, one_mul]
      _ = toZModPow 3 a * toZModPow 3 a * toZModPow 3 b' := by rw [mul_assoc, hAB, ← mul_assoc]
      _ = toZModPow 3 b' := by rw [hAu, one_mul]
  obtain ⟨s, hs, rfl⟩ := exists_eq_sq_mul_of_toZModPow_three_eq ha ha' hA
  obtain ⟨t, ht, rfl⟩ := exists_eq_sq_mul_of_toZModPow_three_eq hb hb' hB
  exact LinearMap.BilinForm.equivalent_toBilin'_diagonal_fin_two (x := s) (y := 0) (z := 0)
    (t := t) (by simpa using hs.mul ht) (by ring) (by ring) (by ring)

/-- **Binary diagonal forms with two scales over `ℤ_[2]`.** Let `a`, `b`, `a'`, `b'` be units of
`ℤ_[2]` and `k ≥ 1`. Then `⟨a, 2ᵏ b⟩` and `⟨a', 2ᵏ b'⟩` are isometric exactly when `a b a' b'` is a
square and `a'` is congruent to `a` or to `a + 2ᵏ b` modulo `8`. -/
theorem equivalent_toBilin'_diagonal_two_pow_mul_iff (ha : IsUnit a) (hb : IsUnit b)
    (ha' : IsUnit a') (hb' : IsUnit b') {k : ℕ} (hk : k ≠ 0) :
    (toBilin' (diagonal ![a, 2 ^ k * b])).Equivalent
        (toBilin' (diagonal ![a', 2 ^ k * b'])) ↔
      IsSquare (a * b * (a' * b')) ∧
        ((8 : ℤ_[2]) ∣ a' - a ∨ (8 : ℤ_[2]) ∣ a' - (a + 2 ^ k * b)) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hsq, h8⟩ ↦ ?_⟩
  · -- The Gram determinants `2ᵏ a b` and `2ᵏ a' b'` differ by the square of a unit.
    obtain ⟨u, hu⟩ := h.exists_det_eq_unit_sq_mul_det (Pi.basisFun ℤ_[2] (Fin 2))
      (Pi.basisFun ℤ_[2] (Fin 2))
    simp only [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
      Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hu
    have hab : a * b = u ^ 2 * (a' * b') :=
      mul_left_cancel₀ (pow_ne_zero k two_ne_zero) (by linear_combination hu)
    exact ⟨u * (a' * b'), by rw [hab]; ring⟩
  · -- The first basis vector of `⟨a', 2ᵏ b'⟩` pulls back to a vector of norm `a'`.
    obtain ⟨f⟩ := h
    have hv := f.symm.map_app (Pi.single 0 1) (Pi.single 0 1)
    set w := f.symm (Pi.single 0 1)
    simp only [Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_two,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Pi.single_eq_same, mul_one, one_mul, ne_eq, one_ne_zero, not_false_eq_true,
      Pi.single_eq_of_ne, mul_zero, add_zero] at hv
    exact eight_dvd_sub_or_eight_dvd_sub_add_of_eq (x := w 0) (y := w 1) hk ha'
      (by linear_combination hv)
  · rcases h8 with h8 | h8
    · exact equivalent_toBilin'_diagonal_two_pow_mul_of_eight_dvd ha hb ha' hb' k hsq h8
    -- Pass through `⟨a + 2ᵏ b, 2ᵏ a b (a + 2ᵏ b)⟩`, whose first coefficient is `a'` modulo `8`.
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
    have hu : IsUnit (a + 2 ^ (j + 1) * b) := by
      by_contra hu
      obtain ⟨w, hw⟩ := not_isUnit_iff_dvd.mp hu
      refine not_isUnit_iff_dvd.mpr ⟨w - 2 ^ j * b, ?_⟩ ha
      push_cast at hw ⊢
      linear_combination hw
    obtain ⟨r, hr⟩ := hsq
    refine (LinearMap.BilinForm.equivalent_toBilin'_diagonal_fin_two (a := a)
      (c := 2 ^ (j + 1) * b) (a' := a + 2 ^ (j + 1) * b)
      (c' := 2 ^ (j + 1) * (a * b * (a + 2 ^ (j + 1) * b))) (x := 1) (y := 1)
      (z := -(2 ^ (j + 1) * b)) (t := a) (by convert hu using 1; ring) (by ring) (by ring)
      (by ring)).trans ?_
    exact equivalent_toBilin'_diagonal_two_pow_mul_of_eight_dvd hu ((ha.mul hb).mul hu) ha' hb'
      (j + 1) ⟨(a + 2 ^ (j + 1) * b) * r, by linear_combination (a + 2 ^ (j + 1) * b) ^ 2 * hr⟩ h8

/-- **Sign walking.** For units `a`, `b` of `ℤ_[2]`, the forms `⟨a, 4b⟩` and `⟨5a, 20b⟩` are
isometric: multiplying both coefficients by the nonsquare unit `5` changes the sign of both
rank-one constituents and the oddity of each by `4`. -/
theorem equivalent_toBilin'_diagonal_four_mul_five_mul (ha : IsUnit a) (hb : IsUnit b) :
    (toBilin' (diagonal ![a, 4 * b])).Equivalent
      (toBilin' (diagonal ![5 * a, 4 * (5 * b)])) := by
  have h5 : IsUnit (5 : ℤ_[2]) := by
    rw [isUnit_iff_toZModPow_three_mul_self, map_ofNat]
    decide
  have key := (equivalent_toBilin'_diagonal_two_pow_mul_iff (k := 2) ha hb (h5.mul ha)
    (h5.mul hb) two_ne_zero).mpr ⟨⟨5 * a * b, by ring⟩, Or.inr ?_⟩
  · rwa [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num] at key
  -- `5a - (a + 4b) = 4 (a - b)` and `a - b` is even.
  rw [eight_dvd_sub_iff_toZModPow_three_eq, map_add, map_mul, map_mul, map_pow, map_ofNat,
    map_ofNat]
  have hA := isUnit_iff_toZModPow_three_mul_self.mp ha
  have hB := isUnit_iff_toZModPow_three_mul_self.mp hb
  generalize toZModPow 3 a = A at hA ⊢
  generalize toZModPow 3 b = B at hB ⊢
  revert A B
  decide

/-- **Far-apart scales do not interact.** For units `a`, `b`, `a'`, `b'` of `ℤ_[2]` and `k ≥ 3`,
the forms `⟨a, 2ᵏ b⟩` and `⟨a', 2ᵏ b'⟩` are isometric exactly when `a a'` and `b b'` are squares. -/
theorem equivalent_toBilin'_diagonal_two_pow_mul_iff_of_three_le (ha : IsUnit a) (hb : IsUnit b)
    (ha' : IsUnit a') (hb' : IsUnit b') {k : ℕ} (hk : 3 ≤ k) :
    (toBilin' (diagonal ![a, 2 ^ k * b])).Equivalent
        (toBilin' (diagonal ![a', 2 ^ k * b'])) ↔
      IsSquare (a * a') ∧ IsSquare (b * b') := by
  have h8 : (8 : ℤ_[2]) ∣ 2 ^ k * b :=
    dvd_mul_of_dvd_left ((show (8 : ℤ_[2]) = 2 ^ 3 by norm_num) ▸ pow_dvd_pow 2 hk) b
  have hor : (8 : ℤ_[2]) ∣ a' - a ∨ (8 : ℤ_[2]) ∣ a' - (a + 2 ^ k * b) ↔ (8 : ℤ_[2]) ∣ a' - a := by
    rw [show a' - (a + 2 ^ k * b) = a' - a - 2 ^ k * b by ring, dvd_sub_left h8, or_self]
  rw [equivalent_toBilin'_diagonal_two_pow_mul_iff ha hb ha' hb' (k := k) (by omega), hor,
    isSquare_mul_iff_toZModPow_three_eq (ha.mul hb) (ha'.mul hb'),
    isSquare_mul_iff_toZModPow_three_eq ha ha', isSquare_mul_iff_toZModPow_three_eq hb hb',
    eight_dvd_sub_iff_toZModPow_three_eq, map_mul, map_mul]
  have hA := isUnit_iff_toZModPow_three_mul_self.mp ha
  have hB := isUnit_iff_toZModPow_three_mul_self.mp hb
  generalize toZModPow 3 a = A at hA ⊢
  generalize toZModPow 3 b = B at hB ⊢
  generalize toZModPow 3 a' = A'
  generalize toZModPow 3 b' = B'
  revert A B A' B'
  decide

end TauCeti
