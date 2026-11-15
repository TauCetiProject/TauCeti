/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.Operations
public import TauCeti.RingTheory.Nilpotent.Exp.Ideal
public import TauCeti.RingTheory.Nilpotent.Log
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# The Baker–Campbell–Hausdorff formula through degree three

For elements `x` and `y` of a left ideal `I` of an associative `ℚ`-algebra whose fourth power
vanishes, the finite logarithm of the product `exp x * exp y` is exactly the usual
Baker–Campbell–Hausdorff polynomial through degree three:
`x + y + ½⁅x, y⁆ + 1/12 (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)`, where `⁅a, b⁆ = a * b - b * a`
(`Ideal.log_exp_mul_exp_of_pow_four_eq_bot`). Every word of length at least four in `x` and `y`
vanishes, so no convergence assumption is involved. Equivalently, exponentiating the
polynomial recovers `exp x * exp y` (`Ideal.exp_bch_of_pow_four_eq_bot`). If already `I ^ 3 = ⊥`,
the cubic terms vanish and the formula reduces to `x + y + ½⁅x, y⁆`
(`Ideal.log_exp_mul_exp_of_pow_three_eq_bot`).

The finite exponential and logarithm are `IsNilpotent.exp` and `IsNilpotent.log`; that
`exp x * exp y - 1` lies in `I` is `Ideal.exp_mul_exp_sub_one_mem`, which makes the logarithm
meaningful.

Adapted from `yuma-mizuno-lean/Mei`, commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/Nilpotent/BCH.lean` and `Mei/RingTheory/Ideal/Operations.lean` (Apache 2.0).

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, Chapter 5 (the
  Baker–Campbell–Hausdorff formula).
-/

public section

namespace Ideal

variable {A : Type*} [Ring A] [Algebra ℚ A]

-- Separate the homogeneous terms before expanding the powers of the logarithm.
private theorem algebra_bch3 (x y : A)
    (h4 : ∀ a b c d : A, (a = x ∨ a = y) → (b = x ∨ b = y) →
      (c = x ∨ c = y) → (d = x ∨ d = y) → a * (b * (c * d)) = 0) :
    let e := (1 + x + (1 / 2 : ℚ) • x ^ 2 + (1 / 6 : ℚ) • x ^ 3) *
      (1 + y + (1 / 2 : ℚ) • y ^ 2 + (1 / 6 : ℚ) • y ^ 3) - 1
    e - (1 / 2 : ℚ) • e ^ 2 + (1 / 3 : ℚ) • e ^ 3 =
      x + y + (1 / 2 : ℚ) • (x * y - y * x) +
        (1 / 12 : ℚ) • ((x * (x * y - y * x) - (x * y - y * x) * x) +
          (y * (y * x - x * y) - (y * x - x * y) * y)) := by
  -- Products of total degree at least four vanish, so square and cube reduce separately.
  let l := x + y
  let q := (1 / 2 : ℚ) • x ^ 2 + x * y + (1 / 2 : ℚ) • y ^ 2
  let c := (1 / 6 : ℚ) • x ^ 3 + (1 / 2 : ℚ) • (x ^ 2 * y) +
    (1 / 2 : ℚ) • (x * y ^ 2) + (1 / 6 : ℚ) • y ^ 3
  have he : (1 + x + (1 / 2 : ℚ) • x ^ 2 + (1 / 6 : ℚ) • x ^ 3) *
      (1 + y + (1 / 2 : ℚ) • y ^ 2 + (1 / 6 : ℚ) • y ^ 3) - 1 = l + q + c := by
    dsimp [l, q, c]
    noncomm_ring (discharger := simp) [h4, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  have he2 : (l + q + c) ^ 2 = l ^ 2 + l * q + q * l := by
    dsimp [l, q, c]
    noncomm_ring (discharger := simp) [h4, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  have he3 : (l + q + c) ^ 3 = l ^ 3 := by
    rw [pow_succ, he2]
    dsimp [l, q, c]
    noncomm_ring (discharger := simp) [h4, smul_add, smul_sub,
      smul_smul, smul_neg, add_smul, sub_smul]
    module
  dsimp only
  rw [he, he2, he3]
  dsimp [l, q, c]
  noncomm_ring [smul_add, smul_sub, smul_smul, smul_neg, add_smul, sub_smul]
  module

/-- **The Baker–Campbell–Hausdorff formula is exact through degree three** for elements of a
left ideal whose fourth power vanishes. -/
theorem log_exp_mul_exp_of_pow_four_eq_bot (I : Ideal A) (hI : I ^ 4 = ⊥) {x y : A}
    (hx : x ∈ I) (hy : y ∈ I) :
    IsNilpotent.log (IsNilpotent.exp x * IsNilpotent.exp y) =
      x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
        (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  have hI0 : I ^ 4 = 0 := by simpa only [Ideal.zero_eq_bot] using hI
  have hx4 := Ideal.pow_eq_zero_of_mem hI0 le_rfl hx
  have hy4 := Ideal.pow_eq_zero_of_mem hI0 le_rfl hy
  have hu4 := I.exp_mul_exp_sub_one_pow_eq_zero hI hx hy
  have he (z : A) : (∑ i ∈ Finset.range 4, (Nat.factorial i : ℚ)⁻¹ • z ^ i) =
      1 + z + (1 / 2 : ℚ) • z ^ 2 + (1 / 6 : ℚ) • z ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, Nat.factorial,
      Nat.cast_one, inv_one, pow_zero, one_smul, Nat.succ_eq_add_one, zero_add, mul_one,
      pow_one, Nat.reduceAdd, Nat.cast_ofNat, Nat.reduceMul, one_div]
  have hl (z : A) : (∑ i ∈ Finset.range 4, ((-1 : ℚ) ^ (i + 1) / i) • z ^ i) =
      z - (1 / 2 : ℚ) • z ^ 2 + (1 / 3 : ℚ) • z ^ 3 := by
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      pow_one, CharP.cast_eq_zero, div_zero, pow_zero, zero_smul, Nat.reduceAdd, even_two,
      Even.neg_pow, one_pow, Nat.cast_one, div_self (by decide : (1 : ℚ) ≠ 0), one_smul,
      Nat.cast_ofNat, one_div]
    module
  rw [IsNilpotent.log_eq_sum hu4, hl, IsNilpotent.exp_eq_sum hx4,
    IsNilpotent.exp_eq_sum hy4, he, he]
  simp only [Ring.lie_def]
  exact algebra_bch3 x y (fun a b c d ha hb hc hd ↦ by
    have ha' : a ∈ I := ha.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hb' : b ∈ I := hb.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hc' : c ∈ I := hc.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hd' : d ∈ I := hd.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil,
      mul_assoc, hI0, Ideal.zero_eq_bot, Ideal.mem_bot] using
      (Ideal.list_prod_mem_pow (I := I) (l := [a, b, c, d]) (by simp [ha', hb', hc', hd'])))

/-- Exponentiating the degree-three Baker–Campbell–Hausdorff polynomial of elements of a left
ideal with vanishing fourth power gives the product of their exponentials. -/
theorem exp_bch_of_pow_four_eq_bot (I : Ideal A) (hI : I ^ 4 = ⊥) {x y : A}
    (hx : x ∈ I) (hy : y ∈ I) :
    IsNilpotent.exp (x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
        (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)) =
      IsNilpotent.exp x * IsNilpotent.exp y := by
  rw [← log_exp_mul_exp_of_pow_four_eq_bot I hI hx hy]
  exact IsNilpotent.exp_log ⟨4, I.exp_mul_exp_sub_one_pow_eq_zero hI hx hy⟩

/-- **The Baker–Campbell–Hausdorff formula through degree two**: for elements of a left ideal
with vanishing cube, `log (exp x * exp y) = x + y + ½ ⁅x, y⁆`. -/
theorem log_exp_mul_exp_of_pow_three_eq_bot (I : Ideal A) (hI : I ^ 3 = ⊥) {x y : A}
    (hx : x ∈ I) (hy : y ∈ I) :
    IsNilpotent.log (IsNilpotent.exp x * IsNilpotent.exp y) =
      x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  have hI4 : I ^ 4 = ⊥ := le_bot_iff.mp (hI ▸ Ideal.pow_le_pow_right (by norm_num))
  have hz (a b c : A) (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) : a * b * c = 0 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil,
      ← mul_assoc, hI, Ideal.mem_bot] using
      (Ideal.list_prod_mem_pow (I := I) (l := [a, b, c]) (by simp [ha, hb, hc]))
  rw [log_exp_mul_exp_of_pow_four_eq_bot I hI4 hx hy]
  simp only [Ring.lie_def]
  have h1 : x * (x * y - y * x) - (x * y - y * x) * x = 0 := by
    simp only [mul_sub, sub_mul, ← mul_assoc, hz x x y hx hx hy, hz x y x hx hy hx,
      hz y x x hy hx hx]
    abel
  have h2 : y * (y * x - x * y) - (y * x - x * y) * y = 0 := by
    simp only [mul_sub, sub_mul, ← mul_assoc, hz y y x hy hy hx, hz y x y hy hx hy,
      hz x y y hx hy hy]
    abel
  rw [h1, h2]
  simp

end Ideal
