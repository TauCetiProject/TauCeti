/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Nilpotent.Exp.Submodule
public import TauCeti.RingTheory.Nilpotent.Log
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# The Baker–Campbell–Hausdorff formula through degree three

For elements `x` and `y` of a submodule `M` of an associative `ℚ`-algebra whose fourth power
vanishes, the finite logarithm of the product `exp x * exp y` is exactly the usual
Baker–Campbell–Hausdorff polynomial through degree three:
`x + y + ½⁅x, y⁆ + 1/12 (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)`, where `⁅a, b⁆ = a * b - b * a`
(`Submodule.log_exp_mul_exp_of_pow_four_eq_bot`). Every word of length at least four in `x` and `y`
vanishes, so no convergence assumption is involved. Equivalently, exponentiating the
polynomial recovers `exp x * exp y` (`Submodule.exp_bch_of_pow_four_eq_bot`).
If already `M ^ 3 = ⊥`, the cubic terms vanish and the formula reduces to `x + y + ½⁅x, y⁆`
(`Submodule.log_exp_mul_exp_of_pow_three_eq_bot`), whose exponentiated form is
`Submodule.exp_bch_of_pow_three_eq_bot`.

The finite exponential and logarithm are `IsNilpotent.exp` and `IsNilpotent.log`.
The vanishing of words of length four also makes `exp x * exp y - 1` nilpotent, so the
logarithm is meaningful; no closure of `M` under rational scalars is needed.

Adapted from `yuma-mizuno-lean/Mei`, commit `3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/RingTheory/Nilpotent/BCH.lean` and `Mei/RingTheory/Ideal/Operations.lean` (Apache 2.0).

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, Chapter 5 (the
  Baker–Campbell–Hausdorff formula).
-/

public section

namespace Submodule

variable {A : Type*} [Ring A] [Module ℚ A]

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
  rw [he]
  rw [he2, he3]
  dsimp [l, q, c]
  noncomm_ring [smul_add, smul_sub, smul_smul, smul_neg, add_smul, sub_smul]
  module

variable {R : Type*} [Semiring R] [Module R A] [IsScalarTower R A A]

/-- **The Baker–Campbell–Hausdorff formula is exact through degree three** for elements of a
submodule whose fourth power vanishes. -/
theorem log_exp_mul_exp_of_pow_four_eq_bot (M : Submodule R A) (hM : M ^ 4 = ⊥) {x y : A}
    (hx : x ∈ M) (hy : y ∈ M) :
    IsNilpotent.log (IsNilpotent.exp x * IsNilpotent.exp y) =
      x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
        (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆) := by
  have hx4 : x ^ 4 = 0 := by simpa only [hM, Submodule.mem_bot] using M.pow_mem_pow hx 4
  have hy4 : y ^ 4 = 0 := by simpa only [hM, Submodule.mem_bot] using M.pow_mem_pow hy 4
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
  have hcalc := algebra_bch3 x y (fun a b c d ha hb hc hd ↦ by
    have ha' : a ∈ M := ha.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hb' : b ∈ M := hb.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hc' : c ∈ M := hc.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    have hd' : d ∈ M := hd.elim (fun h ↦ h ▸ hx) (fun h ↦ h ▸ hy)
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil,
      mul_assoc, hM, Submodule.mem_bot] using
      (Submodule.list_prod_mem_pow (M := M) (l := [a, b, c, d]) (by simp [ha', hb', hc', hd'])))
  rw [IsNilpotent.log_eq_sum (M.exp_mul_exp_sub_one_pow_eq_zero hM hx hy), hl,
    IsNilpotent.exp_eq_sum hx4, IsNilpotent.exp_eq_sum hy4, he, he]
  simpa only [Ring.lie_def] using hcalc

/-- Exponentiating the degree-three Baker–Campbell–Hausdorff polynomial of elements of a
submodule with vanishing fourth power gives the product of their exponentials. -/
theorem exp_bch_of_pow_four_eq_bot (M : Submodule R A) (hM : M ^ 4 = ⊥) {x y : A}
    (hx : x ∈ M) (hy : y ∈ M) :
    IsNilpotent.exp (x + y + (1 / 2 : ℚ) • ⁅x, y⁆ +
        (1 / 12 : ℚ) • (⁅x, ⁅x, y⁆⁆ + ⁅y, ⁅y, x⁆⁆)) =
      IsNilpotent.exp x * IsNilpotent.exp y := by
  let _ : Algebra ℚ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  rw [← log_exp_mul_exp_of_pow_four_eq_bot M hM hx hy]
  exact IsNilpotent.exp_log ⟨4, M.exp_mul_exp_sub_one_pow_eq_zero hM hx hy⟩

/-- **The Baker–Campbell–Hausdorff formula through degree two**: for elements of a submodule
with vanishing cube, `log (exp x * exp y) = x + y + ½ ⁅x, y⁆`. -/
theorem log_exp_mul_exp_of_pow_three_eq_bot (M : Submodule R A) (hM : M ^ 3 = ⊥) {x y : A}
    (hx : x ∈ M) (hy : y ∈ M) :
    IsNilpotent.log (IsNilpotent.exp x * IsNilpotent.exp y) =
      x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  have hM4 : M ^ 4 = ⊥ := by rw [Submodule.pow_succ, hM, Submodule.bot_mul]
  have hz (a b c : A) (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) : a * b * c = 0 := by
    simpa only [List.prod_cons, List.prod_nil, mul_one, List.length_cons, List.length_nil,
      ← mul_assoc, hM, Submodule.mem_bot] using
      (Submodule.list_prod_mem_pow (M := M) (l := [a, b, c]) (by simp [ha, hb, hc]))
  rw [log_exp_mul_exp_of_pow_four_eq_bot M hM4 hx hy]
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

/-- Exponentiating the degree-two Baker–Campbell–Hausdorff polynomial of elements of a
submodule with vanishing cube gives the product of their exponentials. -/
theorem exp_bch_of_pow_three_eq_bot (M : Submodule R A) (hM : M ^ 3 = ⊥) {x y : A}
    (hx : x ∈ M) (hy : y ∈ M) :
    IsNilpotent.exp (x + y + (1 / 2 : ℚ) • ⁅x, y⁆) =
      IsNilpotent.exp x * IsNilpotent.exp y := by
  let _ : Algebra ℚ A := Algebra.ofModule smul_mul_assoc mul_smul_comm
  rw [← log_exp_mul_exp_of_pow_three_eq_bot M hM hx hy]
  exact IsNilpotent.exp_log ⟨3, M.exp_mul_exp_sub_one_pow_eq_zero hM hx hy⟩

end Submodule
