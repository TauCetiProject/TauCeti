/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic triangle groups

For natural numbers `m` and `n`, the triangle group `TriangleGroup 1 m n` is cyclic. The first
relator makes `x` trivial, the product relation makes `z = y⁻¹`, and the remaining presentation
is the cyclic group of order `Nat.gcd m n` when that gcd is positive. When `m = n = 0`, it is
infinite cyclic. In particular, taking `n = m` identifies `TriangleGroup 1 m m` with the cyclic
group of order `m`.

The equivalence is stated with the usual Mathlib multiplicative tag on `ZMod (Nat.gcd m n)`;
it is a group because the additive group `ZMod (Nat.gcd m n)` is being reinterpreted
multiplicatively.
-/

public section

noncomputable section

namespace TauCeti

namespace TriangleGroup

private theorem ofAdd_one_zpow_eq_one (d k : ℕ) (h : d ∣ k) :
    (Multiplicative.ofAdd (1 : ZMod d)) ^ k = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, nsmul_eq_mul, toAdd_ofAdd, mul_one]
  exact (ZMod.natCast_eq_zero_iff k d).2 h

private theorem ofAdd_neg_one_zpow_eq_one (d k : ℕ) (h : d ∣ k) :
    ((Multiplicative.ofAdd (1 : ZMod d))⁻¹) ^ k = 1 := by
  rw [inv_pow, ofAdd_one_zpow_eq_one d k h, inv_one]

private def toCyclic (m n : ℕ) :
    TriangleGroup 1 m n →* Multiplicative (ZMod (Nat.gcd m n)) :=
  lift 1 (Multiplicative.ofAdd (1 : ZMod (Nat.gcd m n)))
    ((Multiplicative.ofAdd (1 : ZMod (Nat.gcd m n)))⁻¹) (by simp)
    (ofAdd_one_zpow_eq_one _ _ (Nat.gcd_dvd_left m n))
    (ofAdd_neg_one_zpow_eq_one _ _ (Nat.gcd_dvd_right m n))
    (by simp)

private theorem toCyclic_y (m n : ℕ) :
    toCyclic m n (y 1 m n) = Multiplicative.ofAdd (1 : ZMod (Nat.gcd m n)) := by
  simp [toCyclic]

private theorem cyclic_zpowers_eq_top (m n : ℕ) :
    Subgroup.zpowers (y 1 m n : TriangleGroup 1 m n) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  have hg : g ∈ Subgroup.closure {x 1 m n, y 1 m n} := by
    rw [closure_x_y]
    exact Subgroup.mem_top _
  -- After eliminating `x = 1`, the existing two-generator closure theorem says that `y` alone
  -- generates the group.
  have hle : Subgroup.closure {x 1 m n, y 1 m n} ≤
      Subgroup.zpowers (y 1 m n) :=
    (Subgroup.closure_le (Subgroup.zpowers (y 1 m n))).2 (by
      intro q hq
      rcases hq with rfl | rfl
      · have hx : x 1 m n = 1 := by
          simpa using (x_pow 1 m n)
        rw [hx]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers (y 1 m n))
  exact hle hg

private theorem cyclic_order_y (m n : ℕ) :
    orderOf (y 1 m n : TriangleGroup 1 m n) = Nat.gcd m n := by
  -- The representation into `ZMod (Nat.gcd m n)` supplies the lower bound on the order.
  have hmap : orderOf (toCyclic m n (y 1 m n)) = Nat.gcd m n := by
    rw [toCyclic_y, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have h₁ : orderOf (toCyclic m n (y 1 m n)) ∣ orderOf (y 1 m n) :=
    orderOf_map_dvd _ _
  have hx : x 1 m n = 1 := by simpa using (x_pow 1 m n)
  have hyₙ : (y 1 m n) ^ n = 1 := by
    simpa [hx] using (y_mul_x_pow (a := 1) (b := m) (c := n))
  have h₂ : orderOf (y 1 m n : TriangleGroup 1 m n) ∣ Nat.gcd m n :=
    Nat.dvd_gcd (orderOf_y_dvd 1 m n) (orderOf_dvd_of_pow_eq_one hyₙ)
  -- The relators supply the upper bound; the two divisibilities therefore force equality.
  have h₁' : Nat.gcd m n ∣ orderOf (y 1 m n) := by simpa [hmap] using h₁
  exact Nat.dvd_antisymm h₂ h₁'

/-- The triangle group `TriangleGroup 1 m n` has cardinality `Nat.gcd m n`.
For `m = n = 0`, it is infinite cyclic and its `Nat.card` is `0`. -/
@[simp]
theorem natCard_one (m n : ℕ) : Nat.card (TriangleGroup 1 m n) = Nat.gcd m n := by
  exact (orderOf_eq_card_of_zpowers_eq_top (cyclic_zpowers_eq_top m n)).symm.trans
    (cyclic_order_y m n)

/-- For `m > 0`, the triangle group `TriangleGroup 1 m m` has cardinality `m`.
For `m = 0`, it is infinite cyclic and its `Nat.card` is `0`. -/
theorem natCard_one_self_self (m : ℕ) : Nat.card (TriangleGroup 1 m m) = m := by
  simpa only [Nat.gcd_self] using natCard_one m m

/-- If `Nat.gcd m n > 0`, the signature `(1, m, n)` has cyclic triangle group of order
`Nat.gcd m n`. If `m = n = 0`, it is infinite cyclic. -/
noncomputable def equivCyclic (m n : ℕ) :
    TriangleGroup 1 m n ≃* Multiplicative (ZMod (Nat.gcd m n)) :=
  (zmodMulEquivOfGenerator (G := TriangleGroup 1 m n) (g := y 1 m n)
    (by
      intro q
      rw [cyclic_zpowers_eq_top]
      exact Subgroup.mem_top q)
    (by exact natCard_one m n)).symm

/-- `equivCyclic` sends the trivial generator `x` to the identity. -/
@[simp]
theorem equivCyclic_x (m n : ℕ) :
    equivCyclic m n (x 1 m n) = 1 := by
  have hx : x 1 m n = 1 := by simpa using (x_pow 1 m n)
  simp [hx, equivCyclic]

/-- `equivCyclic` sends `y` to the generator `Multiplicative.ofAdd 1`. -/
@[simp]
theorem equivCyclic_y (m n : ℕ) :
    equivCyclic m n (y 1 m n) = Multiplicative.ofAdd (1 : ZMod (Nat.gcd m n)) := by
  simp [equivCyclic]

/-- `equivCyclic` sends `z` to the inverse generator `Multiplicative.ofAdd (-1)`. -/
@[simp]
theorem equivCyclic_z (m n : ℕ) :
    equivCyclic m n (z 1 m n) = Multiplicative.ofAdd (-1 : ZMod (Nat.gcd m n)) := by
  have hx : x 1 m n = 1 := by simpa only [pow_one] using (x_pow 1 m n)
  rw [z_eq, hx]
  simp [equivCyclic]

/-- The inverse of `equivCyclic` sends `Multiplicative.ofAdd 1` to `y`. -/
@[simp]
theorem equivCyclic_symm_ofAdd_one (m n : ℕ) :
    (equivCyclic m n).symm (Multiplicative.ofAdd (1 : ZMod (Nat.gcd m n))) = y 1 m n := by
  simp [equivCyclic]

end TriangleGroup

end TauCeti
