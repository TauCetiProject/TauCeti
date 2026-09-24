/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TriangleGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic triangle groups

For a positive integer `m`, the spherical signature `(1, m, m)` has triangle group
`TriangleGroup 1 m m`. The first relator makes `x` trivial, the product relation makes `z = y⁻¹`,
and the remaining presentation is the cyclic group of order `m`. This file records that
identification and its cardinality.

The equivalence is stated with the usual Mathlib multiplicative tag on `ZMod m`; it is a group
because the additive group `ZMod m` is being reinterpreted multiplicatively.
-/

public section

noncomputable section

namespace TauCeti

namespace TriangleGroup

private theorem cyclicGenerator_pow (m : ℕ) :
    (Multiplicative.ofAdd (1 : ZMod m)) ^ m = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow]
  simp

private theorem cyclicGenerator_inv_pow (m : ℕ) :
    ((Multiplicative.ofAdd (1 : ZMod m))⁻¹) ^ m = 1 := by
  rw [inv_pow, cyclicGenerator_pow, inv_one]

private def toCyclic (m : ℕ) : TriangleGroup 1 m m →* Multiplicative (ZMod m) :=
  lift 1 (Multiplicative.ofAdd (1 : ZMod m))
    ((Multiplicative.ofAdd (1 : ZMod m))⁻¹) (by simp) (cyclicGenerator_pow m)
    (cyclicGenerator_inv_pow m) (by simp)

private theorem toCyclic_y (m : ℕ) :
    toCyclic m (y 1 m m) = Multiplicative.ofAdd (1 : ZMod m) := by
  simp [toCyclic]

private theorem cyclic_zpowers_eq_top (m : ℕ) :
    Subgroup.zpowers (y 1 m m : TriangleGroup 1 m m) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  have hg : g ∈ Subgroup.closure {x 1 m m, y 1 m m} := by
    rw [closure_x_y]
    exact Subgroup.mem_top _
  -- After eliminating `x = 1`, the existing two-generator closure theorem says that `y` alone
  -- generates the group.
  have hle : Subgroup.closure {x 1 m m, y 1 m m} ≤ Subgroup.zpowers (y 1 m m) :=
    (Subgroup.closure_le (Subgroup.zpowers (y 1 m m))).2 (by
      intro q hq
      rcases hq with rfl | rfl
      · have hx : x 1 m m = 1 := by
          simpa using (x_pow 1 m m)
        rw [hx]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers (y 1 m m))
  exact hle hg

private theorem cyclic_order_y (m : ℕ) (hm : 0 < m) :
    orderOf (y 1 m m : TriangleGroup 1 m m) = m := by
  -- The representation into `ZMod m` supplies the lower bound on the order.
  have hmap : orderOf (toCyclic m (y 1 m m)) = m := by
    rw [toCyclic_y, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have h₁ : orderOf (toCyclic m (y 1 m m)) ∣ orderOf (y 1 m m) :=
    orderOf_map_dvd _ _
  have h₂ : orderOf (y 1 m m) ∣ m := orderOf_dvd_of_pow_eq_one (y_pow 1 m m)
  -- The relator supplies the upper bound; the two divisibilities therefore force equality.
  have h₁' : m ∣ orderOf (y 1 m m) := by simpa [hmap] using h₁
  apply Nat.le_antisymm
  · exact Nat.le_of_dvd hm h₂
  · exact Nat.le_of_dvd (Nat.pos_of_dvd_of_pos h₂ hm) h₁'

/-- The cyclic spherical triangle group `TriangleGroup 1 m m` has cardinality `m`. -/
@[simp]
theorem natCard_one_self_self (m : ℕ) (hm : 0 < m) : Nat.card (TriangleGroup 1 m m) = m := by
  exact (orderOf_eq_card_of_zpowers_eq_top (cyclic_zpowers_eq_top m)).symm.trans
    (cyclic_order_y m hm)

/-- The spherical signature `(1, m, m)` has cyclic triangle group, of order `m`. -/
noncomputable def equivCyclic (m : ℕ) (hm : 0 < m) :
    TriangleGroup 1 m m ≃* Multiplicative (ZMod m) :=
  (zmodMulEquivOfGenerator (G := TriangleGroup 1 m m) (g := y 1 m m)
    (by
      intro q
      rw [cyclic_zpowers_eq_top]
      exact Subgroup.mem_top q)
    (by simpa using natCard_one_self_self m hm)).symm

/-- `equivCyclic` sends the trivial generator `x` to the identity. -/
@[simp]
theorem equivCyclic_x (m : ℕ) (hm : 0 < m) :
    equivCyclic m hm (x 1 m m) = 1 := by
  have hx : x 1 m m = 1 := by simpa using (x_pow 1 m m)
  simp [hx, equivCyclic]

/-- `equivCyclic` sends `y` to the generator `Multiplicative.ofAdd 1`. -/
@[simp]
theorem equivCyclic_y (m : ℕ) (hm : 0 < m) :
    equivCyclic m hm (y 1 m m) = Multiplicative.ofAdd (1 : ZMod m) := by
  simp [equivCyclic]

/-- `equivCyclic` sends `z` to the inverse generator `Multiplicative.ofAdd (-1)`. -/
@[simp]
theorem equivCyclic_z (m : ℕ) (hm : 0 < m) :
    equivCyclic m hm (z 1 m m) = Multiplicative.ofAdd (-1 : ZMod m) := by
  have hx : x 1 m m = 1 := by simpa only [pow_one] using (x_pow 1 m m)
  rw [z_eq, hx]
  simp [equivCyclic]

/-- The inverse of `equivCyclic` sends `Multiplicative.ofAdd 1` to `y`. -/
@[simp]
theorem equivCyclic_symm_ofAdd_one (m : ℕ) (hm : 0 < m) :
    (equivCyclic m hm).symm (Multiplicative.ofAdd (1 : ZMod m)) = y 1 m m := by
  simp [equivCyclic]

end TriangleGroup

end TauCeti
