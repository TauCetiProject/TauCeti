/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Directed

/-!
# Ramification indices

Ramified Laurent levels are indexed by positive natural numbers ordered by divisibility. This
file introduces that index type, shows it is a directed order with bottom element `1`, and
records the transition degree `m / n` attached to `n ∣ m`.

## Main definitions

* `TauCeti.RamificationIndex`: positive natural numbers ordered by divisibility.
* `TauCeti.RamificationIndex.transitionDegree`: the quotient `m / n` attached to `n ≤ m`.
-/

public section

namespace TauCeti

/-- Positive ramification indices, ordered by divisibility rather than by their usual order. -/
@[ext]
structure RamificationIndex where
  /-- The positive natural number underlying a ramification index. -/
  toPNat : ℕ+

namespace RamificationIndex

instance : LE RamificationIndex := ⟨fun n m ↦ n.toPNat ∣ m.toPNat⟩

/-- Comparison of ramification indices is divisibility of the underlying positive integers. -/
@[simp]
theorem le_iff_dvd {n m : RamificationIndex} : n ≤ m ↔ n.toPNat ∣ m.toPNat := Iff.rfl

instance : PartialOrder RamificationIndex where
  le := (· ≤ ·)
  le_refl n := dvd_refl n.toPNat
  le_trans _ _ _ := dvd_trans
  le_antisymm _ _ hnm hmn := RamificationIndex.ext (PNat.dvd_antisymm hnm hmn)

instance : IsDirectedOrder RamificationIndex where
  directed n m := ⟨⟨n.toPNat * m.toPNat⟩, ⟨m.toPNat, rfl⟩,
    ⟨n.toPNat, mul_comm _ _⟩⟩

instance : OrderBot RamificationIndex where
  bot := ⟨1⟩
  bot_le n := one_dvd n.toPNat

/-- The least ramification index is `1`. -/
@[simp]
theorem toPNat_bot : (⊥ : RamificationIndex).toPNat = 1 := rfl

/-- The quotient `m / n` attached to a divisibility relation `n ≤ m`. -/
def transitionDegree {n m : RamificationIndex} (_h : n ≤ m) : ℕ+ :=
  PNat.divExact m.toPNat n.toPNat

/-- Multiplying an index by its transition degree recovers the target index. -/
theorem mul_transitionDegree {n m : RamificationIndex} (h : n ≤ m) :
    n.toPNat * transitionDegree h = m.toPNat :=
  PNat.mul_div_exact h

@[simp]
theorem transitionDegree_refl (n : RamificationIndex) :
    transitionDegree (le_refl n) = 1 := by
  apply mul_left_cancel (a := n.toPNat)
  rw [mul_transitionDegree, mul_one]

/-- Transition degrees multiply along a chain of ramification indices. -/
theorem transitionDegree_trans {n m l : RamificationIndex} (hnm : n ≤ m) (hml : m ≤ l) :
    transitionDegree hnm * transitionDegree hml = transitionDegree (hnm.trans hml) := by
  apply mul_left_cancel (a := n.toPNat)
  calc
    n.toPNat * (transitionDegree hnm * transitionDegree hml) =
        (n.toPNat * transitionDegree hnm) * transitionDegree hml := (mul_assoc _ _ _).symm
    _ = m.toPNat * transitionDegree hml := by rw [mul_transitionDegree hnm]
    _ = l.toPNat := mul_transitionDegree hml
    _ = n.toPNat * transitionDegree (hnm.trans hml) :=
      (mul_transitionDegree (hnm.trans hml)).symm

end RamificationIndex

end TauCeti
