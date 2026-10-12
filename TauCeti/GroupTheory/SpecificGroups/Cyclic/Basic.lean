/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic groups

For `n ≠ 0`, this file gives the standard computable enumeration of
`Multiplicative (ZMod n)`, transported from the additive group `ZMod n`.
It also records that an element corresponding to `1` under an equivalence with
`Multiplicative ℤ` generates its group, and Euler's criterion for `n`-th powers in a finite cyclic
group: when `n` divides the order `m`, an element is an `n`-th power exactly when its
`(m / n)`-th power is trivial.

## Main definitions

* `TauCeti.cyclicElements`: a computable enumeration of `Multiplicative (ZMod n)`.

## Main results

* `TauCeti.mem_cyclicElements`: the enumeration exhausts the group when `n ≠ 0`.
* `MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one`: an element sent to `1` by an equivalence with
  `Multiplicative ℤ` generates its group.
* `IsCyclic.mem_range_powMonoidHom_iff`: Euler's criterion for `n`-th powers in a finite cyclic
  group.

## References

The construction follows the enumeration pattern of `TauCeti.dihedralElements`.
-/

public section

namespace TauCeti

/-- For `n ≠ 0`, the standard computable enumeration of the finite cyclic group
`Multiplicative (ZMod n)`. For `n = 0`, this list is empty. -/
@[expose] def cyclicElements (n : ℕ) : List (Multiplicative (ZMod n)) :=
  List.ofFn fun i : Fin n => Multiplicative.ofAdd (i : ZMod n)

/-- Every element of `Multiplicative (ZMod n)` occurs in `TauCeti.cyclicElements n` when `n` is
nonzero. -/
theorem mem_cyclicElements (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ cyclicElements n := by
  rw [cyclicElements, List.mem_ofFn']
  exact ⟨⟨g.toAdd.val, ZMod.val_lt g.toAdd⟩,
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)⟩

/-- An element sent to `1` by a group equivalence with `Multiplicative ℤ` generates its
group. -/
theorem _root_.MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one {G : Type*} [Group G] {g : G}
    (e : G ≃* Multiplicative ℤ) (hg : e g = Multiplicative.ofAdd 1) :
    Subgroup.zpowers g = ⊤ :=
  (Subgroup.eq_top_iff' _).mpr fun y => ⟨(e y).toAdd,
    e.injective (by simp [hg, ← ofAdd_zsmul])⟩

/-- **Euler's criterion in a finite cyclic group.** If `n` divides the order of a finite cyclic
group `G`, then `x` is an `n`-th power exactly when `x ^ (Nat.card G / n) = 1`. -/
theorem _root_.IsCyclic.mem_range_powMonoidHom_iff {G : Type*} [CommGroup G] [IsCyclic G]
    [Finite G] {n : ℕ} (hn : n ∣ Nat.card G) (x : G) :
    x ∈ (powMonoidHom n : G →* G).range ↔ x ^ (Nat.card G / n) = 1 := by
  -- The `n`-th powers lie in the kernel of `y ↦ y ^ (Nat.card G / n)`, and both subgroups have
  -- `Nat.card G / n` elements.
  have hle : (powMonoidHom n : G →* G).range ≤ (powMonoidHom (Nat.card G / n) : G →* G).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
      Nat.mul_div_cancel' hn, pow_card_eq_one']
  have hcard : Nat.card (powMonoidHom (Nat.card G / n) : G →* G).ker ≤
      Nat.card (powMonoidHom n : G →* G).range := by
    rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range,
      Nat.gcd_eq_right hn, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hn)]
  rw [Subgroup.eq_of_le_of_card_ge hle hcard, MonoidHom.mem_ker, powMonoidHom_apply]

end TauCeti
