/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Commute.Units

/-!
# Commuting with nonzero powers, and distinct powers along homomorphisms

In a monoid with unique roots, a unit commutes with a nonzero natural power of `x` exactly when
it commutes with `x`. In a group with unique roots, the same holds for nonzero integer powers.

`Group.isUnit` is registered as a simp lemma, so that `simp` discharges the unit hypothesis of
the natural-power lemmas in a group.

The natural powers of an element whose image under a homomorphism into a torsion-free cancellative
monoid is nontrivial are pairwise distinct. This is the pullback of Mathlib's
`IsMulTorsionFree.pow_right_injective` along the homomorphism.

## Main results

* `Commute.pow_right_iff`, `Commute.zpow_left_iff`: with unique roots, commuting with a nonzero
  power of `x` is the same as commuting with `x`.
* `MonoidHom.pow_right_injective_of_map_ne_one` and its additive form
  `AddMonoidHom.nsmul_left_injective_of_map_ne_zero`: if `f a ≠ 1` with torsion-free target, then
  `n ↦ a ^ n` is injective.
-/

public section

attribute [simp] Group.isUnit

namespace Commute

section Monoid

variable {M : Type*} [Monoid M] [HasUniqueRoots M] {x y : M}

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_right_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute y (x ^ n) ↔ Commute y x := by
  obtain ⟨u, rfl⟩ := hy
  rw [u.commute_iff_mul_inv_cancel, u.commute_iff_mul_inv_cancel, ← u.conj_pow,
    (pow_left_injective hn).eq_iff]

/-- In a monoid with unique roots, a unit commutes with a nonzero natural power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem pow_left_iff {n : ℕ} (hn : n ≠ 0) (hy : IsUnit y) :
    Commute (x ^ n) y ↔ Commute x y :=
  Commute.symm_iff.trans ((pow_right_iff hn hy).trans Commute.symm_iff)

end Monoid

section Group

variable {G : Type*} [Group G] [HasUniqueRoots G] {x y : G}

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_left_iff {n : ℤ} (hn : n ≠ 0) : Commute (x ^ n) y ↔ Commute x y := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]
    exact pow_left_iff (by omega) (Group.isUnit y)
  · rw [zpow_neg, zpow_natCast, inv_left_iff]
    exact pow_left_iff (by omega) (Group.isUnit y)

/-- In a group with unique roots, an element commutes with a nonzero integer power of `x`
exactly when it commutes with `x`. -/
@[simp]
theorem zpow_right_iff {n : ℤ} (hn : n ≠ 0) : Commute y (x ^ n) ↔ Commute y x :=
  Commute.symm_iff.trans ((zpow_left_iff hn).trans Commute.symm_iff)

end Group

end Commute

/-- If a homomorphism into a torsion-free cancellative monoid sends `a` to a nontrivial element,
then the natural powers of `a` are pairwise distinct. -/
@[to_additive nsmul_left_injective_of_map_ne_zero /-- If an additive homomorphism into a
torsion-free cancellative additive monoid sends `a` to a nonzero element, then the natural
multiples of `a` are pairwise distinct. -/]
theorem MonoidHom.pow_right_injective_of_map_ne_one {M G : Type*} [Monoid M] [CancelMonoid G]
    [IsMulTorsionFree G] (f : M →* G) {a : M} (ha : f a ≠ 1) :
    Function.Injective fun n : ℕ => a ^ n :=
  .of_comp (f := f) <| by
    simpa only [Function.comp_def, map_pow] using IsMulTorsionFree.pow_right_injective ha
