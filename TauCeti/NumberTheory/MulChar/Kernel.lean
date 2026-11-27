/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.MulChar.Cyclic

/-!
# Kernels of characters on cyclic unit groups

On a finite cyclic unit group, a character of order `m` has an image of size `m`. In particular,
the character kills every `d`-torsion unit exactly when `m * gcd(d, #Mˣ)` divides `#Mˣ`.

For a finite field of cardinality `q` with `m² ∣ q - 1`, this constructs a character of order
`m` as the `m`-th power of a character of order `m²`. The resulting character is trivial on
roots of unity of every order dividing `m`. This allows a residue character of prescribed
order to kill the reductions of global roots of unity.

The residue character application follows `New.Data.chiMLocal`, `New.Data.orderOf_chiMLocal` and
`New.Data.chiMLocal_apply_eq_one_of_pow_q₁_eq_one` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace MulChar

section CyclicUnits

variable {M R : Type*} [CommMonoid M] [CommMonoidWithZero R] [IsCyclic Mˣ]

/-- The image on units of a character of a monoid with cyclic unit group has cardinality equal
to the order of the character. For an infinite image both natural numbers are zero. -/
theorem natCard_range_toUnitHom (χ : MulChar M R) :
    Nat.card χ.toUnitHom.range = orderOf χ := by
  obtain ⟨g, htop⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic Mˣ)
  have hg := (Subgroup.eq_top_iff' _).mp htop
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_zpowers, Nat.card_zpowers,
    ← orderOf_units, coe_toUnitHom, χ.orderOf_apply_eq_orderOf hg]

/-- A character kills every `d`-torsion unit precisely when the size of the `d`-torsion subgroup
multiplied by the order of the character divides the size of the unit group. -/
theorem forall_apply_eq_one_of_pow_eq_one_iff [Finite Mˣ] (χ : MulChar M R) (d : ℕ) :
    (∀ u : Mˣ, u ^ d = 1 → χ u = 1) ↔ orderOf χ * (Nat.card Mˣ).gcd d ∣ Nat.card Mˣ := by
  have hcard := Subgroup.card_ker_mul_card_range χ.toUnitHom
  rw [χ.natCard_range_toUnitHom, mul_comm] at hcard
  have hdiv : orderOf χ * (Nat.card Mˣ).gcd d ∣ Nat.card Mˣ ↔
      (Nat.card Mˣ).gcd d ∣ Nat.card χ.toUnitHom.ker := by
    conv_lhs => arg 2; rw [← hcard]
    exact Nat.mul_dvd_mul_iff_left (MulChar.orderOf_pos χ)
  rw [hdiv, ← IsCyclic.card_powMonoidHom_ker, ← IsCyclic.subgroup_le_iff_card_dvd]
  simp only [IsConcreteLE.le_iff, MonoidHom.mem_ker, powMonoidHom_apply]
  exact ⟨fun h u hu ↦ Units.val_eq_one.mp (by simpa only [coe_toUnitHom] using h u hu),
    fun h u hu ↦ by simpa only [← coe_toUnitHom] using Units.val_eq_one.mpr (h hu)⟩

end CyclicUnits

/-- If `m²` divides the size of the multiplicative group of a finite field, an `m`-th power of a
character of order `m²` has order `m` and is trivial on every `d`-torsion unit for `d ∣ m`. -/
theorem exists_orderOf_eq_and_apply_eq_one_of_pow_eq_one {F R : Type*}
    [Field F] [Fintype F] [CommRing R] {m : ℕ} {ζ : R}
    (hm : m ^ 2 ∣ Fintype.card F - 1) (hζ : IsPrimitiveRoot ζ (m ^ 2)) :
    ∃ ψ : MulChar F R, orderOf ψ = m ^ 2 ∧ orderOf (ψ ^ m) = m ∧
      ∀ d : ℕ, d ∣ m → ∀ u : Fˣ, u ^ d = 1 → (ψ ^ m) u = 1 := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_mulChar_orderOf F hm hζ
  have hm0 : m ≠ 0 := fun h ↦ (Nat.sub_pos_of_lt Fintype.one_lt_card).ne' (by simpa [h] using hm)
  have horder : orderOf (ψ ^ m) = m := by
    rw [orderOf_pow_of_dvd hm0 (hψ.symm ▸ dvd_pow_self m two_ne_zero), hψ, sq,
      Nat.mul_div_cancel _ hm0.bot_lt]
  refine ⟨ψ, hψ, horder, fun d hd ↦ ((ψ ^ m).forall_apply_eq_one_of_pow_eq_one_iff d).mpr ?_⟩
  have hcard : Nat.card Fˣ = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [horder, hcard]
  exact (Nat.mul_dvd_mul_left m ((Nat.gcd_dvd_right _ _).trans hd)).trans (by simpa [sq] using hm)

end MulChar
