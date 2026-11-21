/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.RingTheory.Valuation.Discrete.Order.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in the valuation ring of a normalized discrete valuation

For a surjective `ℤᵐ⁰`-valued valuation `v` on a field `F`, the valuation subring
`v.valuationSubring` is a discrete valuation ring
(`Valuation.valuationSubring_isDiscreteValuationRing_of_surjective`), so Mathlib's length-based
order of vanishing `Ring.ord v.valuationSubring x` is defined for every `x : v.valuationSubring`.
On nonzero elements, it agrees with the normalized additive order `(Valuation.ord v (x : F)).toNat`.

## Main results

* `Valuation.ringOrd_valuationSubring_eq_toNat_ord`: for `x : v.valuationSubring` with
  `(x : F) ≠ 0`, `Ring.ord v.valuationSubring x = ((Valuation.ord v (x : F)).toNat : ℕ∞)`.
-/

public section

open scoped WithZero

namespace Valuation

/-- For a nonzero element `x` of the valuation subring of a surjective `ℤᵐ⁰`-valued valuation `v`,
the module-length order of vanishing `Ring.ord v.valuationSubring x` agrees with the normalized
additive order `(Valuation.ord v (x : F)).toNat`. -/
theorem ringOrd_valuationSubring_eq_toNat_ord {F : Type*} [Field F]
    (v : _root_.Valuation F ℤᵐ⁰) (hv : Function.Surjective v) {x : v.valuationSubring}
    (hx : (x : F) ≠ 0) :
    Ring.ord v.valuationSubring x = ((ord v (x : F)).toNat : ℕ∞) := by
  let _ := nontrivial_valueGroup_of_surjective v hv
  let _ := valuationSubring_isDiscreteValuationRing_of_surjective v hv
  obtain ⟨t, ht⟩ := exists_isUniformizer_of_surjective v hv
  have ht_ord : ord v t = 1 := (isUniformizer_iff_ord_eq_one_of_surjective v hv).1 ht
  have ht0 : t ≠ 0 := fun h0 ↦ by rw [h0, ord_zero] at ht_ord; omega
  let π : v.valuationSubring := ⟨t, (mem_valuationSubring_iff_ord_nonneg v).2 (by omega)⟩
  have hπ : Irreducible π := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact ht.is_generator
  have hx0 : x ≠ 0 := fun h0 ↦ hx (congrArg Subtype.val h0)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_def' u hπ n]
  have hu0 : ((u : v.valuationSubring) : F) ≠ 0 := fun h0 ↦ u.ne_zero (Subtype.ext h0)
  have hord : ord v (((u : v.valuationSubring) * π ^ n : v.valuationSubring) : F) = n := by
    rw [Subring.coe_mul, Subring.coe_pow]
    simp only [π]
    rw [ord_mul v (v.ne_zero_iff.2 hu0) (v.ne_zero_iff.2 (pow_ne_zero n ht0)),
      (isUnit_iff_ord_eq_zero v hu0).1 u.isUnit, ord_pow v t n, ht_ord]
    omega
  rw [hord, Int.toNat_natCast]

end Valuation
