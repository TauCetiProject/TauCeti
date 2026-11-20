/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Order of vanishing in the valuation ring of a place

For a place `P` of a field extension `F / k`, the valuation ring `P.integers` is a discrete
valuation ring (`TauCeti.Place.instIsDiscreteValuationRing`), so Mathlib's length-based order of
vanishing `Ring.ord P.integers x` is defined for every element `x : P.integers`. On nonzero
elements, it agrees with the normalized additive valuation `(P.ord (x : F)).toNat`.

## Main results

* `TauCeti.Place.ringOrd_integers_eq_toNat_ord`: for `x : P.integers` with `(x : F) ≠ 0`,
  `Ring.ord P.integers x = ((P.ord (x : F)).toNat : ℕ∞)`.
-/

public section

namespace TauCeti.Place

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

/-- For a nonzero element `x` of the valuation ring `𝒪_P` of a place `P`, the module-length order
of vanishing `Ring.ord 𝒪_P x` agrees with the normalized valuation `(P.ord x).toNat`. -/
theorem ringOrd_integers_eq_toNat_ord (P : Place k F) {x : P.integers} (hx : (x : F) ≠ 0) :
    Ring.ord P.integers x = ((P.ord (x : F)).toNat : ℕ∞) := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have ht_ord : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.1 ht
  have ht0 : t ≠ 0 := fun h0 ↦ by rw [h0, P.ord_zero] at ht_ord; omega
  let π : P.integers := ⟨t, P.mem_integers_iff_ord_nonneg.2 (by omega)⟩
  have hπ : Irreducible π := P.irreducible_of_isUniformizer ht
  have hx0 : x ≠ 0 := fun h0 ↦ hx (congrArg Subtype.val h0)
  obtain ⟨n, u, rfl⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  rw [Ring.ord_eq_addVal, _root_.IsDiscreteValuationRing.addVal_def' u hπ n]
  have hu0 : ((u : P.integers) : F) ≠ 0 := fun h0 ↦ u.ne_zero (Subtype.ext h0)
  have hord : P.ord (((u : P.integers) * π ^ n : P.integers) : F) = n := by
    rw [Subring.coe_mul, Subring.coe_pow]
    simp only [π]
    rw [P.ord_mul hu0 (pow_ne_zero n ht0), (P.isUnit_iff_ord_eq_zero hu0).1 u.isUnit,
      P.ord_pow t n, ht_ord]
    omega
  rw [hord, Int.toNat_natCast]

end TauCeti.Place
