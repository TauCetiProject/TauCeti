/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Nontriviality survives restriction along an integral algebra

A valuation of `L` restricts along `algebraMap K L` to a valuation of `K`, and this file records
that the restriction of a nontrivial valuation is again nontrivial as soon as `L` is integral
over `K`.

Integrality is what makes this true, and it is sharp: without it the restriction can collapse.
The valuation of `K(t)` reading the `t`-adic order restricts to the trivial valuation on `K`.

This is restriction of the *domain*, along a ring map. It is unrelated to
`Valuation.RankOne.isNontrivial_restrict`, which restricts the *value group* of a valuation to its
value subgroup and leaves the domain alone.

## Main results

* `Valuation.isNontrivial_comap_algebraMap`: the restriction of a nontrivial valuation along an
  integral algebra is nontrivial.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005].
-/

public section

namespace Valuation

variable {K L Γ₀ : Type*} [CommRing K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- **The restriction of a nontrivial valuation along an integral algebra is nontrivial.** -/
theorem isNontrivial_comap_algebraMap [Algebra.IsIntegral K L] (v : Valuation L Γ₀)
    [v.IsNontrivial] : (v.comap (algebraMap K L)).IsNontrivial := by
  by_contra hcon
  -- a trivial restriction puts `K` inside the valuation ring; splitting on the *value* rather
  -- than on `k` avoids needing `algebraMap K L` to be injective
  have htriv : ∀ k : K, v (algebraMap K L k) ≤ 1 := by
    intro k
    by_contra hk
    exact hcon ⟨k, fun h ↦ hk (h ▸ zero_le_one), fun h ↦ hk (le_of_eq h)⟩
  have hmem : ∀ k : K, algebraMap K L k ∈ v.integer := fun k ↦ htriv k
  let _ : Algebra K v.integer := ((algebraMap K L).codRestrict _ hmem).toAlgebra
  have _ : IsScalarTower K v.integer L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- every element is integral over `K`, hence over the valuation ring, hence of value `≤ 1`
  have hle : ∀ x : L, v x ≤ 1 := fun x ↦
    (Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).1
      (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  -- the same at inverses forces every nonzero element to have value exactly `1`
  obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
  refine hx1 (le_antisymm (hle x) ?_)
  have h1 : v x⁻¹ ≤ 1 := hle x⁻¹
  rw [map_inv₀] at h1
  exact (inv_le_one₀ (zero_lt_iff.mpr hx0)).mp h1

end Valuation

end
