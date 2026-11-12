/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Irreducible elements in the integer ring of a valuation

For any valuation `v` on a field `K` (without assuming `v.integer` is discrete), an irreducible
element `c : v.integer` has maximal valuation among elements of `IsLocalRing.maximalIdeal v.integer`
(`TauCeti.valuation_le_of_mem_maximalIdeal`, `TauCeti.valuation_le_mul_of_div_lt_one`), cannot be
factored into two elements of valuation below `1` (`TauCeti.valuation_lt_one_mul_ne_irreducible`),
and satisfies `v (x ^ 2) ≠ v (c * y ^ 2)` for `y ≠ 0`
(`TauCeti.valuation_sq_ne_valuation_mul_sq`). When `v.integer` is a discrete valuation ring, every
nonzero integral element has valuation a natural power of `v c`
(`TauCeti.exists_valuation_eq_pow_irreducible`).

## References

* N. Bourbaki, *Commutative Algebra*, Chapter VI, §3.
-/

public section

namespace TauCeti

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

/-- In a valued field, a product of two elements of valuation strictly below `1` cannot equal an
irreducible element of `v.integer`. -/
theorem valuation_lt_one_mul_ne_irreducible {c : v.integer} (hc : Irreducible c) {x y : K}
    (hx : v x < 1) (hy : v y < 1) : x * y ≠ (c : K) := fun h ↦
  hc.ne_mul_of_mem_maximalIdeal (x := ⟨x, hx.le⟩) (y := ⟨y, hy.le⟩)
    (v.mem_maximalIdeal_iff.mpr hx) (v.mem_maximalIdeal_iff.mpr hy) (Subtype.ext h.symm)

/-- Every element of `IsLocalRing.maximalIdeal v.integer` has valuation at most that of any
irreducible element of `v.integer`, without assuming discreteness of `v`. -/
theorem valuation_le_of_mem_maximalIdeal {c m : v.integer} (hc : Irreducible c)
    (hm : m ∈ IsLocalRing.maximalIdeal v.integer) : v (m : K) ≤ v (c : K) := by
  by_contra! hlt
  obtain ⟨-, d, hdu, hcd⟩ := (Valuation.integer.integers v).dvdNotUnit_iff_lt.mpr hlt
  exact (hc.isUnit_or_isUnit hcd).elim ((IsLocalRing.mem_maximalIdeal m).mp hm) hdu

/-- For irreducible `c : v.integer` and `0 < v y`, `v (x / y) < 1` implies `v x ≤ v c * v y`. -/
theorem valuation_le_mul_of_div_lt_one {c : v.integer} (hc : Irreducible c) {x y : K}
    (hy0 : 0 < v y) (hxy1 : v (x / y) < 1) :
    v x ≤ v (c : K) * v y := by
  simpa only [map_div₀, div_le_iff₀ hy0] using valuation_le_of_mem_maximalIdeal
    (m := ⟨x / y, hxy1.le⟩) hc (v.mem_maximalIdeal_iff.mpr hxy1)

/-- For an irreducible `c : v.integer` and `y ≠ 0`, `v (x ^ 2)` never equals `v (c * y ^ 2)`. -/
theorem valuation_sq_ne_valuation_mul_sq {c : v.integer} (hc : Irreducible c) {x y : K}
    (hy : y ≠ 0) : v (x ^ 2) ≠ v ((c : K) * y ^ 2) := fun h ↦ by
  have hy0 : v y ≠ 0 := ((Valuation.pos_iff v).mpr hy).ne'
  rcases eq_or_ne x 0 with rfl | hx
  · exact (mul_ne_zero (Valuation.integer.v_irreducible_pos hc).ne' (pow_ne_zero 2 hy0))
      (by simpa using h.symm)
  have hx0 : v x ≠ 0 := ((Valuation.pos_iff v).mpr hx).ne'
  have hdiv : v (x / y) ^ 2 = v (c : K) := by
    rw [← map_pow, div_pow, map_div₀, h, map_mul, map_pow,
      mul_div_cancel_right₀ _ (pow_ne_zero 2 hy0)]
  have hu1 : v (x / y) < 1 := not_le.mp fun hge ↦
    (hdiv ▸ Valuation.integer.v_irreducible_lt_one hc).not_ge (one_le_pow₀ hge)
  have hw1 : v ((c : K) * y / x) < 1 := by
    rwa [map_div₀, map_mul, ← hdiv, sq, map_div₀, mul_div_assoc, mul_assoc,
      div_mul_div_cancel₀ hy0, div_self hx0, mul_one, ← map_div₀]
  exact valuation_lt_one_mul_ne_irreducible hc hu1 hw1 (by field_simp)

/-- When `v.integer` is a discrete valuation ring, every nonzero integral element has valuation a
natural power of that of any irreducible element. -/
theorem exists_valuation_eq_pow_irreducible (v : Valuation K Γ₀) [IsDiscreteValuationRing v.integer]
    {c x : v.integer} (hx : x ≠ 0) (hc : Irreducible c) :
    ∃ n : ℕ, v (x : K) = v (c : K) ^ n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hc
  have hu : v ((u : v.integer) : K) = 1 := (Valuation.integer.integers v).valuation_unit u
  exact ⟨n, by simp [hu]⟩

end TauCeti
