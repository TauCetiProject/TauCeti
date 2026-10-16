/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Valuation rings: squares `1 + 4c`, integrality under domination, and divisibility

In a commutative ring `R` with total divisibility and regular `2`, the element `1 + 4c` is a square
exactly when `c` has the form `t ^ 2 + t`, the witness being `1 + 2t`. One direction is an identity
valid in every commutative ring. The other says that every square root `y` of `1 + 4c` satisfies
`2 ∣ y - 1`, using total divisibility and cancellation by `2`.

Over the integer ring of a dyadic local field this reduces the question whether a unit of depth
`2 v(2)` is a square to the residue field, where `t ↦ t ^ 2 + t` is the Artin–Schreier map. This
is how the depth of the local square theorem is shown to be sharp.

A valuation ring `R` with fraction field `K` is also integrally closed against every ring that
dominates it: if `R → S` is a local homomorphism and `K` maps compatibly into a field `L`
containing `S`, an element of `K` whose image lies in `S` already lies in `R`. Over a discrete
valuation ring this is what lets an integrality statement proved after a ramified extension of
the base descend to the base itself.

Finally, on a ring with total divisibility, a valuation that is at most `1` everywhere, below `1`
on the nonunits and zero only at `0` is determined by divisibility: `v x ≤ v y` exactly when
`y ∣ x`. This describes the `𝔪`-adic valuation of a discrete valuation ring on its own elements,
and the points with zero support of its adic spectrum.

## Main results

* `TauCeti.ValuationRing.isSquare_one_add_four_mul_iff`: `1 + 4c` is a square if and only if
  `c = t ^ 2 + t` for some `t`.
* `TauCeti.ValuationRing.isInteger_of_isInteger_algebraMap`: an element of `K` whose image in `L`
  lies in a ring `S` dominating `R` already lies in `R`.
* `Valuation.le_iff_dvd`: a valuation at most `1`, below `1` on the nonunits and with zero
  support compares elements by divisibility.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

namespace TauCeti

namespace ValuationRing

variable {R : Type*} [CommRing R] [PreValuationRing R]

/-- In a commutative ring with total divisibility and regular `2`, the element `1 + 4c` is a
square if and only if `c` lies in the image of the quadratic map `t ↦ t ^ 2 + t`. -/
theorem isSquare_one_add_four_mul_iff (h2 : IsRegular (2 : R)) {c : R} :
    IsSquare (1 + 4 * c) ↔ ∃ t, t ^ 2 + t = c := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨t, ht⟩ ↦ ⟨1 + 2 * t, by rw [← ht]; ring⟩⟩
  -- Write `y = 1 + z`, so that `z ^ 2 + 2 * z = 4 * c`. The point is that `2 ∣ z`.
  obtain ⟨t, ht⟩ : 2 ∣ y - 1 := by
    rcases _root_.ValuationRing.dvd_total 2 (y - 1) with h | ⟨w, hw⟩
    · exact h
    -- Otherwise `2 = z * w`, and cancelling `z ^ 2` from `z ^ 2 * (1 + w) = z ^ 2 * w ^ 2 * c`
    -- shows that `w` is a unit.
    have hz : IsRegular (y - 1) :=
      (show IsRegular ((y - 1) * w) from hw ▸ h2).of_mul_left
    have hw' : 1 + w = w * w * c := (hz.mul hz).left <| by
      linear_combination -hy - (y - 1 - ((y - 1) * w + 2) * c) * hw
    have hu : IsUnit w := IsUnit.of_mul_eq_one (w * c - 1) (by linear_combination -hw')
    exact ⟨↑hu.unit⁻¹, by rw [hw, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩
  refine ⟨t, (h2.mul h2).left ?_⟩
  rw [sub_eq_iff_eq_add] at ht
  rw [ht] at hy
  linear_combination -hy

section Domination

variable {R S K L : Type*} [CommRing R] [IsDomain R] [_root_.ValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing S] [Field L] [Algebra S L] [Algebra K L]
  [Algebra R S] [IsLocalHom (algebraMap R S)]

/-- **A valuation ring is integrally closed against every ring dominating it.** Let `R` be a
valuation ring with fraction field `K`, let `R → S` be a local homomorphism, and let `S` and `K`
map compatibly into a field `L`, with `S → L` injective. An element of `K` whose image in `L` comes
from `S` already comes from `R`. -/
theorem isInteger_of_isInteger_algebraMap (hS : Function.Injective (algebraMap S L))
    (h : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    {x : K} (hx : IsLocalization.IsInteger S (algebraMap K L x)) :
    IsLocalization.IsInteger R x := by
  rcases _root_.ValuationRing.isInteger_or_isInteger R x with hR | ⟨r, hr⟩
  · exact hR
  rcases eq_or_ne x 0 with rfl | hx0
  · exact IsLocalization.isInteger_zero
  obtain ⟨s, hs⟩ := hx
  -- `x⁻¹ = r`, and the image of `r` in `S` is a unit with inverse `s`, so `r` is a unit of `R`.
  have hr' : IsUnit r := (isUnit_map_iff (algebraMap R S) r).mp <|
    IsUnit.of_mul_eq_one s <| hS <| by
      rw [map_mul, map_one, hs, ← RingHom.comp_apply, h, RingHom.comp_apply, hr, ← map_mul,
        inv_mul_cancel₀ hx0, map_one]
  refine ⟨↑hr'.unit⁻¹, ?_⟩
  rw [← inv_inv x, ← hr, map_units_inv, IsUnit.unit_spec]

end Domination

end ValuationRing

end TauCeti

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [PreValuationRing R] [LinearOrderedCommGroupWithZero Γ₀]

/-- **A valuation on a ring with total divisibility compares elements by divisibility** when it is
at most `1` everywhere, strictly below `1` on the nonunits, and zero only at `0`: then
`v x ≤ v y` exactly when `y ∣ x`. -/
theorem le_iff_dvd (v : Valuation R Γ₀) (hle : ∀ x, v x ≤ 1) (hlt : ∀ x, ¬ IsUnit x → v x < 1)
    (hsupp : ∀ x, v x = 0 → x = 0) {x y : R} : v x ≤ v y ↔ y ∣ x := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
  · rcases _root_.ValuationRing.dvd_total y x with hyx | ⟨z, rfl⟩
    · exact hyx
    -- `y = x * z`: either `z` is a unit, or `v y = v x * v z < v x` unless `x = 0`.
    by_cases hz : IsUnit z
    · exact ⟨↑hz.unit⁻¹, by simp [mul_assoc]⟩
    rcases eq_or_ne (v x) 0 with hx | hx
    · simp [hsupp x hx]
    rw [map_mul] at h
    exact absurd h (mul_lt_of_lt_one_right (zero_lt_iff.mpr hx) (hlt z hz)).not_ge
  · rw [hz, map_mul]
    exact mul_le_of_le_one_right' (hle z)

end Valuation
