/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import TauCeti.Data.Rat.NumDenDvd

/-!
# Linear fractional transformations over a field

A linear fractional transformation `t ↦ (a * t + b) / (c * t + d)` over a field `𝕜` is
determined by its coefficient matrix `!![a, b; c, d]`, and the determinant `a * d - b * c`
controls how it separates points. This file records the algebraic identity behind that: the
transformation carries the displacement `t - w` to the displacement of the images scaled by
`(a * d - b * c) / ((c * t + d) * (c * w + d))`, and in particular, if it fixes `w`, it scales
the displacement `t - w` by that factor.

This is the computation that linearizes a linear fractional transformation at a fixed point.
Over `ℂ` it is what turns a Möbius transformation of the upper half-plane into a rotation between
the disc coordinates centred at a point and at its image, in
`TauCeti/Analysis/Complex/UpperHalfPlane/DiscCoordinate.lean`.

## Main results

* `TauCeti.one_add_div_one_sub_sub_mul_div_one_sub`: affine factors under the chart
  `u ↦ u / (1 - u)` over a division ring.
* `TauCeti.moebius_sub_moebius`: the difference formula for a linear fractional transformation.
* `TauCeti.moebius_sub_of_fixed`: the difference formula for a linear fractional
  transformation at a fixed point.
* `TauCeti.neg_mul_moebius_add_ne_zero`, `TauCeti.moebius_inv_moebius`: away from the pole
  `c * t + d = 0`, the adjugate transformation `y ↦ (d * y - b) / (-c * y + a)` has nonzero
  denominator at `y = (a * t + b) / (c * t + d)` and recovers `t` when `a * d - b * c ≠ 0`.
* `RingHom.eq_map_neg_div_of_map_mul_add_map_eq_zero`: at the pole `f c * x + f d = 0` of a
  nonsingular linear fractional transformation with coefficients mapped along `f : K →+* L`,
  `x = f (-d / c)`.
* `TauCeti.apply_mul_add_div_mul_add_eq_of_int_le`: a function on a characteristic-zero field
  that is nonincreasing under nonsingular integer linear fractional transformations away from
  their poles is invariant under all nonsingular rational linear fractional transformations,
  including at the pole.
* `TauCeti.crossRatio_comp_eq_of_sub_eq_div`: maps with factorized differences preserve
  cross-ratios.
* `TauCeti.div_sub_inv_sub_div_sq_eq_div_sub_sub_div`: the partial-fraction identity for a pole
  under the inversion `w ↦ p - w⁻¹`.
* `TauCeti.siegel_identity`: Siegel's three-term identity for linear factors `x - θᵢ y`,
  divided by `(θ₁ - θ₀) (x - θ₂ y)`.
* `TauCeti.ne_one_of_mul_sub_mul_eq`, `TauCeti.div_eq_sub_mul_div_one_sub_of_mul_sub_mul_eq`:
  the quotient `t = (x - θ₀ y) / (x - θ₂ y)`, a linear fractional function of `x / y`, is not
  `1` when `θ₀ ≠ θ₂` and `y ≠ 0`, and the inverse transformation recovers
  `x / y = (θ₀ - t θ₂) / (1 - t)`. These are used in the reduction of Thue equations to unit
  equations, in `TauCeti/NumberTheory/UnitEquation/Thue/Basic.lean`.
-/

public section

namespace RingHom

/-- At the pole `f c * x + f d = 0` of a linear fractional transformation with coefficients mapped
along a field homomorphism `f : K →+* L` and nonzero determinant `a * d - b * c`,
`x = f (-d / c)`. -/
theorem eq_map_neg_div_of_map_mul_add_map_eq_zero {K L : Type*} [Field K] [Field L]
    (f : K →+* L) {a b c d : K} {x : L} (hdet : a * d - b * c ≠ 0)
    (hx : f c * x + f d = 0) :
    x = f (-d / c) := by
  have hc : c ≠ 0 := by
    rintro rfl
    have hd : d = 0 := (map_eq_zero f).mp (by simpa using hx)
    exact hdet (by simp [hd])
  rw [map_div₀, map_neg, eq_div_iff ((map_ne_zero f).mpr hc)]
  linear_combination hx

end RingHom

namespace TauCeti

/-- The chart `u ↦ u / (1 - u)` shifts by one to the inverse denominator. -/
theorem one_add_div_one_sub {K : Type*} [DivisionRing K] {u : K} (hu : 1 - u ≠ 0) :
    1 + u / (1 - u) = (1 - u)⁻¹ := by
  rw [one_add_div hu]
  simp

/-- An affine factor in the chart `v = u / (1 - u)` has the same denominator. -/
theorem one_add_div_one_sub_sub_mul_div_one_sub {K : Type*} [DivisionRing K] {u : K}
    (hu : 1 - u ≠ 0) (z : K) :
    1 + u / (1 - u) - z * (u / (1 - u)) = (1 - z * u) * (1 - u)⁻¹ := by
  rw [one_add_div_one_sub hu, div_eq_mul_inv, ← mul_assoc, sub_mul, one_mul]

/-- **The Möbius difference formula**: if both denominators are nonzero, then
`(a * t + b) / (c * t + d) - (a * w + b) / (c * w + d) =
(a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d))`. -/
theorem moebius_sub_moebius {𝕜 : Type*} [Field 𝕜] {a b c d w t : 𝕜} (hj : c * w + d ≠ 0)
    (hjt : c * t + d ≠ 0) :
    (a * t + b) / (c * t + d) - (a * w + b) / (c * w + d) =
      (a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d)) := by
  rw [div_sub_div _ _ hjt hj]
  ring

/-- The Möbius difference formula at a fixed point: if `w` is fixed, in the cleared form
`a * w + b = w * (c * w + d)`, and both denominators are nonzero, then
`(a * t + b) / (c * t + d) - w = (a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d))`. -/
theorem moebius_sub_of_fixed {𝕜 : Type*} [Field 𝕜] {a b c d w t : 𝕜}
    (hw : a * w + b = w * (c * w + d)) (hj : c * w + d ≠ 0) (hjt : c * t + d ≠ 0) :
    (a * t + b) / (c * t + d) - w =
      (a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d)) := by
  rw [← moebius_sub_moebius hj hjt, (div_eq_iff hj).mpr hw]

/-- Away from the pole `c * t + d = 0`, a linear fractional transformation of nonzero determinant
`a * d - b * c` takes a value outside the pole `-c * y + a = 0` of its adjugate inverse. -/
theorem neg_mul_moebius_add_ne_zero {𝕜 : Type*} [Field 𝕜] {a b c d t : 𝕜}
    (hdet : a * d - b * c ≠ 0) (hjt : c * t + d ≠ 0) :
    -c * ((a * t + b) / (c * t + d)) + a ≠ 0 := by
  have hy : (a * t + b) / (c * t + d) * (c * t + d) = a * t + b := div_mul_cancel₀ _ hjt
  exact fun h0 ↦ hdet (by linear_combination (c * t + d) * h0 + c * hy)

/-- **Left-inverse identity for a linear fractional transformation.** Away from the pole
`c * t + d = 0`, the adjugate transformation `y ↦ (d * y - b) / (-c * y + a)` recovers `t` from
`y = (a * t + b) / (c * t + d)` whenever `a * d - b * c ≠ 0`. -/
theorem moebius_inv_moebius {𝕜 : Type*} [Field 𝕜] {a b c d t : 𝕜}
    (hdet : a * d - b * c ≠ 0) (hjt : c * t + d ≠ 0) :
    (d * ((a * t + b) / (c * t + d)) - b) / (-c * ((a * t + b) / (c * t + d)) + a) = t := by
  rw [div_eq_iff (neg_mul_moebius_add_ne_zero hdet hjt)]
  linear_combination (div_mul_cancel₀ (a * t + b) hjt)

/-- **Invariance under rational linear fractional transformations from a one-sided integer bound.**
Let `f : 𝕜 → α` be a function from a characteristic-zero field into a partial order satisfying
`f ((a t + b) / (c t + d)) ≤ f t` for every integer matrix `(a, b; c, d)` of nonzero determinant
away from its pole `c t + d = 0`. Then `f ((a t + b) / (c t + d)) = f t` for every rational matrix
`(a, b; c, d)` of nonzero determinant, including at the pole `c t + d = 0` where Lean's convention
`x / 0 = 0` sends `t = -d / c` to `0` (and `f` is constant on `ℚ` via rational translations). -/
theorem apply_mul_add_div_mul_add_eq_of_int_le
    {𝕜 α : Type*} [Field 𝕜] [CharZero 𝕜] [PartialOrder α] {f : 𝕜 → α}
    (hle : ∀ (t : 𝕜) {a b c d : ℤ}, a * d - b * c ≠ 0 → (c : 𝕜) * t + d ≠ 0 →
      f (((a : 𝕜) * t + b) / ((c : 𝕜) * t + d)) ≤ f t)
    (t : 𝕜) {a b c d : ℚ} (hdet : a * d - b * c ≠ 0) :
    f (((a : 𝕜) * t + b) / ((c : 𝕜) * t + d)) = f t := by
  suffices haway : ∀ {s : 𝕜} {a b c d : ℚ}, a * d - b * c ≠ 0 → (c : 𝕜) * s + d ≠ 0 →
      f (((a : 𝕜) * s + b) / ((c : 𝕜) * s + d)) = f s by
    by_cases ht : (c : 𝕜) * t + d = 0
    · -- At the pole `t = -d / c`, both `t` and its image `0` are rational translates of `0`.
      rw [ht, div_zero, (Rat.castHom 𝕜).eq_map_neg_div_of_map_mul_add_map_eq_zero hdet ht,
        Rat.coe_castHom]
      simpa using (haway (s := 0) (a := 1) (b := -d / c) (c := 0) (d := 1) (by simp) (by simp)).symm
    · exact haway hdet ht
  intro t a b c d hdet ht
  -- Clear denominators of `a, b, c, d` by multiplying by `m = a.den * b.den * c.den * d.den`.
  set m : ℕ := a.den * b.den * c.den * d.den
  have hm_pos : 0 < m := mul_pos (mul_pos (mul_pos a.pos b.pos) c.pos) d.pos
  have hm : (m : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
  have hint (q : ℚ) (hq : q.den ∣ m) : ∃ z : ℤ, (z : 𝕜) = m * q := by
    obtain ⟨z, hz⟩ := (Rat.den_dvd_iff_exists_mul_intCast_eq q m).1 (Int.natCast_dvd_natCast.2 hq)
    exact ⟨z, by simpa [mul_comm] using (congrArg (Rat.cast (K := 𝕜)) hz).symm⟩
  obtain ⟨a', ha'⟩ := hint a ⟨b.den * c.den * d.den, by ring⟩
  obtain ⟨b', hb'⟩ := hint b ⟨a.den * c.den * d.den, by ring⟩
  obtain ⟨c', hc'⟩ := hint c ⟨a.den * b.den * d.den, by ring⟩
  obtain ⟨d', hd'⟩ := hint d ⟨a.den * b.den * c.den, by ring⟩
  have hdet' : a' * d' - b' * c' ≠ 0 := fun h0 ↦ by
    have hK : ((a * d - b * c : ℚ) : 𝕜) ≠ 0 := Rat.cast_ne_zero.2 hdet
    push_cast at hK
    have h0K : (a' : 𝕜) * d' - b' * c' = 0 := by exact_mod_cast h0
    rw [ha', hb', hc', hd'] at h0K
    exact mul_ne_zero (pow_ne_zero 2 hm) hK (by linear_combination h0K)
  have hden : (c' : 𝕜) * t + d' = m * (c * t + d) := by rw [hc', hd']; ring
  have hnum : (a' : 𝕜) * t + b' = m * (a * t + b) := by rw [ha', hb']; ring
  have ht' : (c' : 𝕜) * t + d' ≠ 0 := by rw [hden]; exact mul_ne_zero hm ht
  have hscale :
      ((a : 𝕜) * t + b) / ((c : 𝕜) * t + d) = ((a' : 𝕜) * t + b') / ((c' : 𝕜) * t + d') := by
    rw [hden, hnum, mul_div_mul_left _ _ hm]
  rw [hscale]
  -- Apply the integer bound to `(a', b'; c', d')` and to its adjugate `(d', -b'; -c', a')`.
  refine le_antisymm (hle t hdet' ht') ?_
  set u : 𝕜 := ((a' : 𝕜) * t + b') / ((c' : 𝕜) * t + d')
  have hdetK : (a' : 𝕜) * d' - b' * c' ≠ 0 := by exact_mod_cast hdet'
  have hu : ((-c' : ℤ) : 𝕜) * u + a' ≠ 0 := by
    simpa using neg_mul_moebius_add_ne_zero hdetK ht'
  have hinv : ((d' : 𝕜) * u + (-b' : ℤ)) / (((-c' : ℤ) : 𝕜) * u + a') = t := by
    simpa [sub_eq_add_neg] using moebius_inv_moebius hdetK ht'
  have hdet_inv : d' * a' - (-b') * (-c') ≠ 0 := fun h0 ↦ hdet' (by linear_combination h0)
  have := hle u hdet_inv hu
  rwa [hinv] at this

/-- **Maps with factorized difference quotients preserve cross-ratios.** If
`φ s - φ t = κ * (s - t) / (d s * d t)` for all `s` and `t` in `S`, with `κ` and the values of `d`
on `S` nonzero, then `φ` preserves the cross-ratio `(p - r) * (q - s) / ((p - s) * (q - r))` of any
four points of `S`. Möbius transformations have difference quotients of this form. -/
theorem crossRatio_comp_eq_of_sub_eq_div {𝕜 : Type*} [Field 𝕜] {φ d : 𝕜 → 𝕜} {κ : 𝕜}
    {S : Set 𝕜} (hκ : κ ≠ 0) (hd : ∀ t ∈ S, d t ≠ 0)
    (hφ : ∀ s ∈ S, ∀ t ∈ S, φ s - φ t = κ * (s - t) / (d s * d t))
    {p q r s : 𝕜} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hs : s ∈ S) :
    (φ p - φ r) * (φ q - φ s) / ((φ p - φ s) * (φ q - φ r)) =
      (p - r) * (q - s) / ((p - s) * (q - r)) := by
  have hL : κ ^ 2 / (d p * d q * d r * d s) ≠ 0 := by
    simp [hκ, hd p hp, hd q hq, hd r hr, hd s hs]
  rw [hφ p hp r hr, hφ q hq s hs, hφ p hp s hs, hφ q hq r hr,
    ← mul_div_mul_right ((p - r) * (q - s)) _ hL]
  congr 1 <;> ring

/-- **Siegel's identity.** For `θ₁ ≠ θ₀` and `x - θ₂ y ≠ 0` in a field,
`(θ₁ - θ₂) / (θ₁ - θ₀) · (x - θ₀ y) / (x - θ₂ y) + (θ₂ - θ₀) / (θ₁ - θ₀) · (x - θ₁ y) / (x - θ₂ y)`
equals `1`. Applied to the linear factors of a binary form, it turns a Thue equation into unit
equations. -/
theorem siegel_identity {F : Type*} [Field F] {θ₀ θ₁ θ₂ x y : F} (h : θ₁ ≠ θ₀)
    (hxy : x - θ₂ * y ≠ 0) :
    (θ₁ - θ₂) / (θ₁ - θ₀) * ((x - θ₀ * y) / (x - θ₂ * y)) +
      (θ₂ - θ₀) / (θ₁ - θ₀) * ((x - θ₁ * y) / (x - θ₂ * y)) = 1 := by
  field_simp [sub_ne_zero.2 h]
  ring

/-- If `t (x - θ₂ y) = x - θ₀ y` with `θ₀ ≠ θ₂` and `y ≠ 0` in a ring without zero divisors,
then `t ≠ 1`. -/
theorem ne_one_of_mul_sub_mul_eq {R : Type*} [Ring R] [NoZeroDivisors R] {θ₀ θ₂ x y t : R}
    (h : θ₀ ≠ θ₂) (hy : y ≠ 0) (ht : t * (x - θ₂ * y) = x - θ₀ * y) : t ≠ 1 := by
  rintro rfl
  rw [one_mul, sub_right_inj] at ht
  exact h (mul_right_cancel₀ hy ht).symm

/-- If `t (x - θ₂ y) = x - θ₀ y` with `θ₀ ≠ θ₂` and `y ≠ 0`, then `x / y = (θ₀ - t θ₂) / (1 - t)`.
Thus the quotient of two linear factors at `(x, y)` determines the ratio `x / y`. -/
theorem div_eq_sub_mul_div_one_sub_of_mul_sub_mul_eq {F : Type*} [Field F] {θ₀ θ₂ x y t : F}
    (h : θ₀ ≠ θ₂) (hy : y ≠ 0) (ht : t * (x - θ₂ * y) = x - θ₀ * y) :
    x / y = (θ₀ - t * θ₂) / (1 - t) := by
  rw [div_eq_div_iff hy (sub_ne_zero.2 (ne_one_of_mul_sub_mul_eq h hy ht).symm)]
  linear_combination -ht

/-- The partial-fraction step in the inversion `w ↦ p - w⁻¹`: the pole `a` of a function at
`p - z⁻¹`, rescaled by `z ^ 2`, splits into the poles at `-(a - p)⁻¹` and `0`. -/
theorem div_sub_inv_sub_div_sq_eq_div_sub_sub_div {𝕜 : Type*} [Field 𝕜] (e : 𝕜) {a p : 𝕜}
    (hap : a ≠ p) {z : 𝕜} (hz0 : z ≠ 0) (hden : p - z⁻¹ - a ≠ 0) :
    e / (p - z⁻¹ - a) / z ^ 2 = e / (z - -(a - p)⁻¹) - e / z := by
  have hgap : a - p ≠ 0 := sub_ne_zero.mpr hap
  have hw : z - -(a - p)⁻¹ ≠ 0 := by
    intro h
    apply hden
    have hz : z = -(a - p)⁻¹ := sub_eq_zero.mp h
    rw [hz, inv_neg, inv_inv]
    ring
  rw [div_div, div_sub_div _ _ hw hz0,
    div_eq_div_iff (mul_ne_zero hden (pow_ne_zero 2 hz0)) (mul_ne_zero hw hz0)]
  field_simp
  ring

end TauCeti
