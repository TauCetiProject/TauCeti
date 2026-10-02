/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Basic results on roots of unity

This file records a criterion for a root of unity congruent to `1` modulo an ideal to equal `1`,
and counts the square roots of unity in a domain in which `2 ≠ 0`. It also records that roots of
unity, and hence the values of a character of a finite group, are integral over `ℤ`.

## Main results

* `IsOfFinOrder.isIntegral`: a finite-order element of a commutative ring is integral over `ℤ`.
* `MonoidHom.isIntegral_coe_apply`: the values of a homomorphism from a finite group to the units
  of a commutative ring are integral over `ℤ`.

* `TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem`: in a commutative ring without zero divisors, a
  root of unity that is congruent to `1` modulo an ideal not containing its order is `1`.
* `TauCeti.card_rootsOfUnity_two`: in a domain in which `2 ≠ 0`, the group `μ₂ = {±1}` has two
  elements.
-/

public section

noncomputable section

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Every finite-order element of a commutative ring is integral over `ℤ`. -/
theorem _root_.IsOfFinOrder.isIntegral {x : R} (hx : IsOfFinOrder x) : IsIntegral ℤ x :=
  (IsPrimitiveRoot.orderOf x).isIntegral hx.orderOf_pos

/-- The values of a homomorphism from a finite group to the units of a commutative ring are
integral over `ℤ`. -/
theorem _root_.MonoidHom.isIntegral_coe_apply {G : Type*} [Group G] [Finite G] (χ : G →* Rˣ)
    (g : G) : IsIntegral ℤ ((χ g : Rˣ) : R) :=
  (((Units.coeHom R).comp χ).isOfFinOrder (isOfFinOrder_of_finite g)).isIntegral

/-- In a commutative ring without zero divisors, a root of unity that is congruent to `1` modulo an
ideal not containing its order is equal to `1`. -/
theorem eq_one_of_pow_eq_one_of_sub_one_mem [NoZeroDivisors R] {I : Ideal R} {n : ℕ}
    (hn : (n : R) ∉ I) {ζ : R} (hζ : ζ ^ n = 1) (hmem : ζ - 1 ∈ I) : ζ = 1 := by
  by_contra hne
  have hgeom : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have h := geom_sum_mul ζ n
    rw [hζ, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hres : Ideal.Quotient.mk I ζ = 1 := by
    have h : Ideal.Quotient.mk I (ζ - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_sub, map_one, sub_eq_zero] at h
  refine hn ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  have h := congrArg (Ideal.Quotient.mk I) hgeom
  rw [map_sum, map_zero] at h
  simpa [map_pow, hres] using h

/-- In a domain in which `2 ≠ 0`, the group `μ₂ = {±1}` of square roots of unity has two
elements. -/
theorem card_rootsOfUnity_two [IsDomain R] (h2 : (2 : R) ≠ 0) :
    Nat.card (rootsOfUnity 2 R) = 2 :=
  (IsPrimitiveRoot.neg_one (ringChar R) fun h ↦
    h2 (by simpa [h] using ringChar.Nat.cast_ringChar (R := R))).card_rootsOfUnity

end TauCeti
