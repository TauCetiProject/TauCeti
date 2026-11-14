/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# When nontriviality survives restriction of a valuation

A valuation of `L` restricts along a ring homomorphism `K →+* L` to a valuation of `K`. Without
extra hypotheses the restriction can collapse: the `t`-adic valuation of `K(t)` restricts to the
trivial valuation on `K`. This file records two independent mechanisms that keep the restriction
nontrivial:

1. **Integrality**: the restriction of a nontrivial valuation along an integral algebra is
   nontrivial (`Valuation.isNontrivial_comap_algebraMap`).
2. **Residue finiteness**: if the valuation ring of `v` is local with finite residue field, then
   the restriction of `v` to any infinite division ring is nontrivial
   (`Valuation.isNontrivial_comap_of_finite_residueField`), since a trivial restriction would embed
   that division ring into the finite residue field. In particular, this applies whenever the
   source division ring itself carries a nontrivial valuation
   (`Valuation.infinite_of_isNontrivial`), with no algebraicity assumption on the map.

This is restriction of the *domain*, along a ring map. It is unrelated to
`Valuation.RankOne.isNontrivial_restrict`, which restricts the *value group* of a valuation to its
value subgroup and leaves the domain alone.

## Main results

* `Valuation.isNontrivial_comap_algebraMap`: the restriction of a nontrivial valuation along an
  integral algebra is nontrivial.
* `Valuation.infinite_of_isNontrivial`: a division ring carrying a nontrivial valuation is
  infinite.
* `Valuation.isNontrivial_comap_of_finite_residueField`: the restriction of a valuation with finite
  residue field to an infinite division ring is nontrivial.

## Implementation notes

The proof of `Valuation.isNontrivial_comap_algebraMap` adapts the vanishing-sum argument of Aaron
Liu's `Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic` in
`Mathlib.RingTheory.Valuation.Algebraic`. That lemma cannot be applied directly, since it needs
the base `K` to be a field, while here `K` is only a commutative ring.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005].
-/

public section

namespace Valuation

section Integral

variable {K L Γ₀ : Type*} [CommRing K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- **The restriction of a nontrivial valuation along an integral algebra is nontrivial.** -/
theorem isNontrivial_comap_algebraMap [Algebra.IsIntegral K L] (v : Valuation L Γ₀)
    [v.IsNontrivial] : (v.comap (algebraMap K L)).IsNontrivial := by
  by_contra hcon
  -- a trivial restriction gives every nonzero value on `K` the value `1`
  have htriv (k : K) (hk : v (algebraMap K L k) ≠ 0) : v (algebraMap K L k) = 1 :=
    of_not_not fun h ↦ hcon ⟨k, hk, h⟩
  obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
  obtain ⟨p, hp, hpx⟩ := Algebra.IsIntegral.isIntegral (R := K) x
  -- in the vanishing sum `p(x) = 0`, two distinct terms share a nonzero value; their
  -- coefficients have value `1`, so two distinct powers of `v x` agree, impossible as
  -- `v x ≠ 0, 1` (adapted from `Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic`)
  rw [Polynomial.eval₂_eq_sum_range] at hpx
  obtain ⟨i, -, j, -, hij, hi, hj, heq⟩ := v.exists_map_eq_of_map_sum_eq_zero
    (Finset.self_mem_range_succ p.natDegree) (by simp [hp.coeff_natDegree, hx0])
    ((congrArg v hpx).trans (map_zero v))
  simp only [map_mul, map_pow] at hi hj heq
  rw [htriv _ (left_ne_zero_of_mul hi), htriv _ (left_ne_zero_of_mul hj), one_mul,
    one_mul] at heq
  exact hij (pow_right_injective₀ (zero_lt_iff.mpr hx0) hx1 heq)

end Integral

/-- **A division ring carrying a nontrivial valuation is infinite**: a nonzero element whose
valuation is not `1` has infinite multiplicative order, whereas in a finite division ring two
distinct powers of it would agree. -/
theorem infinite_of_isNontrivial {D Γ₀ : Type*} [DivisionRing D]
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation D Γ₀) [v.IsNontrivial] :
    Infinite D := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
  have hx : x ≠ 0 := fun h ↦ hx0 (by simp [h])
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ ↦ x ^ n)
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm heq.symm (hij.lt_or_gt.resolve_left hlt)
  have hpow : x ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i hx)
    (by rw [← pow_add, Nat.add_sub_of_le hlt.le, mul_one, heq])
  have hvpow : v x ^ (j - i) = 1 := by rw [← map_pow, hpow, map_one]
  have hk0 : j - i ≠ 0 := Nat.sub_ne_zero_of_lt hlt
  rcases hx1.lt_or_gt with hlt1 | hgt1
  · exact ((pow_le_of_le_one zero_le hlt1.le hk0).trans_lt hlt1).ne hvpow
  · exact (hgt1.trans_le (le_self_pow₀ hgt1.le hk0)).ne' hvpow

/-- **The restriction of a valuation with finite residue field to an infinite division ring is
nontrivial**: a trivial restriction sends every element into the valuation ring, and composing with
reduction embeds the division ring into the finite residue field. -/
theorem isNontrivial_comap_of_finite_residueField {D R Γ₀ : Type*} [DivisionRing D] [Infinite D]
    [CommRing R] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) [IsLocalRing v.integer]
    [Finite (IsLocalRing.ResidueField v.integer)] (f : D →+* R) :
    (v.comap f).IsNontrivial := by
  by_contra htriv
  have hmem (x : D) : f x ∈ v.integer := by
    rw [Valuation.mem_integer_iff]
    rcases eq_or_ne (v (f x)) 0 with h0 | h0
    · exact h0 ▸ zero_le
    · exact le_of_eq (of_not_not fun h1 ↦ htriv ⟨x, h0, h1⟩)
  let φ : D →+* IsLocalRing.ResidueField v.integer :=
    (IsLocalRing.residue v.integer).comp (f.codRestrict v.integer hmem)
  have := Finite.of_injective φ φ.injective
  exact not_finite D

end Valuation

end
