/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FractionalIdeal.Trace
public import TauCeti.RingTheory.DedekindDomain.Different.Trace
import TauCeti.FieldTheory.Separable.FractionRing.Basic
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Traces of fractional powers of the maximal ideal

In a finite extension of discrete valuation rings with separable fraction fields, the trace
of the `m`-th power of the maximal ideal is the power with exponent `⌊(m + d) / e⌋`, where
`d` is the different exponent and `e` the ramification index. The exponent `m` can be negative.
Euclidean division by `e` reduces the computation to the integral trace formula
`TauCeti.map_intTrace_pow_eq_maximalIdeal_pow` and linearity over the base field.

Reference: Serre, *Local Fields*, Chapter III, §3, Proposition 7.
-/

public section

open IsLocalRing FractionalIdeal
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (A B K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field K] [Field L]
  [Algebra A B] [Algebra A K] [Algebra K L] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [IsFractionRing A K] [IsFractionRing B L]
  [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra.IsSeparable K L]

/-- The trace of any integer power of the maximal ideal of `B`, as a fractional ideal of `A`.
Integer division by the positive ramification index rounds down. -/
@[simp]
theorem trace_maximalIdeal_zpow (m : ℤ) :
    ((maximalIdeal B : FractionalIdeal B⁰ L) ^ m).trace A K =
      (maximalIdeal A : FractionalIdeal A⁰ K) ^
        ((m + multiplicity (maximalIdeal B) (differentIdeal A B)) /
          (maximalIdeal B).ramificationIdx A) := by
  have := isSeparable_fractionRing_of_isFractionRing A B K L
  let e := (maximalIdeal B).ramificationIdx A
  let d := multiplicity (maximalIdeal B) (differentIdeal A B)
  let P : FractionalIdeal B⁰ L := maximalIdeal B
  let p : FractionalIdeal A⁰ K := maximalIdeal A
  have he : (e : ℤ) ≠ 0 := by exact_mod_cast ((maximalIdeal B).ramificationIdx_pos A).ne'
  have hP : P ≠ 0 := coeIdeal_ne_zero.mpr (_root_.IsDiscreteValuationRing.not_a_field B)
  have hp : p ≠ 0 := coeIdeal_ne_zero.mpr (_root_.IsDiscreteValuationRing.not_a_field A)
  have hmap := IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx
    (Ideal.map_ne_bot_of_ne_bot (S := B) (_root_.IsDiscreteValuationRing.not_a_field A))
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
  let t := algebraMap A K π
  have ht : p = spanSingleton A⁰ t := by
    simp only [p, t, hπ.maximalIdeal_eq, coeIdeal_span_singleton]
  have htL : P ^ e = spanSingleton B⁰ (algebraMap K L t) := by
    simp only [P, e, ← coeIdeal_pow, ← hmap, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, coeIdeal_span_singleton, t, ← IsScalarTower.algebraMap_apply]
  let q := m / e
  let n := (m % e).toNat
  have hn : (n : ℤ) = m % e := Int.toNat_of_nonneg (Int.emod_nonneg _ he)
  have hm : m = (e : ℤ) * q + n := by
    rw [hn, add_comm]
    exact (Int.emod_add_mul_ediv ..).symm
  have hdiv : (m + d) / e = q + ((n + d) / e : ℕ) := by
    calc
      _ = ((↑(n + d) : ℤ) + e * q) / e := by push_cast; congr 1; omega
      _ = _ := by rw [Int.add_mul_ediv_left _ _ he, Int.natCast_ediv, add_comm]
  have hint : (P ^ n).trace A K = p ^ ((n + d) / e) := by
    simp only [P, p, e, d, ← coeIdeal_pow, trace_coeIdeal,
      map_intTrace_pow_eq_maximalIdeal_pow A (_root_.IsDiscreteValuationRing.not_a_field B) hmap]
  calc
    (P ^ m).trace A K =
        (spanSingleton B⁰ (algebraMap K L (t ^ q)) * P ^ n).trace A K := by
      rw [hm, zpow_add₀ hP]
      simp only [zpow_mul, zpow_natCast, htL, map_zpow₀]
    _ = spanSingleton A⁰ (t ^ q) * p ^ ((n + d) / e) := by rw [trace_spanSingleton_mul, hint]
    _ = p ^ ((m + d) / e) := by rw [hdiv, zpow_add₀ hp, zpow_natCast, map_zpow₀, ← ht]

end TauCeti
