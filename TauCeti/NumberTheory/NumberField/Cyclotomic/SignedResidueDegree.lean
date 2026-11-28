/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.ResidueDegree
import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification

/-!
# Cyclotomic residue cardinalities from a signed order

Above an inert quadratic prime, relative Frobenius in a cyclotomic extension acts by the
square of the rational prime on the roots of unity. If the signed rational prime has even
order, that square has half its order. Thus the signed order gives the exponent of the
rational prime in the absolute residue-field cardinality.

This is the residue-cardinality calculation in `New.Data.IsExceptional.card_residueField`
in `grh/src/New/UpperBound/Divisibility/MarkOperator.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField

namespace Ideal

/-- Over a prime of norm `p²` not dividing the cyclotomic order `n`, the absolute norm of
`Q` is `p` to the order of `-p` modulo `n`, provided that order is even. In particular the
base prime can be any inert prime of a quadratic field. -/
theorem absNorm_eq_pow_orderOf_neg {K F : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] {n p : ℕ} [IsCyclotomicExtension {n} K F]
    (Q : Ideal (𝓞 F)) [Q.IsPrime] (v : HeightOneSpectrum (𝓞 K)) [Q.LiesOver v.asIdeal]
    (hn : (n : 𝓞 K) ∉ v.asIdeal) (hv : absNorm v.asIdeal = p ^ 2)
    (heven : Even (orderOf (-(p : ZMod n)))) :
    absNorm Q = p ^ orderOf (-(p : ZMod n)) := by
  have hn₀ : n ≠ 0 := fun h ↦ hn (by simp [h])
  have : NeZero n := ⟨hn₀⟩
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) K F
    (Set.mem_singleton n) hn₀
  have := IsCyclotomicExtension.isGalois {n} K F
  obtain ⟨σ, hσ⟩ := NumberField.exists_isArithFrobAt K Q (ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have := IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem F n hn Q
  have hfrob := hσ.autToPow_eq_absNorm hζ v hn Q
  have hd : Q.inertiaDeg (𝓞 K) = orderOf ((-(p : ZMod n)) ^ 2) := by
    rw [hζ.inertiaDeg_eq_orderOf_autToPow Q hσ, ← orderOf_units, hfrob, hv, Nat.cast_pow, neg_sq]
  have htwo := even_iff_two_dvd.mp heven
  rw [← absNorm_pow_inertiaDeg v.asIdeal Q, hv, ← pow_mul, hd,
    orderOf_pow_of_dvd two_ne_zero htwo, Nat.mul_div_cancel' htwo]

end Ideal
