/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic

import Mathlib.RingTheory.Polynomial.Quotient
import TauCeti.RingTheory.Unramified.RootExtraction

/-!
# Tests for standard tamely ramified covers

These tests exercise the properties of the standard tamely ramified cover `A[x]/(x^e − f)`
(`TauCeti.standardTameCover`) asserted in Stacks, Example 58.31.4 (0EYF), on two covers of the
affine line along `f = t`, with `e = 2`.

* Over `A = ℤ_(3)[t]`, where `ℤ_(3)` is the localization of `ℤ` at a height-one prime `v`
  containing `3`, the exponent `2` is invertible. The cover `A[x]/(x² − t)` is free of rank `2`,
  its restriction `A_t[x]/(x² − t)` to `D(t)` is étale over `A_t`, and it is the integral closure
  of `A` in its localization at `t`: here `t` is a nonzerodivisor and `A/(t) ≅ ℤ_(3)` is reduced.
* Over `A = 𝔽₂[t]` the exponent `2` vanishes, so it is not invertible in `A`. The derivative `2x`
  of `x² − t` is zero, and `A_t[x]/(x² − t)` is not étale over `A_t`: a root cover that is étale
  over its base has invertible exponent
  (`TauCeti.isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C`). So the invertibility
  of `e` in Stacks' definition cannot be dropped.

## References

* [Stacks Project, Example 58.31.4](https://stacks.math.columbia.edu/tag/0EYF).
-/

public section

open IsDedekindDomain Polynomial

namespace TauCeti.Examples.StandardTameCover

variable (v : HeightOneSpectrum ℤ)

/-- *test_standard_cover_kummer*: for a height-one prime `v` of `ℤ` containing `3`, so that
`ℤ_(v)` is `ℤ_(3)`, and `A = ℤ_(v)[t]`, the standard cover `A[x]/(x² − t)` is free of rank `2`
over `A`, the cover `A_t[x]/(x² − t)` of `D(t)` is étale over `A_t`, and `A[x]/(x² − t)` is the
integral closure of `A` in its localization at `t`. -/
theorem test_standard_cover_kummer (hv : (3 : ℤ) ∈ v.asIdeal) :
    (Module.Free (Localization.AtPrime v.asIdeal)[X]
        (standardTameCover (Localization.AtPrime v.asIdeal)[X] X 2) ∧
      Module.finrank (Localization.AtPrime v.asIdeal)[X]
        (standardTameCover (Localization.AtPrime v.asIdeal)[X] X 2) = 2) ∧
    Algebra.Etale (Localization.Away (X : (Localization.AtPrime v.asIdeal)[X]))
      (standardTameCover (Localization.Away (X : (Localization.AtPrime v.asIdeal)[X]))
        (algebraMap (Localization.AtPrime v.asIdeal)[X] _ X) 2) ∧
    IsIntegralClosure (standardTameCover (Localization.AtPrime v.asIdeal)[X] X 2)
      (Localization.AtPrime v.asIdeal)[X]
      (Localization.Away (algebraMap (Localization.AtPrime v.asIdeal)[X]
        (standardTameCover (Localization.AtPrime v.asIdeal)[X] X 2) X)) := by
  have : IsReduced ((Localization.AtPrime v.asIdeal)[X] ⧸
      Ideal.span {(X : (Localization.AtPrime v.asIdeal)[X])}) := by
    have e := quotientSpanXSubCAlgEquiv (0 : Localization.AtPrime v.asIdeal)
    rw [map_zero, sub_zero] at e
    exact isReduced_of_injective e e.injective
  -- `2 ∉ v` since `3 ∈ v`, so `2` is a unit of `ℤ_(v)`, hence of `A` and of `A_t`.
  have h2v : (2 : ℤ) ∉ v.asIdeal := fun h ↦ v.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by simpa using v.asIdeal.sub_mem hv h))
  have h2 : IsUnit (2 : Localization.AtPrime v.asIdeal) := by
    simpa using (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime v.asIdeal)
      v.asIdeal 2).mpr h2v
  refine ⟨standardTameCover_free _ X 2 one_le_two,
    standardTameCover_etale (IsLocalization.Away.algebraMap_isUnit X) ?_,
    standardTameCover_isIntegralClosure (f := X) (e := 2)
      (X_mem_nonZeroDivisors (R := Localization.AtPrime v.asIdeal)) two_ne_zero _⟩
  have := (h2.map C).map
    (algebraMap _ (Localization.Away (X : (Localization.AtPrime v.asIdeal)[X])))
  rwa [map_ofNat, map_ofNat, ← Nat.cast_ofNat] at this

/-- *test_standard_cover_inseparable*: for `A = 𝔽₂[t]` and `e = 2`, the exponent `2` is not
invertible in `A`, the derivative `2x` of `x² − t` vanishes over `A_t`, and the cover
`A_t[x]/(x² − t)` of `D(t)` is not étale over `A_t`. -/
theorem test_standard_cover_inseparable :
    ¬ IsUnit ((2 : ℕ) : (ZMod 2)[X]) ∧
      derivative (X ^ 2 - C (algebraMap (ZMod 2)[X] (Localization.Away (X : (ZMod 2)[X])) X)) =
        0 ∧
      ¬ Algebra.Etale (Localization.Away (X : (ZMod 2)[X]))
        (standardTameCover (Localization.Away (X : (ZMod 2)[X]))
          (algebraMap (ZMod 2)[X] _ X) 2) := by
  have : Nontrivial (Localization.Away (X : (ZMod 2)[X])) :=
    (IsLocalization.injective (M := Submonoid.powers (X : (ZMod 2)[X]))
      (Localization.Away (X : (ZMod 2)[X]))
      (Submonoid.powers_le.mpr X_mem_nonZeroDivisors)).nontrivial
  -- `2` is zero in every `𝔽₂`-algebra.
  have h2 (B : Type) [CommRing B] [Algebra (ZMod 2) B] : (2 : B) = 0 := by
    rw [← map_ofNat (algebraMap (ZMod 2) B), (by decide : (2 : ZMod 2) = 0), map_zero]
  refine ⟨by simp [h2], by simp [one_add_one_eq_two, h2], fun _ ↦ ?_⟩
  have := isUnit_natCast_of_formallyUnramified_adjoinRoot_X_pow_sub_C
    (algebraMap (ZMod 2)[X] (Localization.Away (X : (ZMod 2)[X])) X) two_ne_zero
  rw [Nat.cast_ofNat, h2] at this
  exact not_isUnit_zero this

end TauCeti.Examples.StandardTameCover
