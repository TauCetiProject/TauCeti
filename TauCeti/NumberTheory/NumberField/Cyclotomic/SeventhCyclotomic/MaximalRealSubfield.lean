/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant
import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield

/-!
# The maximal real subfield of a seventh cyclotomic field

Let `L` be a seventh cyclotomic field over `ℚ`. Its maximal real subfield `L⁺`, classically
written `ℚ(ζ₇ + ζ₇⁻¹)`, is a cubic field of discriminant `49`, and it has class
number one.

The degree of `L⁺` is `φ(7) / 2 = 3`
(`TauCeti.IsCyclotomicExtension.Rat.finrank_maximalRealSubfield`).
The discriminant is computed without an integral basis of `L⁺`. The tower formula
`|d_L| = N(𝔇_{L/L⁺}) · |d_{L⁺}|²` with `|d_L| = 7⁵` shows that `|d_{L⁺}|` is a power of `7`
whose square divides `7⁵`, so it is `1`, `7` or `49`. Minkowski's lower bound
`|d_{L⁺}| ≥ (3³/3!)² = 81/4` for a totally real cubic field leaves `49`. Minkowski's bound
`(3!/3³) · √49 = 14/9 < 2` then gives class number one
(`TauCeti.NumberField.isPrincipalIdealRing_of_finrank_eq_three_of_natAbs_discr_le_forty_nine`).

## Main results

* `TauCeti.NumberField.natAbs_discr_maximalRealSubfield_seven`: `|d_{L⁺}| = 49`.
* `TauCeti.NumberField.classNumber_maximalRealSubfield_seven`: `L⁺` has class number one.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2 and Chapter 11 §1.
-/

public section

open NumberField Module

namespace TauCeti.NumberField

variable (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {7} ℚ L]

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A seventh cyclotomic field over `ℚ` is a CM field. -/
private theorem isCMField_seven : IsCMField L :=
  IsCyclotomicExtension.Rat.isCMField L ⟨7, Set.mem_singleton 7, by norm_num⟩

/-- The maximal real subfield of `ℚ(ζ₇)` is cubic. -/
private theorem finrank_maximalRealSubfield_seven : finrank ℚ (maximalRealSubfield L) = 3 := by
  rw [IsCyclotomicExtension.Rat.finrank_maximalRealSubfield 7 L (by norm_num)]
  decide

/-- **The maximal real subfield of `ℚ(ζ₇)` has discriminant `49`.** -/
theorem natAbs_discr_maximalRealSubfield_seven :
    (discr (maximalRealSubfield L)).natAbs = 49 := by
  have := isCMField_seven L
  set d := (discr (maximalRealSubfield L)).natAbs
  -- The tower formula: `d²` divides `|d_L| = 7⁵`.
  have hdvd : d ^ 2 ∣ 7 ^ 5 := by
    have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      (maximalRealSubfield L) (𝓞 (maximalRealSubfield L)) L (𝓞 L)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L,
      IsCyclotomicExtension.Rat.discr_prime 7 L] at h
    exact ⟨_, by rw [mul_comm]; simpa using h⟩
  obtain ⟨i, hi, hd⟩ :=
    (Nat.dvd_prime_pow (by norm_num)).1 ((dvd_pow_self d two_ne_zero).trans hdvd)
  -- Minkowski's lower bound for a totally real cubic field: `81 / 4 ≤ d`.
  have hge : (81 / 4 : ℝ) ≤ d := by
    have h := abs_discr_ge' (maximalRealSubfield L)
    rw [finrank_maximalRealSubfield_seven, IsTotallyReal.nrComplexPlaces_eq_zero] at h
    norm_num [Nat.factorial] at h
    rw [Nat.cast_natAbs, Int.cast_abs]
    linarith
  rw [hd] at hge hdvd ⊢
  interval_cases i
  · norm_num at hge
  · norm_num at hge
  · rfl
  all_goals exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

/-- **The maximal real subfield of `ℚ(ζ₇)` has class number one.** -/
theorem classNumber_maximalRealSubfield_seven : classNumber (maximalRealSubfield L) = 1 :=
  classNumber_eq_one_iff.2 <| isPrincipalIdealRing_of_finrank_eq_three_of_natAbs_discr_le_forty_nine
    (finrank_maximalRealSubfield_seven L) (natAbs_discr_maximalRealSubfield_seven L).le

end TauCeti.NumberField
