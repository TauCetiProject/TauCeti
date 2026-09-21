/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Centres of valuations on subrings

A valuation of a field `K` that is bounded by `1` on a commutative ring `R` determines a prime
ideal of `R`: the elements whose images have value strictly below `1`. When `K` is the fraction
field of `R` and the valuation is nontrivial, this centre is nonzero.

## Main definitions and results

* `Valuation.centerIdeal`: the prime centre of a valuation bounded by `1` on `R`.
* `Valuation.mem_centerIdeal`: membership is equivalent to valuation strictly below `1`.
* `Valuation.centerIdeal_ne_bot`: a nontrivial valuation of the fraction field has nonzero centre.
* `Valuation.heightOneSpectrum`: the nonzero prime centre bundled as `HeightOneSpectrum R`.
  This structure records a nonzero prime ideal; it is a height one prime when `R` is Dedekind.
* `Valuation.asIdeal_heightOneSpectrum`: the underlying ideal is the centre ideal.

## Implementation notes

The definitions keep their bodies unexposed. The characterization lemmas `Valuation.mem_centerIdeal`
and `Valuation.asIdeal_heightOneSpectrum` provide the interface. The latter's definitional proof
is parenthesized (`(rfl)`) so that it is not inferred to be `@[defeq]`, which would require the body
to be exposed.
-/

public section

open scoped WithZero

open IsDedekindDomain

namespace Valuation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  {w : _root_.Valuation K ℤᵐ⁰}

section CenterIdeal

variable (R) in
/-- The **centre** on `R` of a valuation `w` of `K` whose valuation ring contains `R`: the ideal
of elements of `R` of positive valuation. It is prime (`Valuation.isPrime_centerIdeal`), and it is
nonzero as soon as `w` is nontrivial and `K` is the fraction field of `R`
(`Valuation.centerIdeal_ne_bot`). -/
def centerIdeal (w : _root_.Valuation K ℤᵐ⁰) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    Ideal R :=
  (IsLocalRing.maximalIdeal w.valuationSubring).comap
    ((algebraMap R K).codRestrict w.valuationSubring fun r ↦
      (w.mem_valuationSubring_iff _).mpr (hR r))

/-- An element belongs to the centre ideal exactly when its valuation is strictly below `1`. -/
@[simp]
theorem mem_centerIdeal {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∈ centerIdeal R w hR ↔ w (algebraMap R K r) < 1 := by
  rw [centerIdeal, Ideal.mem_comap, w.mem_maximalIdeal_iff]
  rfl

/-- Off its centre, a valuation bounded by `1` on `R` takes the value `1`. -/
theorem eq_one_of_notMem_centerIdeal {r : R} (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (hr : r ∉ centerIdeal R w hR) : w (algebraMap R K r) = 1 :=
  le_antisymm (hR r) (not_lt.mp (mt mem_centerIdeal.mpr hr))

/-- The centre of a valuation bounded by `1` on `R` is a prime ideal of `R`. -/
theorem isPrime_centerIdeal (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (centerIdeal R w hR).IsPrime :=
  (IsLocalRing.maximalIdeal w.valuationSubring).comap_isPrime _

/-- The centre of a nontrivial valuation of the fraction field `K` of `R` is a nonzero ideal of
`R`: an element of `K` of value below `1` is a fraction `a / b` whose numerator `a` is a nonzero
element of the centre. -/
theorem centerIdeal_ne_bot [IsFractionRing R K] [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : centerIdeal R w hR ≠ ⊥ := by
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := w)
  obtain ⟨ab, hab⟩ := IsLocalization.surj (nonZeroDivisors R) y
  have hb : algebraMap R K (ab.2 : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ab.2.2
  have ha0 : ab.1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hab
    exact (mul_eq_zero.mp hab).elim hy0 hb
  have hmem : ab.1 ∈ centerIdeal R w hR := by
    rw [mem_centerIdeal]
    calc w (algebraMap R K ab.1) = w (y * algebraMap R K (ab.2 : R)) := by rw [hab]
      _ = w y * w (algebraMap R K (ab.2 : R)) := w.map_mul _ _
      _ ≤ w y * 1 := mul_le_mul_right (hR ab.2) _
      _ < 1 := by simpa using hy1
  exact fun h ↦ ha0 (by simpa [h] using hmem)

end CenterIdeal

variable [IsFractionRing R K]

variable (R) in
/-- The nonzero prime centre of a nontrivial valuation of `K` bounded by `1` on `R`, bundled
as a `HeightOneSpectrum R`. This is a height one prime when `R` is a Dedekind domain. -/
def heightOneSpectrum (w : _root_.Valuation K ℤᵐ⁰) [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : HeightOneSpectrum R where
  asIdeal := centerIdeal R w hR
  isPrime := isPrime_centerIdeal hR
  ne_bot := centerIdeal_ne_bot hR

/-- The underlying ideal of `heightOneSpectrum` is the centre ideal. -/
@[simp]
theorem asIdeal_heightOneSpectrum [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (heightOneSpectrum R w hR).asIdeal = centerIdeal R w hR := (rfl)

end Valuation
