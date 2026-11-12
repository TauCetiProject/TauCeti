/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Centres of valuations on subrings

A valuation of a ring `K` that is bounded by `1` on the image of a commutative `R`-algebra map
`R → K` determines a prime ideal of `R`: the elements whose images have value strictly below `1`.
When `K` is the fraction field of `R` and the valuation is nontrivial, this centre is nonzero. The
value group may be any linearly ordered commutative group with zero.

## Main definitions and results

* `Valuation.centerIdeal`: the prime centre of a valuation bounded by `1` on `R`.
* `Valuation.mem_centerIdeal`: membership is equivalent to valuation strictly below `1`.
* `Valuation.notMem_centerIdeal_iff`: off the centre, the valuation takes the value `1`.
* `Valuation.centerIdeal_ne_bot`: a nontrivial valuation of the fraction field has nonzero centre.
* `Valuation.heightOneSpectrum`: the nonzero prime centre bundled as `HeightOneSpectrum R`.
  This structure records a nonzero prime ideal; it is a height one prime when `R` is Dedekind.
* `Valuation.asIdeal_heightOneSpectrum`: the underlying ideal is the centre ideal.
-/

public section

open IsDedekindDomain

namespace Valuation

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section CenterIdeal

variable {K : Type*} [Ring K] [Algebra R K] {w : _root_.Valuation K Γ₀}

variable (R) in
/-- The **centre** on `R` of a valuation `w` of `K` that is bounded by `1` on the image of `R`:
the ideal of elements of `R` whose images have valuation strictly below `1`. It is prime
(`Valuation.isPrime_centerIdeal`), and it is nonzero as soon as `w` is nontrivial and `K` is the
fraction field of `R` (`Valuation.centerIdeal_ne_bot`). -/
def centerIdeal (w : _root_.Valuation K Γ₀) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    Ideal R where
  carrier := {r | w (algebraMap R K r) < 1}
  add_mem' {a b} ha hb := by
    simpa only [Set.mem_ofPred_eq, map_add] using (w.map_add _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c r hr := by
    simpa only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] using
      (mul_le_of_le_one_left' (hR c)).trans_lt hr

/-- An element belongs to the centre ideal exactly when its valuation is strictly below `1`. -/
@[simp]
theorem mem_centerIdeal {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∈ centerIdeal R w hR ↔ w (algebraMap R K r) < 1 :=
  Iff.rfl

/-- Off its centre, and only there, a valuation bounded by `1` on `R` takes the value `1`. -/
theorem notMem_centerIdeal_iff {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∉ centerIdeal R w hR ↔ w (algebraMap R K r) = 1 := by
  rw [mem_centerIdeal, not_lt, le_antisymm_iff, and_iff_right (hR r)]

/-- The centre of a valuation bounded by `1` on `R` is a prime ideal of `R`. -/
theorem isPrime_centerIdeal (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (centerIdeal R w hR).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨fun h ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · simpa using (Ideal.eq_top_iff_one _).mp h
  · by_contra! h
    rw [mem_centerIdeal, map_mul, map_mul, notMem_centerIdeal_iff.mp h.1,
      notMem_centerIdeal_iff.mp h.2, mul_one] at hxy
    exact hxy.false

end CenterIdeal

variable {K : Type*} [Field K] [Algebra R K] {w : _root_.Valuation K Γ₀}

/-- The centre of a nontrivial valuation of the fraction field `K` of `R` is a nonzero ideal of
`R`: an element of `K` of value below `1` is a fraction `a / b` whose numerator `a` is a nonzero
element of the centre. -/
theorem centerIdeal_ne_bot [IsFractionRing R K] [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : centerIdeal R w hR ≠ ⊥ := by
  obtain ⟨y, hy0, hy1⟩ := IsNontrivial.exists_lt_one (v := w)
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) y
  refine (Submodule.ne_bot_iff _).mpr ⟨a, ?_, ?_⟩
  · rw [mem_centerIdeal, ← hab, map_mul]
    exact (mul_le_of_le_one_right' (hR b)).trans_lt hy1
  · rintro rfl
    exact hy0 ((IsLocalization.map_units K b).mul_left_eq_zero.mp (hab.trans (map_zero _)))

variable [IsFractionRing R K]

variable (R) in
/-- The nonzero prime centre of a nontrivial valuation of `K` bounded by `1` on `R`, bundled
as a `HeightOneSpectrum R`. This is a height one prime when `R` is a Dedekind domain. -/
def heightOneSpectrum (w : _root_.Valuation K Γ₀) [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : HeightOneSpectrum R where
  asIdeal := centerIdeal R w hR
  isPrime := isPrime_centerIdeal hR
  ne_bot := centerIdeal_ne_bot hR

-- Parenthesize `rfl` to avoid inferred `@[defeq]`, which would require exposing the definition.
/-- The underlying ideal of `heightOneSpectrum` is the centre ideal. -/
@[simp]
theorem asIdeal_heightOneSpectrum [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (heightOneSpectrum R w hR).asIdeal = centerIdeal R w hR := (rfl)

end Valuation
