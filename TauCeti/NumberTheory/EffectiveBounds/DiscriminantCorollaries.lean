/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.Discriminant

/-!
# Consumer forms of the effective discriminant bound

The EffectiveBounds roadmap's Layer 1 discriminant target gives the rational estimate

`|NumberField.discr K| ≤ |Algebra.discr ℚ b|`

for every `ℚ`-basis `b` of algebraic integers. Concrete trace-form computations usually evaluate
the basis discriminant as an integer and then carry a natural-number bound, for example in the
roadmap's `ℚ(i)` worked example. This file records those conversion forms so later estimates can
reuse the migrated discriminant theorem without redoing coercion bookkeeping.

## Main results

* `TauCeti.NumberField.abs_discr_le_of_basis_isIntegral_of_abs_discr_le`: a monotone rational
  bound from an external bound on the basis discriminant.
* `TauCeti.NumberField.natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int`: if the basis
  discriminant computes to an integer `d`, then `(NumberField.discr K).natAbs ≤ d.natAbs`.
* `TauCeti.NumberField.natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le`: the same
  with a separate natural-number upper bound.
* `TauCeti.NumberField.natAbs_discr_le_of_basis_isIntegral_of_discr_eq_nat`: the nonnegative
  integer specialization.

No formal code is vendored. These are direct API corollaries of the migrated Layer 1 bound
`TauCeti.NumberField.abs_discr_le_of_basis_isIntegral`, whose source attribution is in
`TauCeti/NumberTheory/EffectiveBounds/Discriminant.lean`.
-/

public section

open Module

namespace TauCeti.NumberField

/-- If the discriminant of an algebraic-integer basis is bounded by `B`, then the number-field
discriminant is bounded by the same rational number. -/
theorem abs_discr_le_of_basis_isIntegral_of_abs_discr_le {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℚ}
    (hB : |Algebra.discr ℚ (b : ι → K)| ≤ B) :
    |(NumberField.discr K : ℚ)| ≤ B :=
  (abs_discr_le_of_basis_isIntegral b hb).trans hB

/-- If the trace-form discriminant of an algebraic-integer basis computes to the integer `d`, then
the natural absolute discriminant of the number field is at most `d.natAbs`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    (NumberField.discr K).natAbs ≤ d.natAbs := by
  have hq : |(NumberField.discr K : ℚ)| ≤ |(d : ℚ)| := by
    simpa [hdisc] using abs_discr_le_of_basis_isIntegral b hb
  rw [← Nat.cast_le (α := ℤ), Nat.cast_natAbs, Nat.cast_natAbs]
  exact_mod_cast hq

/-- If the trace-form discriminant of an algebraic-integer basis computes to the integer `d`, and
`d.natAbs ≤ D`, then `(NumberField.discr K).natAbs ≤ D`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) (hd : d.natAbs ≤ D) :
    (NumberField.discr K).natAbs ≤ D :=
  (natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int b hb hdisc).trans hd

/-- If the trace-form discriminant of an algebraic-integer basis computes to the natural number
`D`, then `(NumberField.discr K).natAbs ≤ D`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_nat
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (D : ℚ)) :
    (NumberField.discr K).natAbs ≤ D := by
  exact natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    b hb (d := (D : ℤ)) (by simpa using hdisc) (by simp)

/-- If the trace-form discriminant of an algebraic-integer basis computes to an integer `d` with
`d.natAbs ≤ D`, the same natural-number discriminant bound may be read as an integer absolute-value
bound. -/
theorem abs_discr_le_int_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) (hd : d.natAbs ≤ D) :
    |NumberField.discr K| ≤ (D : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast
    natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le b hb hdisc hd

end TauCeti.NumberField
