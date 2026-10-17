/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.NumberTheory.NumberField.SUnits.Lattice

/-!
# The S-regulator

For a finite set `S` of finite places of a number field `K`, the `S`-regulator is the covolume
of the full `S`-unit lattice. The full-lattice instances come from
`TauCeti.NumberTheory.NumberField.SUnits.Lattice`; positivity is the general positivity theorem
for lattice covolumes. This is the `S`-analogue of Mathlib's `NumberField.Units.regulator`.

## Main definitions and results

* `TauCeti.NumberField.SUnit.regulator`: the covolume of the `S`-unit lattice.
* `TauCeti.NumberField.SUnit.regulator_pos`: the `S`-regulator is positive.
* `TauCeti.NumberField.SUnit.regulator_ne_zero`: the `S`-regulator is nonzero.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.5 (the `S`-unit theorem 1.5.13).
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))

open Classical in
/-- The `S`-regulator is the covolume of the `S`-unit lattice. -/
def regulator : ℝ := ZLattice.covolume (unitLattice S)

/-- The `S`-regulator is positive. -/
theorem regulator_pos : 0 < regulator S := by
  classical
  exact ZLattice.covolume_pos _ _

/-- The `S`-regulator is nonzero. -/
theorem regulator_ne_zero : regulator S ≠ 0 :=
  (regulator_pos S).ne'

end TauCeti.NumberField.SUnit
