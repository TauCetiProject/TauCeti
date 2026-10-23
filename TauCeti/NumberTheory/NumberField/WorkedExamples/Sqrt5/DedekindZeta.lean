/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Invariants
public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Units

/-!
# The residue of the Dedekind zeta function of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`, the
analytic class number formula reads off the residue of `ζ_K` at `s = 1` from the invariants
certified in the sibling files: the signature `(2, 0)`, the regulator `log((1 + √5)/2)`, the
class number `1`, the torsion order `2` and the discriminant `5`. The residue is
`2 log((1 + √5)/2) / √5`. This is one equation crossing the certified fundamental unit, the class
number, the discriminant and the normalisation of Mathlib's `dedekindZeta_residue`.

## Main results

* `TauCeti.NumberField.Sqrt5.dedekindZeta_residue_eq`:
  `dedekindZeta_residue K = 2 log((1 + √5)/2) / √5`.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace NumberField.Units
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- **The residue of `ζ_{ℚ(√5)}` at `s = 1`** is `2 log((1 + √5)/2) / √5`: the class number
formula `2^{r₁} (2π)^{r₂} h R / (w √|D|)` with `(r₁, r₂) = (2, 0)`, `h = 1`, `R = log φ`,
`w = 2` and `D = 5`. -/
theorem dedekindZeta_residue_eq (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    dedekindZeta_residue K = 2 * Real.log Real.goldenRatio / Real.sqrt 5 := by
  rw [dedekindZeta_residue_def, nrRealPlaces_eq_two hmin hgen, nrComplexPlaces_eq_zero hmin hgen,
    regulator_eq_log_goldenRatio hmin hgen, classNumber_eq_one hmin hgen,
    torsionOrder_eq_two hmin hgen, discr_eq_five hmin hgen]
  push_cast
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)]
  field_simp

end TauCeti.NumberField.Sqrt5
