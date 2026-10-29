/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Model
public import Mathlib.NumberTheory.NumberField.ClassNumber

import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv

/-!
# The class number of `ℚ(√d)` from its integral model

For a squarefree nonsquare integer `d`, the ring of integers of the model `QuadraticAlgebra ℚ d 0`
of `ℚ(√d)` is identified with an explicit integral quadratic algebra: `ℤ[√d]` when `d ≢ 1 (mod 4)`
(`QuadraticAlgebra.ringOfIntegersEquiv`) and `ℤ[(1 + √d)/2]` when `d ≡ 1 (mod 4)`
(`QuadraticAlgebra.ringOfIntegersEquivHalf`). Along these ring isomorphisms the class group of
`ℚ(√d)` is identified with the ideal class group of the integral model by `ClassGroup.mulEquiv`, so
the class number of `ℚ(√d)` is the number of ideal classes of `ℤ[√d]`, respectively of
`ℤ[(1 + √d)/2]`.

The integral models are domains because they are isomorphic to a ring of integers; this is the
`IsDomain` instance used to form their class groups below. Combined with
`RingEquiv.classNumber_eq` and `NumberField.nonempty_algEquiv_quadraticAlgebra`, they identify the
class number of any quadratic field presented by a squarefree radicand `d` with the number of ideal
classes of the integral model of `d`.

## Main results

* `QuadraticAlgebra.natCard_classGroup_eq_classNumber_of_mod_four_ne_one`: for `d ≢ 1 (mod 4)`,
  `ℤ[√d]` has `classNumber ℚ(√d)` ideal classes.
* `QuadraticAlgebra.natCard_classGroup_eq_classNumber_of_mod_four_eq_one`: for `d ≡ 1 (mod 4)`,
  `ℤ[(1 + √d)/2]` has `classNumber ℚ(√d)` ideal classes.
-/

public section

open NumberField

namespace QuadraticAlgebra

variable {d : ℤ} [Fact (¬ IsSquare d)] (hsf : Squarefree d)

/-- **The class number of `ℚ(√d)` for `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1`, the
ideal class group of `ℤ[√d] = QuadraticAlgebra ℤ d 0` has `classNumber ℚ(√d)` elements: it is
identified with the class group of `ℚ(√d)` by `ClassGroup.mulEquiv` of `ringOfIntegersEquiv`. -/
theorem natCard_classGroup_eq_classNumber_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    haveI := (ringOfIntegersEquiv hsf hd4).symm.toMulEquiv.isDomain
    Nat.card (ClassGroup (QuadraticAlgebra ℤ d 0)) =
      classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) :=
  haveI := (ringOfIntegersEquiv hsf hd4).symm.toMulEquiv.isDomain
  (ringOfIntegersEquiv hsf hd4).symm.toRingEquiv.natCard_classGroup_eq_classNumber

/-- **The class number of `ℚ(√d)` for `d ≡ 1 (mod 4)`.** For squarefree `d` with `d % 4 = 1`, the
ideal class group of `ℤ[(1 + √d)/2] = QuadraticAlgebra ℤ ((d - 1) / 4) 1` has `classNumber ℚ(√d)`
elements: it is identified with the class group of `ℚ(√d)` by `ClassGroup.mulEquiv` of
`ringOfIntegersEquivHalf`. -/
theorem natCard_classGroup_eq_classNumber_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    haveI := (ringOfIntegersEquivHalf hsf hd4).symm.toMulEquiv.isDomain
    Nat.card (ClassGroup (QuadraticAlgebra ℤ ((d - 1) / 4) 1)) =
      classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) :=
  haveI := (ringOfIntegersEquivHalf hsf hd4).symm.toMulEquiv.isDomain
  (ringOfIntegersEquivHalf hsf hd4).symm.toRingEquiv.natCard_classGroup_eq_classNumber

end QuadraticAlgebra
