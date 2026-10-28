/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Model
public import Mathlib.NumberTheory.NumberField.ClassNumber

import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv
import TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant

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

The same ring isomorphisms specialize the Dedekind equivalences *class number one ⇔ principal ideal
domain ⇔ unique factorization domain* to the integral models: `ℚ(√d)` has class number `1` exactly
when `ℤ[√d]`, respectively `ℤ[(1 + √d)/2]`, is a principal ideal domain, and exactly when it is a
unique factorization domain. Minkowski's bound certifies class number `1` for the radicands with
`|discr| ≤ 9`, namely `d = -1, ±2` with `d ≢ 1 (mod 4)` and `d = -3, 5, -7` with `d ≡ 1 (mod 4)`.

## Main results

* `QuadraticAlgebra.natCard_classGroup_eq_classNumber_of_mod_four_ne_one`: for `d ≢ 1 (mod 4)`,
  `ℤ[√d]` has `classNumber ℚ(√d)` ideal classes.
* `QuadraticAlgebra.natCard_classGroup_eq_classNumber_of_mod_four_eq_one`: for `d ≡ 1 (mod 4)`,
  `ℤ[(1 + √d)/2]` has `classNumber ℚ(√d)` ideal classes.
* `QuadraticAlgebra.classNumber_eq_one_iff_isPrincipalIdealRing_of_mod_four_ne_one`,
  `QuadraticAlgebra.classNumber_eq_one_iff_uniqueFactorizationMonoid_of_mod_four_ne_one` and their
  `_of_mod_four_eq_one` analogues: class number one of `ℚ(√d)` is principality, respectively
  unique factorization, of its integral model.
* `QuadraticAlgebra.classNumber_eq_one_of_mod_four_ne_one_of_natAbs_le_two`,
  `QuadraticAlgebra.classNumber_eq_one_of_mod_four_eq_one_of_natAbs_le_nine`: the Minkowski
  certificates for the radicands of discriminant at most `9` in absolute value.
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

include hsf in
/-- **Class number one of `ℚ(√d)` is principality of `ℤ[√d]`.** For squarefree `d` with
`d % 4 ≠ 1`, the class number of `ℚ(√d)` is `1` exactly when `ℤ[√d]` is a principal ideal ring. -/
theorem classNumber_eq_one_iff_isPrincipalIdealRing_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 ↔
      IsPrincipalIdealRing (QuadraticAlgebra ℤ d 0) :=
  (ringOfIntegersEquiv hsf hd4).symm.toRingEquiv.classNumber_eq_one_iff_isPrincipalIdealRing

include hsf in
/-- **Class number one of `ℚ(√d)` is unique factorization in `ℤ[√d]`.** For squarefree `d` with
`d % 4 ≠ 1`, the class number of `ℚ(√d)` is `1` exactly when `ℤ[√d]` is a unique factorization
domain. -/
theorem classNumber_eq_one_iff_uniqueFactorizationMonoid_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 ↔
      UniqueFactorizationMonoid (QuadraticAlgebra ℤ d 0) :=
  (ringOfIntegersEquiv hsf hd4).symm.toRingEquiv.classNumber_eq_one_iff_uniqueFactorizationMonoid

include hsf in
/-- **Class number one of `ℚ(√d)` is principality of `ℤ[(1 + √d)/2]`.** For squarefree `d` with
`d % 4 = 1`, the class number of `ℚ(√d)` is `1` exactly when `ℤ[(1 + √d)/2]` is a principal
ideal ring. -/
theorem classNumber_eq_one_iff_isPrincipalIdealRing_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 ↔
      IsPrincipalIdealRing (QuadraticAlgebra ℤ ((d - 1) / 4) 1) :=
  (ringOfIntegersEquivHalf hsf hd4).symm.toRingEquiv.classNumber_eq_one_iff_isPrincipalIdealRing

include hsf in
/-- **Class number one of `ℚ(√d)` is unique factorization in `ℤ[(1 + √d)/2]`.** For squarefree
`d` with `d % 4 = 1`, the class number of `ℚ(√d)` is `1` exactly when `ℤ[(1 + √d)/2]` is a unique
factorization domain. -/
theorem classNumber_eq_one_iff_uniqueFactorizationMonoid_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 ↔
      UniqueFactorizationMonoid (QuadraticAlgebra ℤ ((d - 1) / 4) 1) :=
  RingEquiv.classNumber_eq_one_iff_uniqueFactorizationMonoid
    (ringOfIntegersEquivHalf hsf hd4).symm.toRingEquiv

include hsf in
/-- **Minkowski certificate for `d ≢ 1 (mod 4)`.** For squarefree `d` with `d % 4 ≠ 1` and
`|d| ≤ 2`, that is `d = -1, 2, -2`, the field `ℚ(√d)` of discriminant `4d` has class number `1`:
`|4d| ≤ 9` lies below the quadratic Minkowski threshold. -/
theorem classNumber_eq_one_of_mod_four_ne_one_of_natAbs_le_two (hd4 : d % 4 ≠ 1)
    (hd : d.natAbs ≤ 2) : classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 :=
  classNumber_eq_one_iff.mpr <|
    TauCeti.NumberField.isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine
      (QuadraticAlgebra.finrank_eq_two _ _)
      (by rw [discr_eq_four_mul_of_mod_four_ne_one hsf hd4]; omega)

include hsf in
/-- **Minkowski certificate for `d ≡ 1 (mod 4)`.** For squarefree `d` with `d % 4 = 1` and
`|d| ≤ 9`, that is `d = -3, 5, -7`, the field `ℚ(√d)` of discriminant `d` has class number `1`:
`|d| ≤ 9` lies below the quadratic Minkowski threshold. -/
theorem classNumber_eq_one_of_mod_four_eq_one_of_natAbs_le_nine (hd4 : d % 4 = 1)
    (hd : d.natAbs ≤ 9) : classNumber (QuadraticAlgebra ℚ (d : ℚ) 0) = 1 :=
  classNumber_eq_one_iff.mpr <|
    TauCeti.NumberField.isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine
      (QuadraticAlgebra.finrank_eq_two _ _) (by rwa [discr_eq_of_mod_four_eq_one hsf hd4])

end QuadraticAlgebra
