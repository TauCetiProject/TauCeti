/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Cyclic.Automorphism
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.Tactic.Abel

/-!
# Group cohomology of the cyclic representation of an automorphism of finite order

Let `T` be an additive commutative group, `m > 0`, and `A : T ≃+ T` an additive automorphism of
order dividing `m`, that is `A^[m] = id`. Then the cyclic group `C_m = Multiplicative (ZMod m)`
acts on `T` with its standard generator `ofAdd 1` acting by `A`; this is the integral
representation `AddEquiv.cyclicRep A hA : Rep ℤ C_m`. Its norm `N = ∑ g, ρ g` is the ordered sum
of powers `∑ j < m, A^j` (`AddEquiv.cyclicRepresentation_norm_apply`).

The group cohomology of `C_m` is computed by Mathlib's periodic resolution
(`Rep.FiniteCyclicGroup.groupCohomologyπOdd`, `Rep.FiniteCyclicGroup.groupCohomologyπEven`). For
the cyclic representation of `A` these quotient maps read as follows.

* In odd degree, and so in degree one, the classes are the elements `t` with
  `∑ j < m, A^j t = 0`, two of them having the same class exactly when they differ by
  `b - A b` for some `b : T` (`AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff`). The image of
  `A - 1` is that of `1 - A`, by negating the argument. These are the twists `t` for which the
  affine map `x ↦ A x + t` has order dividing `m`, up to conjugation by translations, which
  changes `t` to `t + (b - A b)`.
* In positive even degree, the classes are the fixed points of `A`, two of them having the same
  class exactly when they differ by a norm `∑ j < m, A^j y`
  (`AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`).

Every class arises in each case (`Rep.FiniteCyclicGroup.groupCohomologyπOdd_surjective`,
`Rep.FiniteCyclicGroup.groupCohomologyπEven_surjective`).

The representation itself is constructed in `TauCeti.RepresentationTheory.Cyclic.Automorphism`.

## Main results

* `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff`: odd-degree classes are norm-zero elements
  modulo the image of `1 - A`.
* `AddEquiv.groupCohomologyπEven_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`: positive even-degree classes are fixed points
  of `A` modulo the image of the norm.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §6 (the periodic resolution of a cyclic group).
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter VIII,
  §4 (the cohomology of cyclic groups).
-/

public section

open CategoryTheory Rep Rep.FiniteCyclicGroup
open Multiplicative (mem_zpowers_ofAdd_one)

namespace AddEquiv

variable {T : Type} [AddCommGroup T] {m : ℕ} [NeZero m] (A : T ≃+ T) (hA : (⇑A)^[m] = id)

/-- **Odd-degree classes of the cyclic representation.** A norm-zero element `x` has zero class
in odd degree exactly when `x = b - A b` for some `b : T`. -/
theorem groupCohomologyπOdd_cyclicRep_eq_zero_iff (i : ℕ) (hi : Odd i)
    (x : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap) :
    groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x = 0 ↔
      ∃ b, b - A b = (x : T) := by
  rw [groupCohomologyπOdd_eq_zero_iff, mem_range_cyclicRep_applyAsHom_sub_iff]

/-- **Odd-degree classes of the cyclic representation.** Two norm-zero elements `x` and `y`
have the same class in odd degree exactly when `y = x + (b - A b)` for some `b : T`. -/
theorem groupCohomologyπOdd_cyclicRep_eq_iff (i : ℕ) (hi : Odd i)
    (x y : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap) :
    groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x =
        groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi y ↔
      ∃ b, (y : T) = (x : T) + (b - A b) := by
  rw [eq_comm, groupCohomologyπOdd_eq_iff, mem_range_cyclicRep_applyAsHom_sub_iff]
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, ?_⟩ <;> rw [hb] <;> abel

/-- **Even-degree classes of the cyclic representation.** A fixed point `x` of `A` has zero
class in positive even degree exactly when it is a norm `∑ j < m, A^j y`. -/
theorem groupCohomologyπEven_cyclicRep_eq_zero_iff (i : ℕ) [NeZero i] (hi : Even i)
    (x : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap) :
    groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x = 0 ↔
      ∃ y, ∑ j ∈ Finset.range m, (⇑A)^[j] y = (x : T) := by
  rw [groupCohomologyπEven_eq_zero_iff, mem_range_cyclicRep_norm_iff]

/-- **Even-degree classes of the cyclic representation.** Two fixed points `x` and `y` of `A`
have the same class in positive even degree exactly when `y = x + ∑ j < m, A^j z` for some
`z : T`. -/
theorem groupCohomologyπEven_cyclicRep_eq_iff (i : ℕ) [NeZero i] (hi : Even i)
    (x y : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap) :
    groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x =
        groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi y ↔
      ∃ z, (y : T) = (x : T) + ∑ j ∈ Finset.range m, (⇑A)^[j] z := by
  rw [eq_comm, groupCohomologyπEven_eq_iff, mem_range_cyclicRep_norm_iff]
  constructor <;> rintro ⟨z, hz⟩ <;> refine ⟨z, ?_⟩ <;> rw [hz] <;> abel

end AddEquiv
