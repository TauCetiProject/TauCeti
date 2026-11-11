/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units

/-!
# Bases and ranks of the graded pieces of a monoid algebra

A function `f : M → ι` grades the additive monoid algebra `R[M]` by the submodules
`AddMonoidAlgebra.gradeBy R f i` of elements supported on the fibre `f ⁻¹' {i}`. This file shows
that the basis elements `single m 1` with `f m = i` form a basis of the piece of grade `i`, so that
its rank is the number of elements of `M` of grade `i`.

For the semigroup algebra `k[S]` of an additive monoid `S` graded by a degree `deg : S →+ ℕ`, the
*Hilbert function* of `k[S]` is `n ↦ Module.finrank k (gradeBy k deg n)`, the rank of its
homogeneous component of degree `n`. By `AddMonoidAlgebra.finrank_gradeBy` it is the function
counting the elements of `S` of degree `n`. The count is taken with `Nat.card`, which is `0` for an
infinite fibre, as is the rank of a free module of infinite rank.

## Main declarations

* `AddMonoidAlgebra.gradeBy_eq_supported`: the piece of grade `i` consists of the elements
  supported on `f ⁻¹' {i}`.
* `AddMonoidAlgebra.basisGradeBy`: the basis of the piece of grade `i` given by the elements
  `single m 1` with `f m = i`.
* `AddMonoidAlgebra.finrank_gradeBy`: the rank of the piece of grade `i` is the number of
  elements of `M` of grade `i`.
* `TauCeti.homogeneousUnitDegrees_gradeBy`: for the group algebra `R[G]` graded by an additive
  homomorphism `f : G →+ ι`, the homogeneous unit degrees are the range of `f`.
-/

public section

namespace AddMonoidAlgebra

variable {M ι : Type*} (R : Type*) [CommSemiring R]

/-- The piece of grade `i` of `R[M]` for the grading by `f` consists of the elements supported on
the fibre `f ⁻¹' {i}`. -/
theorem gradeBy_eq_supported (f : M → ι) (i : ι) :
    gradeBy R f i = supported R R (f ⁻¹' {i}) := by
  ext x
  rw [mem_gradeBy_iff, mem_supported]

/-- The piece of grade `i` of `R[M]` for the grading by `f` has a basis indexed by the fibre
`f ⁻¹' {i}`, consisting of the elements `single m 1` with `f m = i`. -/
noncomputable def basisGradeBy (f : M → ι) (i : ι) :
    Module.Basis (f ⁻¹' {i}) R (gradeBy R f i) :=
  (Finsupp.basisSingleOne.map (supportedEquivFinsupp (f ⁻¹' {i})).symm).map
    (LinearEquiv.ofEq _ _ (gradeBy_eq_supported R f i).symm)

@[simp]
theorem coe_basisGradeBy (f : M → ι) (i : ι) (m : f ⁻¹' {i}) :
    (basisGradeBy R f i m : R[M]) = single (m : M) 1 := by
  simp [basisGradeBy, supportedEquivFinsupp]

instance (f : M → ι) (i : ι) : Module.Free R (gradeBy R f i) :=
  .of_basis (basisGradeBy R f i)

/-- **The Hilbert function of a graded monoid algebra.** The rank of the piece of grade `i` of
`R[M]` for the grading by `f` is the number of elements of `M` of grade `i`. -/
theorem finrank_gradeBy [StrongRankCondition R] (f : M → ι) (i : ι) :
    Module.finrank R (gradeBy R f i) = Nat.card (f ⁻¹' {i}) :=
  Module.finrank_eq_nat_card_basis (basisGradeBy R f i)

end AddMonoidAlgebra

namespace TauCeti

open AddMonoidAlgebra

variable {ι G : Type*} [AddGroup ι] [AddGroup G]

/-- For the group algebra `R[G]` over a nontrivial commutative semiring, graded by an additive
homomorphism `f : G →+ ι` (so that `single g r` has degree `f g`), the degrees of the homogeneous
units are the range of `f`: each `single g 1` is a homogeneous unit of degree `f g`, and a nonzero
element of degree `d` has a monomial of degree `d`. -/
@[simp]
theorem homogeneousUnitDegrees_gradeBy (R : Type*) [CommSemiring R] [Nontrivial R]
    (f : G →+ ι) : homogeneousUnitDegrees (gradeBy R f) = f.range := by
  refine le_antisymm (homogeneousUnitDegrees_le_iff.mpr fun u d hu ↦ ?_) fun d ⟨g, hg⟩ ↦ ?_
  · obtain ⟨g, hg⟩ : (u : R[G]).coeff.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff, Ne, ← coeff_zero, coeff_inj]
      exact u.ne_zero
    exact ⟨g, (mem_gradeBy_iff R f d _).mp hu hg⟩
  · let v : R[G]ˣ := ⟨single g 1, single (-g) 1, by simp [AddMonoidAlgebra.one_def],
      by simp [AddMonoidAlgebra.one_def]⟩
    exact mem_homogeneousUnitDegrees_of_mem (u := v) (hg ▸ single_mem_gradeBy _ _ _)

end TauCeti
