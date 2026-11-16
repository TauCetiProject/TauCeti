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
* `AddMonoidAlgebra.eq_single_coeff_of_mem_grade`: every element of `grade R p` equals
  `single p (u.coeff p)`.
* `AddMonoidAlgebra.mapRingHom_mem_gradeBy` and `AddMonoidAlgebra.mapRingHom_mem_grade`: mapping
  coefficients along a ring homomorphism preserves graded pieces.
* `AddMonoidAlgebra.coe_decompose_grade`: projecting an element of `R[M]` to `grade R p` via
  `DirectSum.decompose` extracts `single p (x.coeff p)`.
* `TauCeti.homogeneousUnitDegrees_gradeBy`: for the group algebra `R[G]` graded by an additive
  homomorphism `f : G →+ ι`, the homogeneous unit degrees are the range of `f`.
-/

public section

namespace AddMonoidAlgebra

section GradeCoeff

/-- Every element of the `p`-th homogeneous piece `grade R p` of `R[M]` is the single monomial at
`p` with its `p`-th coefficient. -/
theorem eq_single_coeff_of_mem_grade {R M : Type*} [CommSemiring R] {p : M} {u : R[M]}
    (hu : u ∈ grade R p) : u = single p (u.coeff p) := by
  ext m
  rw [coeff_single]
  by_cases hmp : p = m
  · subst hmp
    exact Finsupp.single_eq_same.symm
  · rw [Finsupp.single_eq_of_ne (Ne.symm hmp)]
    by_contra hne
    exact hmp (hu m (Finsupp.mem_support_iff.mpr hne)).symm

/-- Mapping coefficients along `g : R →+* R'` preserves each homogeneous piece of `gradeBy`. -/
theorem mapRingHom_mem_gradeBy {R R' M ι : Type*} [CommSemiring R] [CommSemiring R'] [AddMonoid M]
    (g : R →+* R') {f : M → ι} {i : ι} {u : R[M]} (hu : u ∈ gradeBy R f i) :
    mapRingHom M g u ∈ gradeBy R' f i := by
  intro m hm
  apply hu m
  rw [Finsupp.mem_support_iff] at hm ⊢
  rw [coeff_mapRingHom] at hm
  intro h0
  exact hm (by rw [h0, map_zero])

/-- Mapping coefficients along `g : R →+* R'` preserves each homogeneous piece of `grade`. -/
theorem mapRingHom_mem_grade {R R' M : Type*} [CommSemiring R] [CommSemiring R'] [AddMonoid M]
    (g : R →+* R') {p : M} {u : R[M]} (hu : u ∈ grade R p) :
    mapRingHom M g u ∈ grade R' p :=
  mapRingHom_mem_gradeBy g hu

/-- Projecting an element of `R[M]` to its `p`-th graded piece via `DirectSum.decompose` extracts
the single monomial at `p` with coefficient `x.coeff p`. -/
theorem coe_decompose_grade {R M : Type*} [CommSemiring R] [AddMonoid M] [DecidableEq M]
    (x : R[M]) (p : M) :
    (DirectSum.decompose (grade R) x p : R[M]) = single p (x.coeff p) := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [DirectSum.decompose_add, DFinsupp.add_apply, Submodule.coe_add, hx, hy,
      coeff_add, Finsupp.add_apply, single_add]
  | single m r =>
    by_cases hmp : m = p
    · subst hmp
      rw [DirectSum.decompose_of_mem_same _ (single_mem_grade m r),
        coeff_single, Finsupp.single_eq_same]
    · have hmp' : m ≠ p := hmp
      rw [DirectSum.decompose_of_mem_ne _ (single_mem_grade m r) hmp',
        coeff_single, Finsupp.single_eq_of_ne hmp'.symm, single_zero]

end GradeCoeff

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
