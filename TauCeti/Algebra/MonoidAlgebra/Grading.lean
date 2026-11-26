/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.MonoidAlgebra.Supported
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
* `AddMonoidAlgebra.coeff_decompose_gradeBy` and
  `AddMonoidAlgebra.coe_decompose_gradeBy_ne_zero_iff`: the projection onto grade `i` restricts
  coefficients to `f ⁻¹' {i}`, and is nonzero iff some supported exponent has weight `i`.
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
  (basisSupported (f ⁻¹' {i})).map
    (LinearEquiv.ofEq _ _ (gradeBy_eq_supported R f i).symm)

@[simp]
theorem coe_basisGradeBy (f : M → ι) (i : ι) (m : f ⁻¹' {i}) :
    (basisGradeBy R f i m : R[M]) = single (m : M) 1 := by
  simp [basisGradeBy]

instance (f : M → ι) (i : ι) : Module.Free R (gradeBy R f i) :=
  .of_basis (basisGradeBy R f i)

/-- **The Hilbert function of a graded monoid algebra.** The rank of the piece of grade `i` of
`R[M]` for the grading by `f` is the number of elements of `M` of grade `i`. -/
theorem finrank_gradeBy [StrongRankCondition R] (f : M → ι) (i : ι) :
    Module.finrank R (gradeBy R f i) = Nat.card (f ⁻¹' {i}) :=
  Module.finrank_eq_nat_card_basis (basisGradeBy R f i)

section Decompose

variable {R} [AddMonoid M] [DecidableEq ι] [AddMonoid ι] (f : M →+ ι)

/-- Projection of `x : R[M]` onto the `i`-th piece of `gradeBy R f` restricts the coefficients of
`x` to the fibre `f ⁻¹' {i}`. -/
@[simp]
theorem coeff_decompose_gradeBy (x : R[M]) (i : ι) (m : M) :
    (DirectSum.decompose (gradeBy R f) x i : R[M]).coeff m =
      if f m = i then x.coeff m else 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
    split_ifs with h <;> simp [ha, hb, h]
  | single g r =>
    rw [GradesBy.decompose_single]
    by_cases hgi : f g = i
    · subst hgi
      rw [DirectSum.of_eq_same]
      by_cases hmg : m = g
      · subst hmg; simp
      · simp [Ne.symm hmg]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hgi)]
      by_cases hmg : m = g
      · subst hmg; simp [hgi]
      · simp [Ne.symm hmg]

/-- The `i`-th homogeneous component of `x : R[M]` under `gradeBy R f` is nonzero if and only if
some supported exponent of `x` has weight `i`. -/
theorem coe_decompose_gradeBy_ne_zero_iff (x : R[M]) (i : ι) :
    (DirectSum.decompose (gradeBy R f) x i : R[M]) ≠ 0 ↔
      ∃ m ∈ x.coeff.support, f m = i := by
  rw [Ne, ← coeff_eq_zero, Finsupp.ext_iff, not_forall]
  simp only [Finsupp.zero_apply, coeff_decompose_gradeBy, ite_eq_right_iff, Classical.not_imp,
    ← Finsupp.mem_support_iff]
  exact ⟨fun ⟨m, hfi, hm⟩ ↦ ⟨m, hm, hfi⟩, fun ⟨m, hm, hfi⟩ ↦ ⟨m, hfi, hm⟩⟩

end Decompose

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
