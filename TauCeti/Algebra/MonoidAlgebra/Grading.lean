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
import TauCeti.Algebra.MonoidAlgebra.Basic

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
* `AddMonoidAlgebra.single_coeff_eq_of_mem_grade`: a homogeneous element of `grade R m` equals
  `single m (a.coeff m)`.
* `AddMonoidAlgebra.coeff_mul_of_mem_grade`: the `(m₁ + m₂)`-th coefficient of a product of
  homogeneous elements in `grade R m₁` and `grade R m₂` is the product of their coefficients.
* `AddMonoidAlgebra.decompose_grade_curryAlgEquiv_symm_single`: homogeneous component of an
  uncurried single-exponent Laurent/monoid-algebra element.
* `AddMonoidAlgebra.map_mem_gradeBy`, `AddMonoidAlgebra.mapAlgHom_mem_gradeBy`,
  `AddMonoidAlgebra.mapAlgHom_mem_grade`: coefficient homomorphisms preserve graded pieces.
* `TauCeti.homogeneousUnitDegrees_gradeBy`: for the group algebra `R[G]` graded by an additive
  homomorphism `f : G →+ ι`, the homogeneous unit degrees are the range of `f`.
-/

public section

namespace AddMonoidAlgebra

section GradeBy

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

end GradeBy

variable {M ι : Type*}

/-- An element of `AddMonoidAlgebra.grade R m` equals `single m` of its `m`-th coefficient. -/
theorem single_coeff_eq_of_mem_grade {R : Type*} [CommSemiring R] {m : M} {a : R[M]}
    (ha : a ∈ grade R m) : single m (a.coeff m) = a := by
  obtain ⟨r, rfl⟩ := (mem_grade_iff' R m a).mp ha
  simp

/-- In an additive monoid algebra, the `(m₁ + m₂)`-th coefficient of a product of homogeneous
elements of degrees `m₁` and `m₂` is the product of their respective coefficients. -/
theorem coeff_mul_of_mem_grade {R : Type*} [CommSemiring R] [Add M] {m₁ m₂ : M}
    {a₁ a₂ : R[M]} (ha₁ : a₁ ∈ grade R m₁) (ha₂ : a₂ ∈ grade R m₂) :
    (a₁ * a₂).coeff (m₁ + m₂) = a₁.coeff m₁ * a₂.coeff m₂ := by
  rw [← single_coeff_eq_of_mem_grade ha₁, ← single_coeff_eq_of_mem_grade ha₂]
  simp

/-- Graded component of `(AddMonoidAlgebra.curryAlgEquiv S).symm (single d f)` in `S[M × N]`. -/
theorem decompose_grade_curryAlgEquiv_symm_single {S M N : Type*} [CommSemiring S]
    [AddMonoid M] [AddMonoid N] [DecidableEq M] [DecidableEq N]
    (d : M) (f : S[N]) (k : M) (m' : N) :
    (DirectSum.decompose (grade S) ((curryAlgEquiv S).symm (single d f)) (k, m') : S[M × N]) =
      if d = k then single (d, m') (f.coeff m') else 0 := by
  rw [grade.decompose_apply, coeff_curryAlgEquiv_symm, coeff_single, Finsupp.single_apply]
  split_ifs with h <;> [rw [h]; simp]

/-- Mapping coefficients along an additive monoid homomorphism preserves every graded piece of
`gradeBy`. -/
theorem map_mem_gradeBy {S S' : Type*} [CommSemiring S] [CommSemiring S']
    (g : S →+ S') (f : M → ι) {i : ι} {x : S[M]} (hx : x ∈ gradeBy S f i) :
    map g x ∈ gradeBy S' f i := by
  intro m hm
  rw [coeff_map] at hm
  exact hx m (Finsupp.support_mapRange hm)

/-- Mapping coefficients along an algebra homomorphism preserves every graded piece of `gradeBy`. -/
theorem mapAlgHom_mem_gradeBy {R S S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring S'] [Algebra R S] [Algebra R S'] [AddMonoid M]
    (φ : S →ₐ[R] S') (f : M → ι) {i : ι} {x : S[M]} (hx : x ∈ gradeBy S f i) :
    mapAlgHom M φ x ∈ gradeBy S' f i := by
  rw [← AlgHom.coe_toRingHom, toRingHom_mapAlgHom, coe_mapRingHom]
  exact map_mem_gradeBy φ.toRingHom.toAddMonoidHom f hx

/-- Mapping coefficients along an algebra homomorphism preserves every graded piece of `grade`. -/
theorem mapAlgHom_mem_grade {R S S' : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring S'] [Algebra R S] [Algebra R S'] [AddMonoid M]
    (φ : S →ₐ[R] S') {m : M} {x : S[M]} (hx : x ∈ grade S m) :
    mapAlgHom M φ x ∈ grade S' m :=
  mapAlgHom_mem_gradeBy φ id hx

end AddMonoidAlgebra

namespace TauCeti

open _root_.AddMonoidAlgebra

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
