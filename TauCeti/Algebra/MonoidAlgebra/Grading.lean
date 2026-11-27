/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Degree
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Algebra.MonoidAlgebra.Supported
public import TauCeti.RingTheory.GradedAlgebra.Degree.Width
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Bases, ranks, and weighted degrees of the graded pieces of a monoid algebra

A function `f : M → ι` grades the additive monoid algebra `R[M]` by the submodules
`AddMonoidAlgebra.gradeBy R f i` of elements supported on the fibre `f ⁻¹' {i}`. This file shows
that the basis elements `single m 1` with `f m = i` form a basis of the piece of grade `i`, so that
its rank is the number of elements of `M` of grade `i`.

For the semigroup algebra `k[S]` of an additive monoid `S` graded by a degree `deg : S →+ ℕ`, the
*Hilbert function* of `k[S]` is `n ↦ Module.finrank k (gradeBy k deg n)`, the rank of its
homogeneous component of degree `n`. By `AddMonoidAlgebra.finrank_gradeBy` it is the function
counting the elements of `S` of degree `n`. The count is taken with `Nat.card`, which is `0` for an
infinite fibre, as is the rank of a free module of infinite rank.

When `w : M →+ ι` takes values in a linearly ordered additive monoid or commutative group, the
`WeightDegree` section relates `TauCeti.GradedAlgebra.minDeg`, `maxDeg`, and `degWidth` for
`gradeBy R w` to `x.coeff.support`, `AddMonoidAlgebra.supDegree`, and `AddMonoidAlgebra.infDegree`.

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
* `AddMonoidAlgebra.supDegree_withBot_eq_maxDeg_gradeBy`,
  `AddMonoidAlgebra.infDegree_withTop_eq_minDeg_gradeBy`, and
  `AddMonoidAlgebra.degWidth_gradeBy_eq_zero_iff_forall_mem_support`: extremal graded degrees and
  degree width of `gradeBy R w` in terms of `x.coeff.support`, `supDegree`, and `infDegree`.
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

section WeightDegree

open TauCeti.GradedAlgebra

variable {R} [AddMonoid M] [DecidableEq ι]

section AddMonoid

variable [AddMonoid ι] [LinearOrder ι] (w : M →+ ι)

/-- Every supported exponent of `x : R[M]` has weight at least `minDeg (gradeBy R w) x`. -/
theorem minDeg_gradeBy_le_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    minDeg (gradeBy R w) x ≤ w m :=
  minDeg_le_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- Every supported exponent of `x : R[M]` has weight at most `maxDeg (gradeBy R w) x`. -/
theorem le_maxDeg_gradeBy_of_mem_support {x : R[M]} {m : M} (hm : m ∈ x.coeff.support) :
    w m ≤ maxDeg (gradeBy R w) x :=
  le_maxDeg_of_decompose_ne_zero (gradeBy R w)
    ((coe_decompose_gradeBy_ne_zero_iff w x (w m)).mpr ⟨m, hm, rfl⟩)

/-- For nonzero `x : R[M]`, `minDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = minDeg (gradeBy R w) x := by
  have hne := minHomogPart_ne_zero (gradeBy R w) hx
  rw [minHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `maxDeg (gradeBy R w) x` is attained at some supported exponent. -/
theorem exists_mem_support_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    ∃ m ∈ x.coeff.support, w m = maxDeg (gradeBy R w) x := by
  have hne := maxHomogPart_ne_zero (gradeBy R w) hx
  rw [maxHomogPart_def] at hne
  exact (coe_decompose_gradeBy_ne_zero_iff w x _).mp hne

/-- For nonzero `x : R[M]`, `supDegree` along `w : M → WithBot ι` agrees with
`maxDeg (gradeBy R w) x`. -/
theorem supDegree_withBot_eq_maxDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.supDegree (fun m ↦ (w m : WithBot ι)) = maxDeg (gradeBy R w) x := by
  refine le_antisymm
    (Finset.sup_le fun m hm ↦ WithBot.coe_le_coe.mpr (le_maxDeg_gradeBy_of_mem_support w hm)) ?_
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_maxDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.le_sup (f := fun m ↦ (w m : WithBot ι)) hm

/-- For nonzero `x : R[M]`, `infDegree` along `w : M → WithTop ι` agrees with
`minDeg (gradeBy R w) x`. -/
theorem infDegree_withTop_eq_minDeg_gradeBy {x : R[M]} (hx : x ≠ 0) :
    x.infDegree (fun m ↦ (w m : WithTop ι)) = minDeg (gradeBy R w) x := by
  refine le_antisymm ?_
    (Finset.le_inf fun m hm ↦ WithTop.coe_le_coe.mpr (minDeg_gradeBy_le_of_mem_support w hm))
  obtain ⟨m, hm, hwm⟩ := exists_mem_support_minDeg_gradeBy w hx
  rw [← hwm]
  exact Finset.inf_le (f := fun m ↦ (w m : WithTop ι)) hm

end AddMonoid

section AddCommGroup

variable [AddCommGroup ι] [LinearOrder ι] (w : M →+ ι)

/-- The difference of weights of any two supported exponents of `x` is bounded above by
`degWidth (gradeBy R w) x`. -/
theorem le_degWidth_gradeBy_of_mem_support [IsOrderedAddMonoid ι] {x : R[M]} {m₁ m₂ : M}
    (hm₁ : m₁ ∈ x.coeff.support) (hm₂ : m₂ ∈ x.coeff.support) :
    w m₁ - w m₂ ≤ degWidth (gradeBy R w) x := by
  rw [degWidth_def]
  exact sub_le_sub (le_maxDeg_gradeBy_of_mem_support w hm₁)
    (minDeg_gradeBy_le_of_mem_support w hm₂)

/-- The degree width of `x : R[M]` along `w` vanishes if and only if `w` takes the same value on
all supported exponents of `x`. -/
theorem degWidth_gradeBy_eq_zero_iff_forall_mem_support {x : R[M]} :
    degWidth (gradeBy R w) x = 0 ↔
      ∀ m₁ ∈ x.coeff.support, ∀ m₂ ∈ x.coeff.support, w m₁ = w m₂ := by
  rw [degWidth_eq_zero_iff]
  refine ⟨fun ⟨d, hd⟩ m₁ hm₁ m₂ hm₂ ↦ by
    rw [(mem_gradeBy_iff R w d x).mp hd hm₁, (mem_gradeBy_iff R w d x).mp hd hm₂], fun h ↦ ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ Submodule.zero_mem _⟩
  · obtain ⟨m₀, hm₀⟩ := Finsupp.support_nonempty_iff.mpr (mt coeff_eq_zero.mp hx)
    exact ⟨w m₀, (mem_gradeBy_iff R w (w m₀) x).mpr fun m hm ↦ h m hm m₀ hm₀⟩

end AddCommGroup

end WeightDegree

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
