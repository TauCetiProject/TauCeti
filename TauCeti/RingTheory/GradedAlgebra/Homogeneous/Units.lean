/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Homogeneous units and shift classes of a graded ring

In a ring `A` graded by an additive group `ι`, the inverse of a homogeneous unit of degree `i` is
homogeneous of degree `-i`, so the degrees of the homogeneous units form an additive subgroup
`homogeneousUnitDegrees 𝒜` of `ι`, and we write `ShiftClassGroup 𝒜` for the quotient of `ι` by it.

The quotient classifies the shifts of the free module of rank one. The shift `A(d)` is `A` with the
grading `n ↦ 𝒜 (n + d)`, and `A(d)` and `A(e)` are isomorphic as graded `A`-modules exactly when
`d - e` is the degree of a homogeneous unit. More generally, if a grading `ℳ` of `A` as a module
over the graded ring `(A, 𝒜)` has a homogeneous generator, a unit `u ∈ ℳ c`, then `ℳ` is the
image of the shift `A(-c)` under right multiplication by `u`.

Geometrically, a commutative `ℤ`-graded ring is a `𝔾_m`-action on `Spec A`, and a grading of the
`A`-module `A` compatible with `𝒜` is a `𝔾_m`-linearisation of the structure sheaf; the shift
`A(d)` is the module of sections of the trivial line bundle twisted by the character `t ↦ t^d`.

## Main definitions

* `TauCeti.GradedAlgebra.homogeneousUnitDegrees`: the subgroup of degrees of homogeneous units.
* `TauCeti.GradedAlgebra.ShiftClassGroup`: the quotient of the degrees by that subgroup.

## Main results

* `TauCeti.GradedAlgebra.val_inv_mem_neg`: the inverse of a homogeneous unit of degree `i` is
  homogeneous of degree `-i`.
* `TauCeti.GradedAlgebra.mem_iff_mul_inv_mem_sub` and
  `TauCeti.GradedAlgebra.eq_map_mulRight_of_mem`: a compatible module grading of `A` with a
  homogeneous unit generator of degree `c` is the shift `A(-c)` transported by right
  multiplication by the generator.
* `TauCeti.GradedAlgebra.sub_mem_homogeneousUnitDegrees_iff` and
  `TauCeti.GradedAlgebra.shiftClassGroup_coe_eq_coe_iff`: `A(d)` and `A(e)` are isomorphic as graded
  modules if and only if `d` and `e` have the same shift class.
* `TauCeti.GradedAlgebra.homogeneousUnitDegrees_eq_top` and
  `TauCeti.GradedAlgebra.homogeneousUnitDegrees_trivialGrading`: the subgroup is everything for the
  zero ring and trivial for the trivial grading of a nonzero algebra.
-/

public section

open DirectSum

namespace TauCeti.GradedAlgebra

variable {ι A σ : Type*} [DecidableEq ι] [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]

section Module

variable [AddGroup ι] (𝒜 : ι → σ) [Decomposition 𝒜]
  {τ : Type*} [SetLike τ A] [AddSubmonoidClass τ A] (ℳ : ι → τ) [SetLike.GradedSMul 𝒜 ℳ]

/-- **Homogeneous generators.** Let `ℳ` be a grading of `A`, viewed as a module over the graded
ring `(A, 𝒜)`, and let the unit `u` be homogeneous of degree `c` for `ℳ`. Then `x` has
`ℳ`-degree `n` exactly when `x * u⁻¹` has `𝒜`-degree `n - c`. -/
theorem mem_iff_mul_inv_mem_sub [Decomposition ℳ] {u : Aˣ} {c : ι} (hu : (u : A) ∈ ℳ c)
    {x : A} {n : ι} : x ∈ ℳ n ↔ x * ↑u⁻¹ ∈ 𝒜 (n - c) := by
  constructor
  · intro hx
    -- The component of `x * u⁻¹` of degree `n - c` times `u` is the component of `x` of degree
    -- `n`, which is `x` itself; cancelling `u` identifies `x * u⁻¹` with that component.
    have h : (decompose 𝒜 (x * ↑u⁻¹) (n - c) : A) * u = x * ↑u⁻¹ * u := by
      rw [← smul_eq_mul, ← coe_decompose_smul_add_of_right_mem 𝒜 ℳ hu, sub_add_cancel,
        smul_eq_mul, Units.inv_mul_cancel_right, decompose_of_mem_same ℳ hx]
    rw [← (Units.mul_left_inj u).mp h]
    exact (decompose 𝒜 (x * ↑u⁻¹) (n - c)).2
  · intro hx
    have h := SetLike.GradedSMul.smul_mem hx hu
    rwa [smul_eq_mul, Units.inv_mul_cancel_right, vadd_eq_add, sub_add_cancel] at h

/-- **Shift classification of a grading with a homogeneous unit generator.** If `ℳ` is a grading
of the algebra `A`, viewed as a module over the graded algebra `(A, 𝒜)`, and the unit `u` is
homogeneous of degree `c` for `ℳ`, then `ℳ n = 𝒜 (n - c) * u` for every `n`: right multiplication
by `u` is a graded isomorphism from the shift `A(-c)` onto `(A, ℳ)`. -/
theorem eq_map_mulRight_of_mem {R : Type*} [CommSemiring R] [Algebra R A]
    (𝒜 ℳ : ι → Submodule R A) [Decomposition 𝒜] [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]
    {u : Aˣ} {c : ι} (hu : (u : A) ∈ ℳ c) (n : ι) :
    ℳ n = (𝒜 (n - c)).map (LinearMap.mulRight R (u : A)) := by
  ext x
  rw [mem_iff_mul_inv_mem_sub 𝒜 ℳ hu, Submodule.mem_map]
  constructor
  · intro hx
    exact ⟨x * ↑u⁻¹, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

end Module

section AddGroup

variable [AddGroup ι] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- The inverse of a homogeneous unit of degree `i` is homogeneous of degree `-i`. -/
theorem val_inv_mem_neg {u : Aˣ} {i : ι} (hu : (u : A) ∈ 𝒜 i) : ((u⁻¹ : Aˣ) : A) ∈ 𝒜 (-i) := by
  have h := (mem_iff_mul_inv_mem_sub 𝒜 𝒜 hu).mp SetLike.GradedOne.one_mem
  rwa [one_mul, zero_sub] at h

/-- The degrees of the homogeneous units of a graded ring, an additive subgroup of the grading
group: products and inverses of homogeneous units are homogeneous units. -/
def homogeneousUnitDegrees : AddSubgroup ι where
  carrier := {i | ∃ u : Aˣ, (u : A) ∈ 𝒜 i}
  zero_mem' := ⟨1, SetLike.GradedOne.one_mem⟩
  add_mem' := fun ⟨u, hu⟩ ⟨v, hv⟩ ↦ ⟨u * v, SetLike.mul_mem_graded hu hv⟩
  neg_mem' := fun ⟨u, hu⟩ ↦ ⟨u⁻¹, val_inv_mem_neg 𝒜 hu⟩

/-- A degree lies in `homogeneousUnitDegrees 𝒜` exactly when it is the degree of a homogeneous
unit: no closure under sums or negatives is needed. -/
@[simp]
theorem mem_homogeneousUnitDegrees_iff {i : ι} :
    i ∈ homogeneousUnitDegrees 𝒜 ↔ ∃ u : Aˣ, (u : A) ∈ 𝒜 i :=
  Iff.rfl

/-- In the zero ring the unit `1 = 0` is homogeneous of every degree. -/
theorem homogeneousUnitDegrees_eq_top [Subsingleton A] : homogeneousUnitDegrees 𝒜 = ⊤ :=
  eq_top_iff.mpr fun i _ ↦ ⟨1, by rw [Units.val_one, Subsingleton.elim (1 : A) 0]; exact zero_mem _⟩

end AddGroup

section AddCommGroup

variable [AddCommGroup ι] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- The shift classes of a graded ring: the grading group modulo the degrees of the homogeneous
units. By `shiftClassGroup_coe_eq_coe_iff`, it classifies the shifts `A(d)` of the free module of
rank one up to graded isomorphism. -/
abbrev ShiftClassGroup : Type _ :=
  ι ⧸ homogeneousUnitDegrees 𝒜

/-- **Classification of shifts.** The shifts `A(d)` and `A(e)`, with degree-`n` pieces `𝒜 (n + d)`
and `𝒜 (n + e)`, are isomorphic as graded `A`-modules if and only if `d - e` is the degree of a
homogeneous unit. -/
theorem sub_mem_homogeneousUnitDegrees_iff {d e : ι} :
    d - e ∈ homogeneousUnitDegrees 𝒜 ↔
      ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ 𝒜 (n + e) ↔ x ∈ 𝒜 (n + d) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v⁻¹.mulRightLinearEquiv A, fun n x ↦ ?_⟩
    rw [Units.mulRightLinearEquiv_apply, mem_iff_mul_inv_mem_sub 𝒜 𝒜 hv (x := x) (n := n + d),
      show n + d - (d - e) = n + e by abel]
  · rintro ⟨φ, hφ⟩
    -- An `A`-linear endomorphism of `A` is right multiplication by the image of `1`.
    have hmul (ψ : A ≃ₗ[A] A) (x : A) : ψ x = x * ψ 1 := by
      rw [← smul_eq_mul, ← ψ.map_smul, smul_eq_mul, mul_one]
    let u : Aˣ :=
      { val := φ 1
        inv := φ.symm 1
        val_inv := by rw [← hmul, φ.symm_apply_apply]
        inv_val := by rw [← hmul, φ.apply_symm_apply] }
    have hu : (u : A) ∈ 𝒜 (-(d - e)) := by
      have h := (hφ (-d) 1).mpr (by rw [neg_add_cancel]; exact SetLike.GradedOne.one_mem)
      rwa [show -d + e = -(d - e) by abel] at h
    simpa using neg_mem (show -(d - e) ∈ homogeneousUnitDegrees 𝒜 from ⟨u, hu⟩)

/-- **Shift classes classify shifts.** The shifts `A(d)` and `A(e)` are isomorphic as graded
`A`-modules if and only if `d` and `e` have the same shift class. -/
theorem shiftClassGroup_coe_eq_coe_iff {d e : ι} :
    (d : ShiftClassGroup 𝒜) = e ↔ ∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ 𝒜 (n + e) ↔ x ∈ 𝒜 (n + d) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, sub_mem_homogeneousUnitDegrees_iff]

end AddCommGroup

/-- For the trivial grading of a nonzero algebra, concentrated in degree zero, every unit has
degree `0` only, so no shifts of the free module of rank one are identified. -/
theorem homogeneousUnitDegrees_trivialGrading (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [Nontrivial A] : homogeneousUnitDegrees (trivialGrading R A) = ⊥ := by
  ext i
  rw [mem_homogeneousUnitDegrees_iff, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨u, hu⟩
    exact ((mem_trivialGrading_iff R A).mp hu).resolve_right u.ne_zero
  · rintro rfl
    exact ⟨1, (mem_trivialGrading_iff R A).mpr (Or.inl rfl)⟩

end TauCeti.GradedAlgebra
