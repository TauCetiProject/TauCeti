/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.LinearAlgebra.Matrix.ConjTranspose

/-!
# The unitary group of a sesquilinear form

Let `R` be a semiring with an involution `star`. For a square matrix `A` over `R`, the
**unitary group of `A`**, `Matrix.unitaryGroupOf A`, is the subgroup of `GL n R` of the
matrices `g` with `star g * A * g = A`: the invertible matrices preserving the sesquilinear form
`⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` of Gram matrix `A`, conjugate-linear in the first slot. For `A = 1` it
is Mathlib's unitary subgroup `unitarySubgroup (GL n R)` (`Matrix.unitaryGroupOf_one`).

A matrix `x` with `star x * A * x = B` pulls the form of `A` back to that of `B`. When `x` is
invertible, conjugation `g ↦ x⁻¹ * g * x` maps `unitaryGroupOf A` into `unitaryGroupOf B`, and
right multiplication by `unitaryGroupOf B` preserves the equation `star x * A * x = B`; a ring
homomorphism commuting with the involutions maps `unitaryGroupOf A` into `unitaryGroupOf (A.map f)`.
Over a commutative ring and for invertible `A`, the inverse of `g ∈ unitaryGroupOf A` is
`A⁻¹ * star g * A`, so every matrix preserving the form is invertible
(`Matrix.unitaryGroupOf.ofMatrix`).

These are the facts shared by the indefinite unitary groups `U(p, q)`
(`TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup`), the topology of the unitary groups
(`TauCeti.Topology.Algebra.Matrix.UnitaryGroup`) and the adelic unitary groups of a CM field.

## Main definitions

* `Matrix.unitaryGroupOf A`: the group of invertible matrices preserving the sesquilinear form of
  Gram matrix `A`.
* `Matrix.unitaryGroupOf.ofMatrix`: the element of `unitaryGroupOf A` defined by a matrix
  preserving the form, for invertible `A`.

## Main results

* `Matrix.mem_unitaryGroupOf_iff`: membership is the equation `star g * A * g = A`.
* `Matrix.unitaryGroupOf_one`: `unitaryGroupOf 1` is the unitary subgroup of `GL n R`.
* `Matrix.inv_mul_mul_mem_unitaryGroupOf`: conjugation by an invertible `x` pulling the form `A`
  back to `B` (`star x * A * x = B`) maps `unitaryGroupOf A` into `unitaryGroupOf B`, and
  `Matrix.star_mul_mul_mul_eq_of_mem_unitaryGroupOf`: such an `x` still pulls `A` back to `B` after
  right multiplication by `unitaryGroupOf B`.
* `Matrix.map_mem_unitaryGroupOf`: a ring homomorphism commuting with the involutions maps
  `unitaryGroupOf A` into `unitaryGroupOf (A.map f)`.
* `Matrix.val_inv_of_mem_unitaryGroupOf`: the inverse of `g` is `A⁻¹ * star g * A`.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Semiring

variable {R : Type*} [Semiring R] [StarRing R]

/-- The **unitary group of a sesquilinear form**: the invertible matrices `g` with
`star g * A * g = A`, that is the invertible matrices preserving the form
`⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` of Gram matrix `A`. For `A = 1` this is the unitary group, and for
`A = diag(1, …, 1, -1, …, -1)` it is the indefinite unitary group
`TauCeti.Matrix.indefiniteUnitaryGroup`. -/
def unitaryGroupOf (A : Matrix n n R) : Subgroup (GL n R) where
  carrier := {g | star (g : Matrix n n R) * A * g = A}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, star_mul] at *
    calc _ = star (b : Matrix n n R) * (star (a : Matrix n n R) * A * a) * b := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc _ = star (↑a⁻¹ : Matrix n n R) * (star (a : Matrix n n R) * A * a) * ↑a⁻¹ := by
          rw [ha]
      _ = star ((a : Matrix n n R) * ↑a⁻¹) * A * ((a : Matrix n n R) * ↑a⁻¹) := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = _ := by simp

variable {A : Matrix n n R}

/-- Membership in `unitaryGroupOf A` is the equation `star g * A * g = A`. -/
theorem mem_unitaryGroupOf_iff {g : GL n R} :
    g ∈ unitaryGroupOf A ↔ star (g : Matrix n n R) * A * g = A :=
  Iff.rfl

/-- Two elements of `unitaryGroupOf A` are equal when their matrices are. -/
@[ext]
theorem unitaryGroupOf.ext {g h : unitaryGroupOf A}
    (H : ((g : GL n R) : Matrix n n R) = ((h : GL n R) : Matrix n n R)) : g = h :=
  Subtype.ext <| Units.ext H

/-- **The unitary group of the identity form is the unitary subgroup** of `GL n R`: both consist
of the invertible matrices `g` with `star g * g = 1`, which for an invertible `g` also gives
`g * star g = 1`. -/
theorem unitaryGroupOf_one : unitaryGroupOf (1 : Matrix n n R) = unitarySubgroup (GL n R) := by
  ext g
  rw [mem_unitaryGroupOf_iff, Matrix.mul_one, mem_unitarySubgroup_iff, Unitary.mem_iff,
    and_iff_left_of_imp fun h ↦ mul_eq_one_iff_inv_eq.2 (mul_eq_one_iff_eq_inv.1 h).symm,
    Units.ext_iff, Units.val_mul, Units.coe_star, Units.val_one]

/-- **Conjugation by an invertible matrix pulling back the form.** If `x` pulls the form of Gram
matrix `A` back to the form of Gram matrix `B`, that is `star x * A * x = B`, then
`g ↦ x⁻¹ * g * x` maps `unitaryGroupOf A` into `unitaryGroupOf B`. -/
theorem inv_mul_mul_mem_unitaryGroupOf {B : Matrix n n R} {x : GL n R}
    (hx : star (x : Matrix n n R) * A * x = B) {g : GL n R} (hg : g ∈ unitaryGroupOf A) :
    x⁻¹ * g * x ∈ unitaryGroupOf B := by
  rw [mem_unitaryGroupOf_iff] at hg ⊢
  set y : Matrix n n R := ((x⁻¹ : GL n R) : Matrix n n R)
  -- `x⁻¹` pulls the form `B` back to the form `A`: this is the Gram identity for `F = x⁻¹`.
  have h : star y * B * y = A := by
    have h := conjTranspose_mul_mul_mul_of_star_mul_mul_eq hx y y
    rw [Units.mul_inv, conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
    rw [star_eq_conjTranspose, ← h]
  -- `(x⁻¹ (g x))ᴴ B (x⁻¹ (g x)) = (g x)ᴴ A (g x) = xᴴ A x = B`
  have h' := conjTranspose_mul_mul_mul_of_star_mul_mul_eq h
    ((g * x : GL n R) : Matrix n n R) ((g * x : GL n R) : Matrix n n R)
  rw [Units.val_mul, conjTranspose_mul_mul_mul_of_star_mul_mul_eq hg,
    ← star_eq_conjTranspose (x : Matrix n n R), hx] at h'
  simpa only [y, Units.val_mul, Matrix.mul_assoc, star_eq_conjTranspose] using h'

/-- If `x` pulls the form of Gram matrix `A` back to the form of Gram matrix `B`, that is
`star x * A * x = B`, then so does `x * g` for every `g ∈ unitaryGroupOf B`. -/
theorem star_mul_mul_mul_eq_of_mem_unitaryGroupOf {B x : Matrix n n R}
    (hx : star x * A * x = B) {g : GL n R} (hg : g ∈ unitaryGroupOf B) :
    star (x * (g : Matrix n n R)) * A * (x * (g : Matrix n n R)) = B := by
  rw [star_eq_conjTranspose, conjTranspose_mul_mul_mul_of_star_mul_mul_eq hx,
    ← star_eq_conjTranspose, mem_unitaryGroupOf_iff.1 hg]

end Semiring

section CommRing

variable {R : Type*} [CommRing R] [StarRing R] {A : Matrix n n R}

/-- **The inverse of an element of `unitaryGroupOf A`**, for invertible `A`, is
`A⁻¹ * star g * A`. -/
theorem val_inv_of_mem_unitaryGroupOf (hA : IsUnit A) {g : GL n R} (hg : g ∈ unitaryGroupOf A) :
    (↑g⁻¹ : Matrix n n R) = A⁻¹ * star (g : Matrix n n R) * A :=
  Units.inv_eq_of_mul_eq_one_left <| by
    have h := mem_unitaryGroupOf_iff.mp hg
    simp only [Matrix.mul_assoc] at h ⊢
    rw [h, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA)]

/-- A ring homomorphism commuting with the involutions maps `unitaryGroupOf A` into
`unitaryGroupOf (A.map f)`. -/
theorem map_mem_unitaryGroupOf {S : Type*} [CommRing S] [StarRing S] {f : R →+* S}
    (hf : ∀ r, f (star r) = star (f r)) {g : GL n R} (hg : g ∈ unitaryGroupOf A) :
    GeneralLinearGroup.map f g ∈ unitaryGroupOf (A.map f) := by
  -- Apply `f` entrywise to the equation `gᴴ A g = A`.
  have h := congrArg (fun M ↦ M.map f) (mem_unitaryGroupOf_iff.1 hg)
  simp only [Matrix.map_mul, star_eq_conjTranspose, conjTranspose_map f hf] at h
  rw [mem_unitaryGroupOf_iff, GeneralLinearGroup.val_map_apply, star_eq_conjTranspose, h]

namespace unitaryGroupOf

/-- A matrix preserving the form of an invertible Gram matrix `A` is invertible, with inverse
`A⁻¹ * star M * A`: this is the element of `unitaryGroupOf A` it defines. -/
noncomputable def ofMatrix (hA : IsUnit A) (M : Matrix n n R) (hM : star M * A * M = A) :
    unitaryGroupOf A :=
  have h : A⁻¹ * star M * A * M = 1 := by
    simp only [Matrix.mul_assoc] at hM ⊢
    rw [hM, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A).mp hA)]
  ⟨⟨M, A⁻¹ * star M * A, mul_eq_one_comm.mp h, h⟩, hM⟩

@[simp]
theorem val_ofMatrix (hA : IsUnit A) (M : Matrix n n R) (hM : star M * A * M = A) :
    ((ofMatrix hA M hM : GL n R) : Matrix n n R) = M :=
  (rfl)

end unitaryGroupOf

end CommRing

end Matrix
