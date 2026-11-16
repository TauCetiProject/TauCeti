/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# `⋆`-algebra homomorphisms and equivalences on `Pi` types

Single-factor inclusions into dependent products of non-unital `⋆`-algebras and `⋆`-algebra
equivalences for products indexed by a `Unique` type:

* `NonUnitalStarAlgHom.single`: the single-coordinate inclusion `A i →⋆ₙₐ[R] ∀ j, A j` sending `x`
  to `Pi.single i x`.
* `StarAlgEquiv.piUnique` and `StarAlgEquiv.funUnique`: the `⋆`-algebra equivalences
  `(∀ i, A i) ≃⋆ₐ[R] A default` and `(ι → A) ≃⋆ₐ[R] A` for `[Unique ι]`.
-/

public section

namespace NonUnitalStarAlgHom

section Single

variable (R : Type*) {ι : Type*} [DecidableEq ι] (A : ι → Type*) [Monoid R]
  [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
  [∀ i, StarAddMonoid (A i)]

/-- The non-unital `⋆`-algebra homomorphism including a single factor `A i` into the dependent
product `∀ j, A j` as functions supported at `i`. -/
def single (i : ι) : A i →⋆ₙₐ[R] ∀ j, A j :=
  { AddMonoidHom.single A i, MulHom.single i with
    map_smul' := Pi.single_smul i
    map_star' := Pi.single_star i }

/-- Coercion of `NonUnitalStarAlgHom.single` to a function is `Pi.single`. -/
@[simp]
theorem coe_single (i : ι) : ⇑(single R A i) = Pi.single i :=
  (rfl)

/-- Applying `NonUnitalStarAlgHom.single` gives `Pi.single`. -/
theorem single_apply {R : Type*} {ι : Type*} [DecidableEq ι] {A : ι → Type*} [Monoid R]
    [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
    [∀ i, StarAddMonoid (A i)] (i : ι) (x : A i) :
    single R A i x = Pi.single i x :=
  (rfl)

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at the same coordinate `i` gives the identity. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_single_same (i : ι) :
    (Pi.evalNonUnitalStarAlgHom R A i).comp (single R A i) = .id R (A i) :=
  ext <| Pi.single_eq_same i

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at a distinct coordinate `j ≠ i` gives zero. -/
theorem evalNonUnitalStarAlgHom_comp_single_of_ne {i j : ι} (h : j ≠ i) :
    (Pi.evalNonUnitalStarAlgHom R A j).comp (single R A i) = 0 :=
  ext <| Pi.single_eq_of_ne h

end Single

end NonUnitalStarAlgHom

namespace StarAlgEquiv

section Unique

variable (R : Type*) {ι : Type*} [Unique ι]

/-- Dependent functions on a `Unique` index type are `⋆`-algebra equivalent to the fiber at
`default`. -/
def piUnique (A : ι → Type*) [∀ i, Add (A i)] [∀ i, Mul (A i)] [∀ i, SMul R (A i)]
    [∀ i, Star (A i)] : (∀ i, A i) ≃⋆ₐ[R] A default where
  __ := Equiv.piUnique A
  map_mul' _ _ := Pi.mul_apply _ _ _
  map_add' _ _ := Pi.add_apply _ _ _
  map_star' _ := Pi.star_apply _ _
  map_smul' _ _ := Pi.smul_apply _ _ _

/-- Applying `StarAlgEquiv.piUnique` evaluates at `default`. -/
@[simp low]
theorem piUnique_apply {R : Type*} {ι : Type*} [Unique ι] {A : ι → Type*}
    [∀ i, Add (A i)] [∀ i, Mul (A i)] [∀ i, SMul R (A i)] [∀ i, Star (A i)] (f : ∀ i, A i) :
    piUnique R A f = f default :=
  (rfl)

/-- Applying `(StarAlgEquiv.piUnique R A).symm` gives `uniqueElim`. -/
@[simp low]
theorem piUnique_symm_apply {R : Type*} {ι : Type*} [Unique ι] {A : ι → Type*}
    [∀ i, Add (A i)] [∀ i, Mul (A i)] [∀ i, SMul R (A i)] [∀ i, Star (A i)] (a : A default) :
    (piUnique R A).symm a = uniqueElim a :=
  (rfl)

/-- Functions from a `Unique` type `ι` to `A` are `⋆`-algebra equivalent to `A`. -/
def funUnique (ι A : Type*) [Unique ι] [Add A] [Mul A] [SMul R A] [Star A] :
    (ι → A) ≃⋆ₐ[R] A :=
  piUnique R (fun _ : ι ↦ A)

/-- Applying `StarAlgEquiv.funUnique` evaluates at `default`. -/
@[simp low]
theorem funUnique_apply {R ι A : Type*} [Unique ι] [Add A] [Mul A] [SMul R A] [Star A]
    (f : ι → A) :
    funUnique R ι A f = f default :=
  (rfl)

/-- Applying `(StarAlgEquiv.funUnique R ι A).symm a` at any index returns `a`. -/
@[simp low]
theorem funUnique_symm_apply {R ι A : Type*} [Unique ι] [Add A] [Mul A] [SMul R A] [Star A]
    (a : A) (i : ι) :
    (funUnique R ι A).symm a i = a := by
  cases Unique.eq_default i
  rfl

end Unique

end StarAlgEquiv
