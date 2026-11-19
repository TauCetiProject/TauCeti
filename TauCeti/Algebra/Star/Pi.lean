/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Direct products of star-algebra equivalences

This file builds `StarAlgEquiv` constructors on indexed product types `∀ i, A i`, transporting
componentwise star-algebra equivalences, index equivalences, and unique-index products without
assuming multiplicative identities on the factors. These constructors assemble blockwise
decompositions of star algebras—such as finite-dimensional C⋆-algebras into matrix blocks—and
collapse single-block products `Fin 1 → A` to `A`.

## Main definitions

* `StarAlgEquiv.piCongrRight`: combine a family `∀ i, A₁ i ≃⋆ₐ[R] A₂ i` into
  `(∀ i, A₁ i) ≃⋆ₐ[R] ∀ i, A₂ i`.
* `StarAlgEquiv.piCongrLeft'` and `StarAlgEquiv.piCongrLeft`: transport `(∀ i, A i)` along an
  equivalence of index types.
* `StarAlgEquiv.piUnique` and `StarAlgEquiv.funUnique`: collapse `∀ i, A i` and `ι → S` over a
  `Unique` index type.

## Attribution

The API design and `[simp low]` normal-form conventions follow `AlgEquiv.piCongrRight`,
`AlgEquiv.piCongrLeft'`, `AlgEquiv.piCongrLeft`, and `AlgEquiv.funUnique` in
`Mathlib/Algebra/Algebra/Pi.lean`.
-/

public section

namespace StarAlgEquiv

section PiCongrRight

variable {ι R : Type*} {A₁ A₂ A₃ : ι → Type*}
  [∀ i, Add (A₁ i)] [∀ i, Mul (A₁ i)] [∀ i, SMul R (A₁ i)] [∀ i, Star (A₁ i)]
  [∀ i, Add (A₂ i)] [∀ i, Mul (A₂ i)] [∀ i, SMul R (A₂ i)] [∀ i, Star (A₂ i)]
  [∀ i, Add (A₃ i)] [∀ i, Mul (A₃ i)] [∀ i, SMul R (A₃ i)] [∀ i, Star (A₃ i)]

/-- Combine a family of star-algebra equivalences `∀ i, A₁ i ≃⋆ₐ[R] A₂ i` into an equivalence of
dependent products `(∀ i, A₁ i) ≃⋆ₐ[R] ∀ i, A₂ i`. -/
def piCongrRight (e : ∀ i, A₁ i ≃⋆ₐ[R] A₂ i) : (∀ i, A₁ i) ≃⋆ₐ[R] ∀ i, A₂ i where
  toFun x i := e i (x i)
  invFun y i := (e i).symm (y i)
  left_inv x := funext fun i ↦ (e i).symm_apply_apply (x i)
  right_inv y := funext fun i ↦ (e i).apply_symm_apply (y i)
  map_mul' x y := funext fun i ↦ map_mul (e i) (x i) (y i)
  map_add' x y := funext fun i ↦ map_add (e i) (x i) (y i)
  map_star' x := funext fun i ↦ map_star (e i) (x i)
  map_smul' r x := funext fun i ↦ map_smul (e i) r (x i)

@[simp]
theorem piCongrRight_apply (e : ∀ i, A₁ i ≃⋆ₐ[R] A₂ i) (x : ∀ i, A₁ i) (i : ι) :
    piCongrRight e x i = e i (x i) :=
  (rfl)

@[simp]
theorem piCongrRight_refl :
    (piCongrRight fun i ↦ (StarAlgEquiv.refl R (A₁ i))) = StarAlgEquiv.refl R (∀ i, A₁ i) :=
  (rfl)

@[simp]
theorem piCongrRight_symm (e : ∀ i, A₁ i ≃⋆ₐ[R] A₂ i) :
    (piCongrRight e).symm = piCongrRight fun i ↦ (e i).symm :=
  (rfl)

@[simp]
theorem piCongrRight_trans (e₁ : ∀ i, A₁ i ≃⋆ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃⋆ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = piCongrRight fun i ↦ (e₁ i).trans (e₂ i) :=
  (rfl)

end PiCongrRight

section PiCongrLeft

variable (R : Type*) {ι : Type*} (A : ι → Type*)
  [∀ i, Add (A i)] [∀ i, Mul (A i)] [∀ i, SMul R (A i)] [∀ i, Star (A i)]

/-- Transport dependent star algebras along an equivalence of the index type.

This is `Equiv.piCongrLeft'` bundled as a `StarAlgEquiv`. -/
def piCongrLeft' {ι' : Type*} (e : ι ≃ ι') : (∀ i, A i) ≃⋆ₐ[R] ∀ j, A (e.symm j) where
  __ := Equiv.piCongrLeft' A e
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

-- Priority `low` ensures generic `map_{add, mul, star, smul}` lemmas fire first.
@[simp low]
theorem piCongrLeft'_apply {ι' : Type*} (e : ι ≃ ι') (x : ∀ i, A i) :
    piCongrLeft' R A e x = Equiv.piCongrLeft' A e x :=
  (rfl)

@[simp low]
theorem piCongrLeft'_symm_apply {ι' : Type*} (e : ι ≃ ι') (x : ∀ j, A (e.symm j)) :
    (piCongrLeft' R A e).symm x = (Equiv.piCongrLeft' A e).symm x :=
  (rfl)

/-- Transport dependent star algebras along an equivalence of the index type, oriented toward
simplification.

This is `Equiv.piCongrLeft` bundled as a `StarAlgEquiv`. -/
def piCongrLeft {ι' : Type*} (e : ι' ≃ ι) : (∀ j, A (e j)) ≃⋆ₐ[R] ∀ i, A i :=
  (piCongrLeft' R A e.symm).symm

@[simp low]
theorem piCongrLeft_apply {ι' : Type*} (e : ι' ≃ ι) (x : ∀ j, A (e j)) :
    piCongrLeft R A e x = Equiv.piCongrLeft A e x :=
  (rfl)

@[simp low]
theorem piCongrLeft_symm_apply {ι' : Type*} (e : ι' ≃ ι) (x : ∀ i, A i) :
    (piCongrLeft R A e).symm x = (Equiv.piCongrLeft A e).symm x :=
  (rfl)

/-- Over a `Unique` index type, a dependent product `∀ i, A i` is star-algebra equivalent to
`A default`. -/
def piUnique [Unique ι] : (∀ i, A i) ≃⋆ₐ[R] A default where
  __ := Equiv.piUnique A
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp low]
theorem piUnique_apply [Unique ι] (x : ∀ i, A i) :
    piUnique R A x = Equiv.piUnique A x :=
  (rfl)

@[simp low]
theorem piUnique_symm_apply [Unique ι] (x : A default) :
    (piUnique R A).symm x = (Equiv.piUnique A).symm x :=
  (rfl)

end PiCongrLeft

section FunUnique

variable (R ι S : Type*) [Unique ι] [Add S] [Mul S] [SMul R S] [Star S]

/-- If `ι` has a unique element, then `ι → S` is isomorphic to `S` as a star algebra over `R`. -/
def funUnique : (ι → S) ≃⋆ₐ[R] S :=
  piUnique R fun _ : ι ↦ S

@[simp low]
theorem funUnique_apply (x : ι → S) :
    funUnique R ι S x = Equiv.funUnique ι S x :=
  (rfl)

@[simp low]
theorem funUnique_symm_apply (x : S) :
    (funUnique R ι S).symm x = (Equiv.funUnique ι S).symm x :=
  (rfl)

end FunUnique

end StarAlgEquiv
