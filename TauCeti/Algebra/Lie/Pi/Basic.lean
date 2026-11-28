/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Products of families of Lie algebras

A dependent product of Lie algebras carries the pointwise bracket. The coordinate projections
and single-coordinate inclusions are Lie homomorphisms, and distinct factors commute.
These maps allow invariant forms on finite products to be restricted to their factors.
The API follows the binary-product constructions in `Mathlib.Algebra.Lie.Prod`.
-/

public section

namespace LieAlgebra.Pi

variable {ι R : Type*} {L : ι → Type*} [CommRing R] [∀ i, LieRing (L i)]

instance instLieRing : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i ↦ add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i ↦ lie_add (x i) (y i) (z i)
  lie_self x := funext fun i ↦ lie_self (x i)
  leibniz_lie x y z := funext fun i ↦ leibniz_lie (x i) (y i) (z i)

@[simp]
theorem bracket_apply (x y : ∀ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := rfl

instance instLieAlgebra [∀ i, LieAlgebra R (L i)] : LieAlgebra R (∀ i, L i) where
  lie_smul r x y := funext fun i ↦ lie_smul r (x i) (y i)

/-- Single-coordinate elements from distinct factors commute. -/
theorem lie_single_single_of_ne [DecidableEq ι] {i j : ι} (hij : i ≠ j)
    (x : L i) (y : L j) : ⁅Pi.single i x, Pi.single j y⁆ = 0 := by
  ext k
  by_cases hik : i = k
  · subst k
    simp [hij.symm]
  · simp [Pi.single_eq_of_ne (Ne.symm hik)]

end LieAlgebra.Pi

namespace LieHom

variable {ι R : Type*} {L : ι → Type*} [CommRing R] [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra R (L i)]

/-- Projection from a product of Lie algebras to one factor. -/
def proj (i : ι) : (∀ i, L i) →ₗ⁅R⁆ L i where
  toLinearMap := LinearMap.proj i
  map_lie' := rfl

@[simp]
theorem proj_apply (i : ι) (x : ∀ i, L i) : proj (R := R) i x = x i := (rfl)

variable (R L) in
/-- Inclusion of a factor into a product of Lie algebras. -/
def single [DecidableEq ι] (i : ι) : L i →ₗ⁅R⁆ (∀ i, L i) where
  toLinearMap := LinearMap.single R L i
  map_lie' {x y} := by
    ext j
    by_cases h : i = j
    · subst j
      simp
    · simp [Pi.single_eq_of_ne (Ne.symm h)]

@[simp]
theorem single_apply [DecidableEq ι] (i : ι) (x : L i) :
    single R L i x = Pi.single i x := (rfl)

end LieHom
