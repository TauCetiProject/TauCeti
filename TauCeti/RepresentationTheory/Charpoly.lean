/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RepresentationTheory.Intertwining
import TauCeti.LinearAlgebra.Charpoly.Dual
import TauCeti.LinearAlgebra.Charpoly.Inverse

/-!
# Characteristic polynomials of representations

For a representation `ρ` of a monoid on a finite free module and an element `g`, the
characteristic polynomial of `ρ g` is invariant under isomorphism of representations,
multiplicative on products, and equal to `(X - 1) ^ dim V` for the trivial representation.

For a representation of a group, `g⁻¹` acts with the reverse of the characteristic polynomial of
`g`, up to a unit, and so does `g` in the contragredient representation `ρ.dual`. Hence in any
field over the coefficients, the characteristic roots of `g` in `ρ.dual` are the inverses of those
of `g` in `ρ`, counted with multiplicity. Applied to a Frobenius element, this compares the
eigenvalues of arithmetic and geometric Frobenius.

## Main results

* `Representation.Equiv.charpoly_apply_eq`: invariance under isomorphism.
* `Representation.charpoly_prod_apply`: multiplicativity on products.
* `Representation.charpoly_trivial_apply`: the characteristic polynomial of the trivial
  representation.
* `Representation.charpoly_apply_inv`, `Representation.aroots_charpoly_apply_inv`: the
  characteristic polynomial and the characteristic roots of `g⁻¹`.
* `Representation.charpoly_dual_apply`, `Representation.aroots_charpoly_dual_apply`: the
  characteristic polynomial and the characteristic roots of `g` in the contragredient
  representation.
-/

public section

open Module Polynomial

namespace Representation

variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

section Monoid

variable {G : Type*} [Monoid G] {ρ : Representation R G V} {σ : Representation R G W}

/-- Isomorphic representations have the same characteristic polynomials. -/
theorem Equiv.charpoly_apply_eq (φ : ρ.Equiv σ) (g : G) : (ρ g).charpoly = (σ g).charpoly := by
  rw [← φ.conj_apply_self g, LinearEquiv.charpoly_conj]

variable (ρ σ) in
/-- The characteristic polynomial is multiplicative on products of representations. -/
@[simp]
theorem charpoly_prod_apply (g : G) :
    (ρ.prod σ g).charpoly = (ρ g).charpoly * (σ g).charpoly :=
  LinearMap.charpoly_prodMap (ρ g) (σ g)

variable (R G V) in
/-- Every element acts with characteristic polynomial `(X - 1) ^ dim V` in the trivial
representation. -/
@[simp]
theorem charpoly_trivial_apply (g : G) : (trivial R G V g).charpoly = (X - 1) ^ finrank R V := by
  nontriviality R
  rw [isTrivial_def, ← Module.End.one_eq_id, LinearMap.charpoly_one]

end Monoid

section Group

variable {G : Type*} [Group G] (ρ : Representation R G V)

/-- In a representation of a group on a finite free module of rank `d`, the characteristic
polynomial of `g⁻¹` is `(-1) ^ d * det (ρ g⁻¹)` times the reverse `det (1 - X ρ(g))` of that of
`g`. -/
theorem charpoly_apply_inv (g : G) :
    (ρ g⁻¹).charpoly = (-1) ^ finrank R V * C (LinearMap.det (ρ g⁻¹)) * (ρ g).charpoly.reverse :=
  LinearMap.charpoly_of_mul_eq_one (by rw [← map_mul, inv_mul_cancel, map_one])

/-- In a representation of a group on a finite free module, the characteristic roots of `g⁻¹` in
a field `S` are the inverses of those of `g`, counted with multiplicity. -/
theorem aroots_charpoly_apply_inv {S : Type*} [Field S] [Algebra R S] (g : G) :
    (ρ g⁻¹).charpoly.aroots S = ((ρ g).charpoly.aroots S).map (·⁻¹) :=
  LinearMap.aroots_charpoly_of_mul_eq_one (by rw [← map_mul, inv_mul_cancel, map_one])

/-- In the contragredient representation, `g` acts with the characteristic polynomial of `g⁻¹`
in the original representation. -/
theorem charpoly_dual_apply (g : G) : (ρ.dual g).charpoly = (ρ g⁻¹).charpoly := by
  rw [dual_apply, ← LinearMap.dualMap_def, LinearMap.charpoly_dualMap]

/-- The characteristic roots of `g` in the contragredient representation, in a field `S`, are the
inverses of those of `g` in the original representation, counted with multiplicity. -/
theorem aroots_charpoly_dual_apply {S : Type*} [Field S] [Algebra R S] (g : G) :
    (ρ.dual g).charpoly.aroots S = ((ρ g).charpoly.aroots S).map (·⁻¹) := by
  rw [charpoly_dual_apply, aroots_charpoly_apply_inv]

end Group

end Representation
