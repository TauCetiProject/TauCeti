/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Characteristic polynomials of representations

For a representation `ρ` of a monoid on a finite free module and an element `g`, the
characteristic polynomial of `ρ g` is invariant under isomorphism of representations,
multiplicative on products, and equal to `(X - 1) ^ dim V` for the trivial representation.

## Main results

* `Representation.Equiv.charpoly_apply_eq`: invariance under isomorphism.
* `Representation.charpoly_prod_apply`: multiplicativity on products.
* `Representation.charpoly_trivial_apply`: the characteristic polynomial of the trivial
  representation.
-/

public section

open Module Polynomial

namespace Representation

variable {R G V W : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCommGroup W] [Module R W] [Module.Free R W]
  [Module.Finite R W] {ρ : Representation R G V} {σ : Representation R G W}

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

end Representation
