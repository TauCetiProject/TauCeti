/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Characteristic polynomials of base-changed representations

The characteristic polynomials of a representation on a finite free module are compatible with
scalar extension: `charpoly ((A ⊗ ρ) g)` is the image of `charpoly (ρ g)` in `A[X]`.
-/

public section

namespace Representation

variable {R G V : Type*} [CommRing R] [Monoid G] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- The characteristic polynomials of a base-changed representation are those of the original
representation, read in the larger ring of scalars. -/
theorem charpoly_baseChange_apply (ρ : Representation R G V) (A : Type*) [CommRing A]
    [Algebra R A] (g : G) :
    (baseChange A ρ g).charpoly = (ρ g).charpoly.map (algebraMap R A) := by
  rw [baseChange_apply, LinearMap.charpoly_baseChange]

end Representation
