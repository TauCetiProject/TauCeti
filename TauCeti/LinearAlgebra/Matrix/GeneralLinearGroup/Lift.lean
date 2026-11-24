/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Lifting invertible matrices

An invertible matrix lifts along a surjective ring homomorphism that reflects units, such as the
quotient map by an ideal contained in the Jacobson radical: lift its entries arbitrarily, and the
determinant of the lift is a unit because its image is one.

This is the general-linear counterpart of `Matrix.SpecialLinearGroup.map_surjective`. It makes
reduction `GL_n(O) → GL_n(O ⧸ I)` surjective over a local ring `O`, so that indices of
congruence subgroups of `GL_n(O)` can be computed over `O ⧸ I`.

## Main declarations

* `Matrix.GeneralLinearGroup.map_surjective`: a surjective ring homomorphism that reflects units
  is surjective on general linear groups.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [DecidableEq n] [Fintype n] {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism that reflects units induces a surjection on general linear
groups, including for an empty index type. -/
theorem map_surjective (φ : R →+* S) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Function.Surjective (map (n := n) φ) := by
  intro g
  choose a ha using fun i j ↦ hφ ((g : Matrix n n S) i j)
  have hM : (Matrix.of a).map φ = g := Matrix.ext ha
  have hunit : IsUnit (Matrix.of a).det := (isUnit_map_iff φ _).mp (by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)
  refine ⟨mk'' (Matrix.of a) hunit, ext fun i j ↦ ?_⟩
  simp [ha]

end Matrix.GeneralLinearGroup
