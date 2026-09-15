/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Replaying binary linear certificates over rings of characteristic two

A left inverse computed over `ZMod 2` remains a left inverse after mapping its entries into any
commutative ring of characteristic two. This is the small trusted bridge used by the homogeneous
blocks of the type-F4 derivation calculation.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- A binary left-inverse certificate proves that the corresponding system has trivial kernel over
any commutative ring of characteristic two. -/
theorem eq_zero_of_modTwo_leftInverse {R : Type*} [CommRing R] [CharP R 2]
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n (ZMod 2)) (B : Matrix n m (ZMod 2)) (hBA : B * A = 1)
    (x : n → R) (hx : A.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0) : x = 0 := by
  have hm : B.map (ZMod.castHom dvd_rfl R) * A.map (ZMod.castHom dvd_rfl R) = 1 := by
    rw [← Matrix.map_mul, hBA,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  have h := congrArg (fun y => B.map (ZMod.castHom dvd_rfl R) *ᵥ y) hx
  rw [mulVec_mulVec, hm, one_mulVec, mulVec_zero] at h
  exact h

end TauCeti.F4ShortRoot
