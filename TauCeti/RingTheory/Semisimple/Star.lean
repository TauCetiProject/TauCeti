/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Artinian rings with a proper involution

A left Artinian star ring with a proper involution is semisimple. In particular, this applies
to finite-dimensional star algebras with a positive definite regular trace form, without
requiring a C*-norm or a completion.

Properness means that `star x * x = 0` implies `x = 0`. If `x` belongs to the Jacobson radical,
then so does `star x * x`, since the radical is a left ideal. The radical is nilpotent, while
a nilpotent self-adjoint element in a proper star ring is zero. Thus the radical vanishes.
No invariance of the radical under star needs to be assumed.

This abstracts the radical argument used in `TauCeti.BrauerAlgebra.isSemisimpleRing_of_le`
for faithful orthogonal Brauer matrices: properness replaces the matrix realization.
-/

public section

namespace TauCeti

/-- A left Artinian ring with a proper involution is semisimple. -/
theorem isSemisimpleRing_of_isProperStar (A : Type*) [Ring A] [StarRing A]
    [IsArtinianRing A] [IsProperStar A] : IsSemisimpleRing A := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  obtain ⟨m, hm⟩ := (IsSemiprimaryRing.isNilpotent : IsNilpotent (Ring.jacobson A))
  refine eq_bot_iff.mpr fun x hx => ?_
  have hnil : IsNilpotent (star x * x) := by
    refine ⟨m, ?_⟩
    have hpow := Ideal.pow_mem_pow ((Ring.jacobson A).smul_mem (star x) hx) m
    simpa only [hm, Ideal.zero_eq_bot, Ideal.mem_bot, smul_eq_mul] using hpow
  exact (Submodule.mem_bot _).mpr
    (star_mul_self_eq_zero.mp ((IsSelfAdjoint.star_mul_self x).eq_zero_of_isNilpotent hnil))

end TauCeti
