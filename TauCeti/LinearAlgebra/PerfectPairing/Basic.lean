/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Transfer of module properties along perfect pairings

A perfect pairing `p : M →ₗ[R] N →ₗ[R] R` identifies `M` with `Dual R N`. Consequently, freeness
and finiteness of `N` transfer across `p` to `M`.

## Main results

* `Module.Free.of_isPerfPair`: if `p : M →ₗ[R] N →ₗ[R] R` is a perfect pairing and `N` is finite and
  free over `R`, then `M` is free over `R`.
* `Module.Finite.of_isPerfPair`: if `p : M →ₗ[R] N →ₗ[R] R` is a perfect pairing and `N` is finite
  and projective over `R`, then `M` is finite over `R`.
-/

public section

namespace Module

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]

include p in
/-- If `p : M →ₗ[R] N →ₗ[R] R` is a perfect pairing and `N` is finite and free over `R`, then
`M` is free over `R`. -/
theorem Free.of_isPerfPair [Free R N] [Module.Finite R N] : Free R M :=
  .of_equiv p.toPerfPair.symm

include p in
/-- If `p : M →ₗ[R] N →ₗ[R] R` is a perfect pairing and `N` is finite and projective over `R`,
then `M` is finite over `R`. -/
theorem Finite.of_isPerfPair [Projective R N] [Module.Finite R N] : Module.Finite R M :=
  .equiv p.toPerfPair.symm

end CommSemiring

end Module
