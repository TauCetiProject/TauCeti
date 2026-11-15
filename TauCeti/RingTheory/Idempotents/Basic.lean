/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal idempotents under nonunital homomorphisms and in product semirings

Mathlib's `OrthogonalIdempotents.map` pushes a family of pairwise orthogonal idempotents along a
unital ring homomorphism `R →+* S`, and `CompleteOrthogonalIdempotents.single` shows that the
coordinate units `Pi.single · 1` in a finite dependent product of semirings form a complete
orthogonal idempotent family. Neither idempotency nor pairwise orthogonality uses `map_one` or
finiteness of the index type: this file provides the corresponding nonunital pushforward
`OrthogonalIdempotents.map'` and arbitrary-index coordinate family `OrthogonalIdempotents.single`.

## Main results

* `OrthogonalIdempotents.map'`: push `OrthogonalIdempotents` forward along any map preserving `*`
  and `0` (in particular any nonunital ring or algebra homomorphism).
* `OrthogonalIdempotents.single`: the coordinate units `Pi.single · 1` in `∀ i, R i` form a family
  of pairwise orthogonal idempotents.
-/

public section

namespace OrthogonalIdempotents

/-- Push a family of pairwise orthogonal idempotents forward along any map preserving multiplication
and `0` (such as a nonunital ring or algebra homomorphism), generalizing
`OrthogonalIdempotents.map` from unital `RingHom`s. -/
theorem map' {R S F I : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [MulHomClass F R S] [ZeroHomClass F R S] {e : I → R}
    (he : OrthogonalIdempotents e) (f : F) : OrthogonalIdempotents (f ∘ e) := by
  classical
  simp [iff_mul_eq, he.mul_eq, ← map_mul f, apply_ite f]

/-- In a dependent product of semirings, the coordinate units `Pi.single · 1` form a family of
pairwise orthogonal idempotents (without assuming finiteness of the index type). -/
theorem single {I : Type*} [DecidableEq I] (R : I → Type*) [∀ i, Semiring (R i)] :
    OrthogonalIdempotents (Pi.single (M := R) · 1) where
  idem i := by rw [IsIdempotentElem, ← Pi.single_mul, one_mul]
  ortho _ _ hij := by
    dsimp only
    rw [← Pi.single_mul_left, Pi.single_eq_of_ne hij, mul_zero, Pi.single_zero]

end OrthogonalIdempotents
