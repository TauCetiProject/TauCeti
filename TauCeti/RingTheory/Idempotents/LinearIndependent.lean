/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal nonzero idempotents are linearly independent

Let `k` be a ring whose multiplication cancels (`IsCancelMulZero`, so in particular any integral
domain), let `A` be a ring that is a torsion-free `k`-module -- no nonzero scalar annihilates a
nonzero element -- on which `k` acts compatibly with multiplication (`IsScalarTower k A A`, as for
any `k`-algebra), and let `e : ι → A` be a family of pairwise orthogonal idempotents, none of them
zero.
Then the `eᵢ` are linearly independent over `k`: multiplying a vanishing combination
`∑ᵢ gᵢ • eᵢ = 0` by `e_j` kills every term but the `j`-th, which orthogonality and idempotence
leave as `g_j • e_j = 0`.

Mathlib has orthogonal families of idempotents (`OrthogonalIdempotents`, in
`Mathlib/RingTheory/Idempotents.lean`) and the ring-theoretic decompositions they generate, but
records nothing about their linear independence, which is what makes a complete orthogonal family
of the right size a *basis*.

## Main results

* `OrthogonalIdempotents.linearIndependent`: **a family of pairwise orthogonal nonzero
  idempotents is linearly independent.**
-/

public section

/-- **A family of pairwise orthogonal nonzero idempotents of a ring `A` is linearly independent**
over a ring `k` with cancellative multiplication, provided `A` is a torsion-free `k`-module on which
`k` acts compatibly with multiplication (for example, a torsion-free `k`-algebra). -/
theorem OrthogonalIdempotents.linearIndependent {k A ι : Type*} [Ring k] [IsCancelMulZero k]
    [Ring A] [Module k A] [IsScalarTower k A A] [Module.IsTorsionFree k A] {e : ι → A}
    (he : OrthogonalIdempotents e) (he₀ : ∀ i, e i ≠ 0) : LinearIndependent k e := by
  classical
  rw [linearIndependent_iff']
  intro s g hg j hj
  simpa [Finset.sum_mul, smul_mul_assoc, he.mul_eq, he₀ j, hj] using congrArg (· * e j) hg
