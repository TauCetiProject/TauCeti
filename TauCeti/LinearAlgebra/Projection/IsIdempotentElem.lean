/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection

/-!
# Ranges of orthogonal idempotents

Two idempotent linear endomorphisms `p` and `q` with `p * q = 0` have disjoint ranges, and if also
`q * p = 0`, then the range of `p + q` is the supremum of their ranges. These are the facts used to
add up the ranks of spectral projections onto disjoint sets.

## Main results

* `LinearMap.IsIdempotentElem.disjoint_range`: idempotents `p`, `q` with `p * q = 0` have disjoint
  ranges.
* `LinearMap.IsIdempotentElem.range_add`: the range of the sum of mutually orthogonal idempotents
  is the supremum of their ranges.
-/

public section

namespace LinearMap.IsIdempotentElem

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p q : M →ₗ[R] M}

/-- The ranges of idempotents `p` and `q` with `p * q = 0` are disjoint. -/
theorem disjoint_range (hp : IsIdempotentElem p) (hpq : p * q = 0) :
    Disjoint (range p) (range q) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have h1 : p (p a) = p a := congr($hp.eq a)
  have h2 : p (q b) = 0 := congr($hpq b)
  rw [← h1, ← hb, h2]

/-- The range of the sum of idempotents `p` and `q` with `p * q = 0` and `q * p = 0` is the
supremum of their ranges. -/
theorem range_add (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (hpq : p * q = 0)
    (hqp : q * p = 0) : range (p + q) = range p ⊔ range q := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, rfl⟩
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨p x, ?_⟩
    simp [← mul_apply_eq_comp, hp.eq, hqp]
  · rintro _ ⟨x, rfl⟩
    refine ⟨q x, ?_⟩
    simp [← mul_apply_eq_comp, hq.eq, hpq]

end LinearMap.IsIdempotentElem
