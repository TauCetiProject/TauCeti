/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The range of a sum of orthogonal idempotents

Two idempotent endomorphisms `p` and `q` are orthogonal when `p * q = 0` and `q * p = 0`. Their
sum is then idempotent, and its range is the internal direct sum of the two ranges: the ranges are
disjoint and span the range of `p + q`. In particular ranks add, which is how the dimensions of
spectral subspaces for disjoint parts of a spectrum are compared.

## Main results

* `LinearMap.IsIdempotentElem.disjoint_range_of_mul_eq_zero`: if `p * q = 0` and `p` is idempotent,
  the ranges of `p` and `q` are disjoint.
* `LinearMap.IsIdempotentElem.range_add_of_mul_eq_zero`: the range of a sum of orthogonal
  idempotents is the supremum of their ranges.
* `LinearMap.IsIdempotentElem.finrank_range_add_of_mul_eq_zero`: the rank of a sum of orthogonal
  idempotents of finite rank is the sum of their ranks.
-/

public section

open Module

namespace LinearMap

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {p q : Module.End R M}

/-- If `p` is idempotent and `p * q = 0`, the ranges of `p` and `q` meet only in `0`. -/
theorem IsIdempotentElem.disjoint_range_of_mul_eq_zero (hp : IsIdempotentElem p)
    (hpq : p * q = 0) : Disjoint (range p) (range q) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  calc p a = p (p a) := congr($hp.eq a).symm
    _ = p (q b) := by rw [hb]
    _ = 0 := congr($hpq b)

/-- The range of a sum of orthogonal idempotents is the supremum of their ranges. -/
theorem IsIdempotentElem.range_add_of_mul_eq_zero (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hpq : p * q = 0) (hqp : q * p = 0) :
    range (p + q) = range p ⊔ range q := by
  refine le_antisymm (range_add_le p q) (sup_le ?_ ?_)
  · rintro _ ⟨a, rfl⟩
    exact ⟨p a, by simpa using congr($hp.eq a + $hqp a)⟩
  · rintro _ ⟨a, rfl⟩
    exact ⟨q a, by simpa using congr($hpq a + $hq.eq a)⟩

end Semiring

section DivisionRing

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] {p q : Module.End K M}

/-- The rank of a sum of orthogonal idempotents of finite rank is the sum of their ranks. -/
theorem IsIdempotentElem.finrank_range_add_of_mul_eq_zero (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hpq : p * q = 0) (hqp : q * p = 0)
    [FiniteDimensional K (range p)] [FiniteDimensional K (range q)] :
    finrank K (range (p + q)) = finrank K (range p) + finrank K (range q) := by
  rw [IsIdempotentElem.range_add_of_mul_eq_zero hp hq hpq hqp,
    ← Submodule.finrank_sup_add_finrank_inf_eq,
    (IsIdempotentElem.disjoint_range_of_mul_eq_zero hp hpq).eq_bot, finrank_bot, add_zero]

end DivisionRing

end LinearMap
