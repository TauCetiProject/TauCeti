/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Primitive roots of unity in separably closed fields

Mathlib's `IsSepClosed.hasEnoughRootsOfUnity` provides primitive `n`-th roots of unity in a
separably closed field `E` in which `n` is nonzero. If `n` is nonzero in some algebra over a
commutative semiring `K`, then it is nonzero in `K`, hence in every algebra over `K` in which `K`
embeds. Hence a separably closed field `E` into which `K` embeds contains a primitive `n`-th root of
unity as soon as some domain over `K` does. For instance, the separable closure of a field `K`
contains every primitive root of unity found in an algebraic closure of `K`, and a separably closed
field of characteristic zero (take `K = ℕ`) contains every primitive root of unity found in a domain
of characteristic zero.

## Main results

* `IsPrimitiveRoot.exists_isPrimitiveRoot_of_isSepClosed`: a separably closed field into which `K`
  embeds contains a primitive `n`-th root of unity as soon as some domain over `K` does.
-/

public section

namespace IsPrimitiveRoot

/-- A separably closed field `E` that is a faithful algebra over a commutative semiring `K` (for
instance any field extension of a field `K`) contains a primitive `n`-th root of unity as soon as
some domain `M` over `K` does. -/
theorem exists_isPrimitiveRoot_of_isSepClosed (K : Type*) {E M : Type*}
    [CommSemiring K] [Field E] [IsSepClosed E] [Algebra K E] [FaithfulSMul K E]
    [CommRing M] [IsDomain M] [Algebra K M]
    {n : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ξ : E, IsPrimitiveRoot ξ n := by
  obtain rfl | hn := eq_or_ne n 0
  · exact ⟨0, .zero⟩
  -- For `n ≠ 0`, `n` is nonzero in `M`, hence in `K` and in `E`.
  have := NeZero.mk hn
  have := hζ.neZero'
  have : NeZero (n : K) := .of_map (algebraMap K M) (neZero := by rwa [map_natCast])
  have : NeZero (n : E) := .nat_of_injective (FaithfulSMul.algebraMap_injective K E)
  exact HasEnoughRootsOfUnity.exists_isPrimitiveRoot E n

end IsPrimitiveRoot
