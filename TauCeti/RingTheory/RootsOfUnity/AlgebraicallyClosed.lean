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
separably closed field `E` in which `n` is nonzero. Whether `n` is nonzero only depends on the
characteristic, which is shared by all nontrivial algebras over a field `K`. Hence `E` contains a
primitive `n`-th root of unity as soon as some domain over `K` does. For instance, the separable
closure of `K` contains every primitive root of unity found in an algebraic closure of `K`.

## Main results

* `IsPrimitiveRoot.exists_isPrimitiveRoot_of_isSepClosed`: a separably closed field over `K`
  contains a primitive `n`-th root of unity as soon as some domain over `K` does.
-/

public section

namespace TauCeti

/-- A separably closed field `E` over a field `K` contains a primitive `n`-th root of unity as soon
as some domain `M` over `K` does. -/
theorem _root_.IsPrimitiveRoot.exists_isPrimitiveRoot_of_isSepClosed (K : Type*) {E M : Type*}
    [Field K] [Field E] [IsSepClosed E] [Algebra K E] [CommRing M] [IsDomain M] [Algebra K M]
    {n : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ n) :
    ∃ ξ : E, IsPrimitiveRoot ξ n := by
  obtain rfl | hn := eq_or_ne n 0
  · exact ⟨0, .zero⟩
  -- For `n ≠ 0`, `n` is nonzero in `M`, hence in `K` and in `E`.
  have := NeZero.mk hn
  have := hζ.neZero'
  have : NeZero (n : K) := .of_map (algebraMap K M) (neZero := by rwa [map_natCast])
  have : NeZero (n : E) := .nat_of_injective (algebraMap K E).injective
  exact HasEnoughRootsOfUnity.exists_primitiveRoot E n

end TauCeti
