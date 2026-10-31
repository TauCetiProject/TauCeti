/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Span

/-!
# Generators of a module isomorphic to the base ring

A generator of a module `N`, that is an element `x` with `span K {x} = ⊤`, is carried by a linear
isomorphism `N ≃ₗ[K] K` to a generator of the ideal `⊤`, that is to a unit of `K`
(`Submodule.span_image_linearEquiv`, `Ideal.span_singleton_eq_top`). So when `1` is the only unit
of the commutative semiring `K`, as for `ZMod 2`, a module isomorphic to `K` has exactly one
generator. This is what makes Thom classes with such coefficients unique on every fibre, without
any orientation.

## Main results

* `LinearEquiv.eq_of_span_singleton_eq_top`: a module isomorphic to a commutative semiring whose
  only unit is `1` has a single generator.
-/

public section

namespace LinearEquiv

/-- **A module isomorphic to `K` has a single generator when `1` is the only unit of `K`**: two
elements `x` and `y` of a module `N ≃ₗ[K] K` with `span K {x} = ⊤` and `span K {y} = ⊤` are
equal. -/
theorem eq_of_span_singleton_eq_top {K N : Type*} [CommSemiring K] [Subsingleton Kˣ]
    [AddCommMonoid N] [Module K N] (φ : N ≃ₗ[K] K) {x y : N}
    (hx : Submodule.span K {x} = ⊤) (hy : Submodule.span K {y} = ⊤) : x = y := by
  -- A generator is carried by `φ` to a generator of the ideal `⊤`, that is to a unit.
  have hunit {z : N} (hz : Submodule.span K {z} = ⊤) : IsUnit (φ z) := by
    rw [← Ideal.span_singleton_eq_top, Ideal.span, ← Set.image_singleton,
      Submodule.span_image_linearEquiv, hz, Submodule.map_top, LinearEquiv.range]
  exact φ.injective (by
    rw [← (hunit hx).unit_spec, ← (hunit hy).unit_spec, Subsingleton.elim (hunit hx).unit])

end LinearEquiv
