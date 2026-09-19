/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting a module along the range and the kernel of a linear map

For a linear map `f : M →ₗ[R] N` the first isomorphism theorem identifies `M ⧸ ker f` with
`range f`, so the cardinality of `M` is the product of the cardinalities of the range and of the
kernel. Both sides are `Nat.card`, which is `0` on an infinite type, so no finiteness hypothesis
is needed: the statement also says that `M` is infinite exactly when the range or the kernel is.

The second result records that the range of a linear map depends only on the map up to an
isomorphism of arrows: two linear maps intertwined by linear equivalences on the source and on
the target have ranges of the same cardinality.

Both are the counting steps of an exact-sequence argument, where a term is compared with the
image of the map leaving it and the image of the map entering it.
-/

public section

namespace LinearMap

section

variable {R M N M' N' : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- The cardinality of the source of a linear map is the product of the cardinalities of its
range and of its kernel. -/
theorem card_eq_card_range_mul_card_ker (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (range f) * Nat.card (ker f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv, Nat.mul_comm]

end

section

variable {R M N M' N' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']

/-- Linear maps intertwined by linear equivalences on the source and on the target have ranges
of the same cardinality. -/
theorem card_range_eq_card_range_of_comp_eq (f : M →ₗ[R] N) (f' : M' →ₗ[R] N') (e : M ≃ₗ[R] M')
    (e' : N ≃ₗ[R] N') (h : (e' : N →ₗ[R] N') ∘ₗ f = f' ∘ₗ (e : M →ₗ[R] M')) :
    Nat.card (range f) = Nat.card (range f') := by
  have hrange : range f' = Submodule.map (e' : N →ₗ[R] N') (range f) := by
    rw [← range_comp, h, range_comp, range_eq_top.2 e.surjective, Submodule.map_top]
  rw [hrange, Nat.card_congr (Submodule.equivMapOfInjective _ e'.injective _).toEquiv]

end

end LinearMap
