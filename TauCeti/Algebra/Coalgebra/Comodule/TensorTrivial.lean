/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Coalgebra.Comodule.Trivial

/-!
# Tensor products of group-like and trivial comodules

This file records the basic tensor-product convention for right comodules over a bialgebra:
the tensor product of the group-like comodules attached to `g` and `h` is the existing
group-like comodule attached to `g * h` on `M ⊗[R] N`. In particular, tensor products of
trivial comodules use the existing `Comodule.trivial` structure on the tensor product.

No extra unbundled API is needed for these special cases. Use
`Comodule.groupLike (M := M ⊗[R] N) (g * h)` with `Comodule.Hom.ofGroupLike` for group-like
coactions, and `Comodule.trivial (M := M ⊗[R] N)` with `Comodule.Hom.ofTrivial` for trivial
coactions.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target
"Comodules over a coalgebra/Hopf algebra", where the finite-dimensional comodule category is
to become a rigid monoidal category. The fully general tensor product of comodules requires
the usual bialgebraic coaction formula; the group-like and trivial cases here are handled by
the existing group-like and trivial-comodule API.

## References

The group-like calculation uses Mathlib's `GroupLike` monoid structure from
`Mathlib.RingTheory.Bialgebra.GroupLike`, due to Yaël Dillies and Michał Mrugała.
-/

open scoped TensorProduct

namespace TauCeti

end TauCeti
