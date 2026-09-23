/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Kernels after extension of scalars

Mathlib's `Submodule.baseChange` extends a submodule of `M` to an `A`-submodule of `A ⊗[R] M`,
and `LinearMap.baseChange` extends a linear map.  The two constructions commute with taking
kernels as soon as tensoring with `A` keeps the pair `ker f ↪ M → N` exact.  Over a flat
coefficient algebra that is `Module.Flat.ker_lTensor_eq`; this file records the other reason it
can happen, namely that `f` is surjective, in which case plain right-exactness of the tensor
product suffices and `A` is arbitrary.  The containment
`(ker f).baseChange A ≤ ker (f.baseChange A)` holds for any `A` and any `f`; it is the reverse
one that needs an argument.

## Main results

* `LinearMap.ker_baseChange_of_surjective`: **for a surjective map the kernel of an extended
  linear map is the extension of its kernel**, with no hypothesis on the coefficient algebra.

## References

* [N. Bourbaki, *Algebra I, Chapters 1-3*][bourbaki1989], Chapter II, §3, n°6, for the exactness
  properties of the tensor product.
-/

public section

open TensorProduct

namespace LinearMap

universe u v w x

variable {R : Type u} (A : Type v) {M : Type w} {N : Type x}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Ring A] [Algebra R A]

/-- **Extension of scalars commutes with the kernel of a surjective map**, with no hypothesis on
the coefficient algebra: the pair `ker f ↪ M → N → 0` is right exact, and the tensor product
preserves right-exact sequences. -/
theorem ker_baseChange_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ker (f.baseChange A) = (ker f).baseChange A :=
  have h : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) :=
    lTensor_exact A f.exact_subtype_ker_map hf
  h.linearMap_ker_eq

end LinearMap
