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
and `LinearMap.baseChange` extends a linear map.  For a general map the two constructions satisfy
only the containment `(ker f).baseChange A ≤ ker (f.baseChange A)`; it is an equality when `A` is
flat over `R`, which is Mathlib's `Module.Flat.ker_lTensor_eq`.  This file records the other case
in which it is an equality: the kernel of a *surjective* map is computed correctly after extending
scalars along an arbitrary coefficient algebra, flat or not.

That is the form wanted when the map is a quotient map, where the kernel of the extension is to be
identified with the extension of the submodule quotiented by.

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
the coefficient algebra.  Dropping surjectivity, the same equality holds when `A` is flat over
`R`, which is Mathlib's `Module.Flat.ker_lTensor_eq`. -/
theorem ker_baseChange_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ker (f.baseChange A) = (ker f).baseChange A :=
  have h : Function.Exact ((ker f).subtype.baseChange A) (f.baseChange A) :=
    lTensor_exact A f.exact_subtype_ker_map hf
  h.linearMap_ker_eq

end LinearMap
