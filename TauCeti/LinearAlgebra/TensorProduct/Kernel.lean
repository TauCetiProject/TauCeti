/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kernels after extension of scalars

Mathlib's `Submodule.baseChange` extends a submodule of `M` to an `A`-submodule of `A ⊗[R] M`,
and `LinearMap.baseChange` extends a linear map.  The two constructions commute with taking
kernels as soon as tensoring with `A` keeps the pair `ker f ↪ M → N` exact, which happens for two
unrelated reasons: `A` may be flat, or `f` may be surjective, in which case plain right-exactness
of the tensor product suffices.  The containment `(ker f).baseChange A ≤ ker (f.baseChange A)`
holds for any `A` and any `f`; it is the reverse one that needs an argument.

## Main results

* `LinearMap.ker_baseChange`: **over a flat coefficient algebra the kernel of an extended linear
  map is the extension of its kernel.**
* `LinearMap.ker_baseChange_of_surjective`: the same conclusion for a surjective map, with no
  hypothesis on the coefficient algebra.

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

section CommRing

variable [CommRing A] [Algebra R A]

/-- **Over a flat coefficient algebra, extension of scalars commutes with kernels.**  This is
Mathlib's `Module.Flat.ker_lTensor_eq` read in the `LinearMap.baseChange` and
`Submodule.baseChange` idiom, the coefficient algebra playing the role of the flat module. -/
theorem ker_baseChange [Module.Flat R A] (f : M →ₗ[R] N) :
    ker (f.baseChange A) = (ker f).baseChange A :=
  Module.Flat.ker_lTensor_eq A A f

end CommRing

section Ring

variable [Ring A] [Algebra R A]

/-- **Extension of scalars commutes with the kernel of a surjective map**, with no hypothesis on
the coefficient algebra: the pair `ker f ↪ M → N → 0` is right exact, and the tensor product
preserves right-exact sequences. -/
theorem ker_baseChange_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    ker (f.baseChange A) = (ker f).baseChange A := by
  have hexact := lTensor_exact A (exact_subtype_ker_map f) hf
  refine Submodule.ext fun x => ?_
  rw [mem_ker, baseChange_eq_ltensor, Submodule.baseChange, mem_range]
  exact (hexact x).trans (exists_congr fun y => by rw [baseChange_eq_ltensor])

end Ring

end LinearMap
