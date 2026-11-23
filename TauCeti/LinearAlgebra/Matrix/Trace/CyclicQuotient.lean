/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.Algebra.CyclicQuotient

/-!
# Matrix traces vanish on the commutator submodule

The trace of a finite square matrix whose entries form an additive commutative monoid with a
commutative multiplication is invariant under exchanging the two factors of a product.  Hence the
trace of a multiplicative `k`-linear map `f` to such matrices kills the commutator submodule
`TauCeti.commutatorSubmodule` over `k`, and an element `x` with `(f x).trace ≠ 0` has nonzero
class in the cyclic quotient `A / [A, A]`.

## Main results

* `TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule`: for a multiplicative `k`-linear map `f`
  from `A` to square matrices with finitely many indices and entries in a commutative magma `R`
  which is an additive `k`-module, the trace of `f x` vanishes for every `x` in the commutator
  submodule over `k`.
-/

public section

namespace TauCeti

/-- **The trace of a matrix representation kills commutators**: if `f` is a multiplicative
`k`-linear map to square matrices with finitely many indices and entries in `R`, where `R` is an
additive `k`-module with a commutative (not necessarily distributive or associative)
multiplication, then the trace of `f x` vanishes for every `x` in the commutator submodule. -/
theorem trace_map_eq_zero_of_mem_commutatorSubmodule {k A n R F : Type*} [Semiring k]
    [NonUnitalNonAssocRing A] [Module k A] [Fintype n] [AddCommMonoid R] [CommMagma R]
    [Module k R] [FunLike F A (Matrix n n R)] [MulHomClass F A (Matrix n n R)]
    [LinearMapClass F k A (Matrix n n R)] (f : F) {x : A} (hx : x ∈ commutatorSubmodule k A) :
    (f x).trace = 0 := by
  -- the trace of `f`, as a `k`-linear map, is invariant under exchanging the factors of a product
  have hle := (commutatorSubmodule_le_ker_iff
    ((Matrix.traceLinearMap n k R).comp (f : A →ₗ[k] Matrix n n R))).2 fun x y => by
      simpa only [LinearMap.comp_apply, LinearMap.coe_ofClass, map_mul,
        Matrix.traceLinearMap_apply] using Matrix.trace_mul_comm (f x) (f y)
  simpa only [LinearMap.comp_apply, LinearMap.coe_ofClass, Matrix.traceLinearMap_apply] using
    LinearMap.mem_ker.1 (hle hx)

end TauCeti
