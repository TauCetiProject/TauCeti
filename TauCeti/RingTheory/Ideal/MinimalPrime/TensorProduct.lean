/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.RingTheory.Ideal.GoingDown

/-!
# Minimal primes of tensor products

Minimal primes behave well under extension of scalars along a flat algebra. If `L` is flat
over a commutative semiring `K`, a minimal prime of `L ⊗[K] A` contracts to a minimal prime of
the commutative ring `A`, because the tensor product is flat over `A` and satisfies going down.

For an ideal `I` of a commutative ring `A`, a minimal prime `Q` over the extension of `I` to
`E ⊗[K] A` is the extension of its contraction `P` whenever `E ⊗[K] (A ⧸ P)` is a domain.
The extension of `P` is then prime and lies between the extension of `I` and `Q`, so minimality
forces equality. This applies to components of arbitrary closed subsets as well as to minimal
primes of the whole tensor product.

## Main results

* `Ideal.eq_map_comap_includeRight_of_isDomain`: a minimal prime over an extended ideal is
  extended from its contraction when the tensor product of the contracted quotient is a domain.
* `Ideal.comap_includeRight_mem_minimalPrimes`: under flat scalar extension, minimal primes of
  a tensor product contract to minimal primes of the right factor.
-/

public section

open scoped TensorProduct
open Algebra.TensorProduct (includeRight)

namespace Ideal

section CommRing

variable {K : Type*} [CommRing K] {A : Type*} [CommRing A] [Algebra K A]

/-- A minimal prime `Q` over the extension of an ideal of `A` to `E ⊗[K] A` is the extension
of its contraction `P` from `A` to `E ⊗[K] A`, provided `E ⊗[K] (A ⧸ P)` is a domain. -/
theorem eq_map_comap_includeRight_of_isDomain {E : Type*} [CommRing E] [Algebra K E]
    (Q : Ideal (E ⊗[K] A)) {I : Ideal A} (hQ : Q ∈ (I.map includeRight).minimalPrimes)
    (hdom : IsDomain (E ⊗[K] (A ⧸ Q.comap includeRight))) :
    Q = (Q.comap includeRight).map includeRight := by
  have hPQ : (Q.comap includeRight).map includeRight ≤ Q := Ideal.map_le_iff_le_comap.mpr le_rfl
  refine Minimal.eq_of_ge (P := fun J : Ideal (E ⊗[K] A) ↦ J.IsPrime ∧ I.map includeRight ≤ J)
    hQ ⟨?_, ?_⟩ hPQ
  · -- `(E ⊗[K] A) ⧸ P.map includeRight` is `E ⊗[K] (A ⧸ P)`, a domain.
    have := (Algebra.TensorProduct.tensorQuotientEquiv (R := K) K A E (Q.comap includeRight)).symm
      |>.toMulEquiv.isDomain
    exact Ideal.Quotient.isDomain_iff_prime _ |>.mp this
  · exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mp hQ.le)

end CommRing

/-- A minimal prime of `L ⊗[K] A` contracts to a minimal prime of `A` when `L` is flat over `K`:
then `L ⊗[K] A` is flat over `A` and satisfies going down. -/
theorem comap_includeRight_mem_minimalPrimes
    {K : Type*} [CommSemiring K] {A : Type*} [CommRing A] [Algebra K A]
    {L : Type*} [CommRing L] [Algebra K L]
    [Module.Flat K L] (Q : Ideal (L ⊗[K] A)) (hQ : Q ∈ minimalPrimes (L ⊗[K] A)) :
    Q.comap (includeRight : A →ₐ[K] L ⊗[K] A) ∈ minimalPrimes A := by
  let := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := A)
  have : Module.Flat A (L ⊗[K] A) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight K A L).symm.toLinearEquiv
  simpa only [Ideal.under_def, Algebra.TensorProduct.algebraMap_eq_includeRight,
    Ideal.comap_coe] using
    (Ideal.under_mem_minimalPrimes (R := A) hQ)

end Ideal
