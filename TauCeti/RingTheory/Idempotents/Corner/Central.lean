/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# The product decomposition along central idempotents, as algebras

Mathlib's `CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral` splits a semiring `A` with a
complete family of orthogonal central idempotents `eᵢ` as the product `A ≃+* ∏ᵢ eᵢ A eᵢ` of its
corner rings, by `x ↦ (eᵢ x eᵢ)ᵢ` with inverse `(yᵢ)ᵢ ↦ ∑ᵢ yᵢ`. When `A` is an algebra over a
commutative semiring `R`, each corner is an `R`-algebra with `algebraMap R (eAe) r = r • e`
(`IsIdempotentElem.Corner.instAlgebra`), and the ring isomorphism is `R`-linear. This file
records it as an isomorphism of `R`-algebras.

## Main definitions

* `CompleteOrthogonalIdempotents.algEquivOfIsMulCentral`: the `R`-algebra isomorphism
  `A ≃ₐ[R] ∏ᵢ eᵢ A eᵢ` defined by a complete family of orthogonal central idempotents.
-/

public section

namespace CompleteOrthogonalIdempotents

variable {R A ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype ι] {e : ι → A}

/-- **The product decomposition along central idempotents, as algebras.** A complete family of
orthogonal central idempotents `eᵢ` of an `R`-algebra `A` splits it as the product
`A ≃ₐ[R] ∏ᵢ eᵢ A eᵢ` of its corner algebras, by `x ↦ (eᵢ x eᵢ)ᵢ`. This is Mathlib's
`CompleteOrthogonalIdempotents.ringEquivOfIsMulCentral`, which is `R`-linear. -/
@[expose] def algEquivOfIsMulCentral (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ i, IsMulCentral (e i)) : A ≃ₐ[R] ∀ i, (he.idem i).Corner :=
  AlgEquiv.ofRingEquiv (f := he.ringEquivOfIsMulCentral hc) fun r ↦ funext fun i ↦
    Subtype.ext <| by
      change e i * algebraMap R A r * e i = r • e i
      rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
        (he.idem i).eq]

@[simp]
theorem algEquivOfIsMulCentral_apply_val (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ i, IsMulCentral (e i)) (x : A) (i : ι) :
    (he.algEquivOfIsMulCentral (R := R) hc x i).val = e i * x * e i :=
  rfl

@[simp]
theorem algEquivOfIsMulCentral_symm_apply (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ i, IsMulCentral (e i)) (y : ∀ i, (he.idem i).Corner) :
    (he.algEquivOfIsMulCentral (R := R) hc).symm y = ∑ i, (y i).val :=
  rfl

end CompleteOrthogonalIdempotents
