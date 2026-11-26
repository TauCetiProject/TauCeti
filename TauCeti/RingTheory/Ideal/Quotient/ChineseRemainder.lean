/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder

/-!
# The Chinese remainder equivalence for modules

If the ideals `Iᵢ` of a commutative ring `R` are pairwise coprime and finitely many, then for any
`R`-module `M` the natural map `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` is surjective with kernel `(⋂ᵢ Iᵢ) • M`
(Mathlib's `Ideal.pi_tensorProductMk_quotient_surjective` and `Ideal.ker_tensorProductMk_quotient`).
This file packages the two facts into a linear equivalence
`M ⧸ (⋂ᵢ Iᵢ) • M ≃ₗ[R] Πᵢ (R ⧸ Iᵢ) ⊗[R] M`.

## Main declarations

* `Ideal.quotientSMulTopEquivPiTensorProduct`: the Chinese remainder equivalence for modules.
* `Ideal.quotientSMulTopEquivPiTensorProduct_mk`: it sends the class of `m` to `(1 ⊗ₜ m)ᵢ`.
-/

public section

open Function TensorProduct

namespace Ideal

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
  (M : Type*) [AddCommGroup M] [Module R M]
  (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))

/-- **Chinese remainder theorem for modules.** If finitely many ideals `Iᵢ` of `R` are pairwise
coprime, then for any `R`-module `M` the natural map `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` induces a linear
equivalence `M ⧸ (⋂ᵢ Iᵢ) • M ≃ₗ[R] Πᵢ (R ⧸ Iᵢ) ⊗[R] M`. -/
noncomputable def quotientSMulTopEquivPiTensorProduct :
    (M ⧸ (⨅ i, I i) • (⊤ : Submodule R M)) ≃ₗ[R] Π i, (R ⧸ I i) ⊗[R] M :=
  (Submodule.quotEquivOfEq _ _ (ker_tensorProductMk_quotient M I hI).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (pi_tensorProductMk_quotient_surjective M I hI))

/-- The Chinese remainder equivalence sends the class of `m` to the family `(1 ⊗ₜ m)ᵢ`. -/
@[simp]
theorem quotientSMulTopEquivPiTensorProduct_mk (m : M) :
    quotientSMulTopEquivPiTensorProduct M I hI (Submodule.Quotient.mk m) =
      fun i ↦ (1 : R ⧸ I i) ⊗ₜ[R] m := by
  rw [quotientSMulTopEquivPiTensorProduct, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end Ideal
