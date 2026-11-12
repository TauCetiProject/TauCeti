/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bijectivity of a lift of tensor products from bases

Let `R → S → T` be a tower of commutative semirings, `U` a commutative `R`-algebra and
`u : U →ₐ[R] T` an `R`-algebra map. The `S`-algebra map `S ⊗[R] U → T`, `x ⊗ y ↦ x * u y`, is
bijective as soon as `u` carries a basis of `U` over `R` to a basis of `T` over `S`: it carries the
basis `1 ⊗ bᵢ` of `S ⊗[R] U` over `S` (Mathlib's `Algebra.TensorProduct.basis`) to that basis of
`T`.

## Main results

* `Algebra.TensorProduct.lift_bijective_of_basis`: the lift `S ⊗[R] U → T` of `S → T` and `u` is
  bijective if `u` carries a basis of `U` over `R` to a basis of `T` over `S`.
-/

public section

namespace Algebra.TensorProduct

/-- **A lift of tensor products carrying a basis to a basis is bijective.** If `u : U →ₐ[R] T`
carries a basis `bᵢ` of `U` over `R` to a basis of `T` over `S`, then the `S`-algebra map
`S ⊗[R] U → T`, `x ⊗ y ↦ x * u y`, is bijective. -/
theorem lift_bijective_of_basis {R S U T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring U] [CommSemiring T] [Algebra R S] [Algebra R U] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (u : U →ₐ[R] T) {ι : Type*}
    (bU : Module.Basis ι R U) (bT : Module.Basis ι S T) (hb : ∀ i, bT i = u (bU i)) :
    Function.Bijective (lift (Algebra.ofId S T) u fun _ _ ↦ .all _ _) := by
  let b := basis S bU
  have hψ : (lift (Algebra.ofId S T) u fun _ _ ↦ .all _ _).toLinearMap =
      (b.equiv bT (Equiv.refl ι)).toLinearMap :=
    b.ext fun i ↦ by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [b, hb]
  rw [← AlgHom.coe_toLinearMap, hψ]
  exact (b.equiv bT (Equiv.refl ι)).bijective

end Algebra.TensorProduct
