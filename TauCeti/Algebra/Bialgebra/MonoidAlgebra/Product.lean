/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# The monoid algebra of a product is the tensor product of monoid algebras

For two monoids `G` and `H`, the canonical map `single (g, h) 1 ↦ single g 1 ⊗ₜ
single h 1` is an isomorphism of `R`-bialgebras `R[G × H] ≃ₐc[R] R[G] ⊗[R] R[H]`.

The underlying linear equivalence is Mathlib's `MonoidAlgebra.tensorEquiv` (inverted); this file
shows that it is multiplicative and compatible with the counits and comultiplications.

This is generic monoid-algebra API used by the diagonalizable-group product calculation.

## Main definitions

* `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`: the bialgebra isomorphism
  `R[G × H] ≃ₐc[R] R[G] ⊗[R] R[H]`.

## References

The linear equivalence `MonoidAlgebra.tensorEquiv` is from Mathlib's
`Mathlib.RingTheory.TensorProduct.MonoidAlgebra`; the tensor-product bialgebra structure is from
`Mathlib.RingTheory.Bialgebra.TensorProduct`, and the monoid-algebra bialgebra structure from
`Mathlib.RingTheory.Bialgebra.MonoidAlgebra`.
-/

public section

open TensorProduct MonoidAlgebra

namespace TauCeti

universe u v w

namespace MonoidAlgebra

variable (R : Type u) [CommSemiring R]
variable {G : Type v} {H : Type w} [Monoid G] [Monoid H]

/-- **The monoid algebra of a product is the tensor product of monoid algebras**, as a bialgebra
isomorphism. Its underlying linear equivalence is `(MonoidAlgebra.tensorEquiv R).symm`. -/
noncomputable def prodTensorBialgEquiv :
    MonoidAlgebra R (G × H) ≃ₐc[R] MonoidAlgebra R G ⊗[R] MonoidAlgebra R H :=
  .ofAlgEquiv
    (.ofLinearEquiv (tensorEquiv R).symm
      (by simp [one_def, tensorEquiv_symm_single_eq_single_one_tmul,
        Algebra.TensorProduct.one_def])
      ((LinearMap.map_mul_iff _).2 <| by ext; simp [tensorEquiv_symm_single_eq_single_one_tmul]))
    (by ext; simp [tensorEquiv_symm_single_eq_single_one_tmul])
    (by ext; simp [tensorEquiv_symm_single_eq_single_one_tmul])

/-- The forward product bialgebra equivalence sends `single (g, h) r` to
`single g 1 ⊗ₜ single h r`. -/
@[simp]
theorem prodTensorBialgEquiv_single (p : G × H) (r : R) :
    prodTensorBialgEquiv R (single p r) = single p.1 1 ⊗ₜ[R] single p.2 r :=
  tensorEquiv_symm_single_eq_single_one_tmul p r

/-- The inverse product bialgebra equivalence sends `single g r ⊗ₜ single h s` to
`single (g, h) (r * s)`. -/
@[simp]
theorem prodTensorBialgEquiv_symm_single_tmul_single (g : G) (h : H) (r s : R) :
    (prodTensorBialgEquiv R).symm (single g r ⊗ₜ[R] single h s) = single (g, h) (r * s) :=
  tensorEquiv_single_tmul_single g r h s

end MonoidAlgebra

end TauCeti
