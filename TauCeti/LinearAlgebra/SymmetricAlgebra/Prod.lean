/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# The symmetric algebra of a product

The symmetric algebra functor sends products of modules to tensor products of algebras: for
`R`-modules `M` and `N` there is a canonical `R`-algebra equivalence

`Sym (M × N) ≃ Sym M ⊗[R] Sym N`,

sending a generator `(m, n)` to `m ⊗ 1 + 1 ⊗ n`. Its inverse multiplies the images of the two
factors under the maps induced by the inclusions `M → M × N` and `N → M × N`. Geometrically,
polynomial functions on a product of two spaces are sums of products of polynomial functions on
the factors. The equivalence is natural in both modules.

## Main definitions

* `SymmetricAlgebra.prodEquiv`: the algebra equivalence `Sym (M × N) ≃ Sym M ⊗[R] Sym N`.

## Main results

* `SymmetricAlgebra.prodEquiv_ι`: the equivalence on a generator.
* `SymmetricAlgebra.prodEquiv_symm_tmul`: its inverse on a pure tensor.
* `SymmetricAlgebra.prodEquiv_map_prodMap`: naturality with respect to a product of linear maps.

## References

* N. Bourbaki, *Algebra I*, Chapter III, § 6.
-/

public section

open TensorProduct

namespace SymmetricAlgebra

variable (R M N : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The symmetric algebra of a product is the tensor product of the symmetric algebras: the
generator `(m, n)` corresponds to `m ⊗ 1 + 1 ⊗ n`, and a pure tensor `p ⊗ q` to the product of
the images of `p` and `q` under the maps induced by the two inclusions. -/
noncomputable def prodEquiv :
    SymmetricAlgebra R (M × N) ≃ₐ[R] SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N :=
  .ofAlgHom
    (lift <| Algebra.TensorProduct.includeLeft.toLinearMap ∘ₗ ι R M ∘ₗ LinearMap.fst R M N +
      Algebra.TensorProduct.includeRight.toLinearMap ∘ₗ ι R N ∘ₗ LinearMap.snd R M N)
    (Algebra.TensorProduct.productMap (map R (LinearMap.inl R M N))
      (map R (LinearMap.inr R M N)))
    (by ext <;> simp)
    (by ext <;> simp)

variable {R M N}

/-- The equivalence `SymmetricAlgebra.prodEquiv` sends the generator `(m, n)` to
`m ⊗ 1 + 1 ⊗ n`. -/
@[simp]
theorem prodEquiv_ι (x : M × N) :
    prodEquiv R M N (ι R (M × N) x) = ι R M x.1 ⊗ₜ 1 + 1 ⊗ₜ ι R N x.2 := by
  simp [prodEquiv]

/-- The inverse of `SymmetricAlgebra.prodEquiv` multiplies the images of the two factors under
the maps induced by the inclusions of `M` and `N` into `M × N`. -/
@[simp]
theorem prodEquiv_symm_tmul (p : SymmetricAlgebra R M) (q : SymmetricAlgebra R N) :
    (prodEquiv R M N).symm (p ⊗ₜ q) =
      map R (LinearMap.inl R M N) p * map R (LinearMap.inr R M N) q := by
  simp [prodEquiv]

/-- The equivalence `SymmetricAlgebra.prodEquiv` is natural: the map induced by a product of
linear maps corresponds to the tensor product of the induced maps. -/
theorem prodEquiv_map_prodMap {M' N' : Type*} [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (p : SymmetricAlgebra R (M × N)) :
    prodEquiv R M' N' (map R (f.prodMap g) p) =
      Algebra.TensorProduct.map (map R f) (map R g) (prodEquiv R M N p) := by
  have : ((prodEquiv R M' N').toAlgHom.comp (map R (f.prodMap g))) =
      (Algebra.TensorProduct.map (map R f) (map R g)).comp (prodEquiv R M N).toAlgHom := by
    ext <;> simp
  exact congr($this p)

end SymmetricAlgebra
