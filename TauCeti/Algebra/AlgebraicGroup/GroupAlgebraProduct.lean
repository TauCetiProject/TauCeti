/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.Bialgebra.MonoidAlgebraProduct
import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# The diagonalizable group of a product

This file records the functor-of-points consequence of
`TauCeti.MonoidAlgebra.prodTensorBialgEquiv`: the diagonalizable group
`D(G × H) = Spec R[G × H]`, for commutative groups `G` and `H`, is the direct product
`D(G) × D(H)` of the diagonalizable groups of the factors.

On points this composes with `TauCeti.AffineGroup.Product.pointsMulEquiv`, the tensor-product
points calculation, through the equiv-version `AlgHom.mapDomainMulEquiv` of the contravariant
functoriality `AlgHom.mapDomain`. When `G` and `H` are commutative groups the group algebras
are Hopf algebras and these convolution monoids are the convolution groups of points
(`TauCeti.AlgHom.instGroup`), so the points equivalence is automatically an isomorphism of
groups: `D(G × H)(A) ≅ D(G)(A) × D(H)(A)`.

This advances the reductive-groups roadmap (`ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 4 "Diagonalizable groups" and the "Worked examples / products" theme, together with the
Layer 0 functor-of-points dictionary): a split torus `𝔾ₘⁿ` is the `n`-fold product of `𝔾ₘ`,
and this identifies its coordinate Hopf algebra `R[ℤⁿ]` with `R[ℤ]^{⊗ n}` and its points with
`(Aˣ)ⁿ`.

## Main definitions

* `TauCeti.DiagonalizableGroup.prodPointsMulEquiv`: on points,
  `D(G × H)(A) ≃* D(G)(A) × D(H)(A)`.

## References

The tensor-product points calculation `TauCeti.AffineGroup.Product.pointsMulEquiv`, the generic
monoid-algebra bialgebra product `TauCeti.MonoidAlgebra.prodTensorBialgEquiv`, and the
contravariant functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's existing
functor-of-points infrastructure, built on Mathlib's tensor-product and monoid-algebra
bialgebra structures and the Mathlib convolution monoid of Yaël Dillies, Michał Mrugała and
Yunzhou Xie.
-/

open TensorProduct WithConv MonoidAlgebra

namespace TauCeti

universe u v w w'

namespace DiagonalizableGroup

variable {R : Type u} [CommSemiring R]
variable {G : Type v} {H : Type w} [CommGroup G] [CommGroup H]
variable {A : Type w'} [CommSemiring A] [Algebra R A]

/-- **The diagonalizable group of a product is the product of diagonalizable groups, on points.**
For commutative groups `G` and `H` and every commutative `R`-algebra `A`, the convolution group
of `A`-points of `D(G × H)` is the product of the convolution groups of `A`-points of `D(G)` and
`D(H)`. -/
noncomputable def prodPointsMulEquiv :
    WithConv (MonoidAlgebra R (G × H) →ₐ[R] A) ≃*
      WithConv (MonoidAlgebra R G →ₐ[R] A) × WithConv (MonoidAlgebra R H →ₐ[R] A) :=
  (AlgHom.mapDomainMulEquiv (A := A) (MonoidAlgebra.prodTensorBialgEquiv R)).symm.trans
    AffineGroup.Product.pointsMulEquiv

/-- The first component of `prodPointsMulEquiv` restricts an `A`-point of `D(G × H)` to the
factor `D(G)`: on the generator `single g 1` it evaluates the original point at `single (g, 1) 1`,
the image of `g` under `G → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_fst_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (g : G) :
    (prodPointsMulEquiv f).1.ofConv (single g (1 : R)) =
      f.ofConv (single (g, (1 : H)) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeLeft_apply, BialgEquiv.coe_toBialgHom]
  rw [show (1 : MonoidAlgebra R H) = single 1 1 from MonoidAlgebra.one_def,
    MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The second component of `prodPointsMulEquiv` restricts an `A`-point of `D(G × H)` to the
factor `D(H)`: on the generator `single h 1` it evaluates the original point at `single (1, h) 1`,
the image of `h` under `H → G × H`. -/
@[simp]
theorem prodPointsMulEquiv_snd_ofConv_single
    (f : WithConv (MonoidAlgebra R (G × H) →ₐ[R] A)) (h : H) :
    (prodPointsMulEquiv f).2.ofConv (single h (1 : R)) =
      f.ofConv (single ((1 : G), h) 1) := by
  rw [prodPointsMulEquiv, MulEquiv.trans_apply, AffineGroup.Product.pointsMulEquiv_apply,
    AlgHom.mapDomainMulEquiv_symm_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
    BialgHom.coe_toAlgHom, Bialgebra.TensorProduct.includeRight_apply, BialgEquiv.coe_toBialgHom]
  rw [show (1 : MonoidAlgebra R G) = single 1 1 from MonoidAlgebra.one_def,
    MonoidAlgebra.prodTensorBialgEquiv_symm_tmul_single]

/-- The inverse of `prodPointsMulEquiv` assembles an `A`-point of `D(G × H)` from a pair of
points of `D(G)` and `D(H)`: on the generator `single (g, h) 1` it multiplies the value of the
first point at `single g 1` and the value of the second at `single h 1`. -/
@[simp]
theorem prodPointsMulEquiv_symm_ofConv_single
    (f₁ : WithConv (MonoidAlgebra R G →ₐ[R] A)) (f₂ : WithConv (MonoidAlgebra R H →ₐ[R] A))
    (g : G) (h : H) :
    (prodPointsMulEquiv.symm (f₁, f₂)).ofConv (single (g, h) (1 : R)) =
      f₁.ofConv (single g 1) * f₂.ofConv (single h 1) := by
  rw [prodPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    AlgHom.mapDomainMulEquiv_apply]
  simp only [AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply, BialgHom.coe_toAlgHom,
    BialgEquiv.coe_toBialgHom, MonoidAlgebra.prodTensorBialgEquiv_single,
    AffineGroup.Product.pointsMulEquiv_symm_apply, Algebra.TensorProduct.productMap_apply_tmul]

end DiagonalizableGroup

end TauCeti
