/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.RingTheory.TensorProduct.Quotient
public import TauCeti.Algebra.MonoidAlgebra.Ideal

/-!
# Tensor products with monoid algebras

This file records the standard linear identification of a tensor product with a monoid algebra
as a space of finitely supported functions.

It also shows that the formation of the quotient of an additive monoid algebra by a monomial ideal
commutes with base change. For a commutative ring `R`, a commutative additive monoid `M`, every set
`D ⊆ M` (translation-stable or not) and every `R`-algebra `S`, the scalar extension
`S ⊗[R] (R[M] ⧸ (D))` is the quotient `S[M] ⧸ (D)` by the ideal spanned by the same monomials over
`S`.

## Main definitions

* `TauCeti.MonoidAlgebra.tensorEquivFinsupp`: the equivalence
  `k[G] ⊗ W ≃ₗ G →₀ W`.
* `AddMonoidAlgebra.quotientSpanOf'ImageTensorEquiv`: the base change of the quotient by a monomial
  ideal is the quotient by the same monomial ideal over the new coefficients.

## Main results

* `TauCeti.MonoidAlgebra.tensorEquivFinsupp_single_tmul` and
  `TauCeti.MonoidAlgebra.tensorEquivFinsupp_symm_single`: the equivalence and its inverse on
  generators.
* `MonoidAlgebra.scalarTensorEquiv_one_tmul` and
  `MonoidAlgebra.scalarTensorEquiv_comp_includeRight`, with their additive versions: Mathlib's
  base change `S ⊗[R] R[M] ≃ₐ[S] S[M]`, restricted to `1 ⊗ R[M]`, is the coefficient change
  `R → S`.
* `AddMonoidAlgebra.quotientSpanOf'ImageTensorEquiv_tmul` and
  `AddMonoidAlgebra.quotientSpanOf'ImageTensorEquiv_symm_mk_single`: the base-change equivalence
  of monomial quotients on pure tensors, and its inverse on classes of monomials.
-/

public section

open scoped TensorProduct

noncomputable section

namespace TauCeti.MonoidAlgebra

variable {k G W : Type*} [CommSemiring k] [AddCommMonoid W] [Module k W]

variable (k G W) in
/-- The standard identification `k[G] ⊗ W ≃ₗ G →₀ W`, sending `single g r ⊗ₜ w` to
`Finsupp.single g (r • w)`. -/
def tensorEquivFinsupp : _root_.MonoidAlgebra k G ⊗[k] W ≃ₗ[k] G →₀ W := by
  classical
  exact TensorProduct.congr (_root_.MonoidAlgebra.coeffLinearEquiv k) (.refl k W) ≪≫ₗ
    TensorProduct.finsuppScalarLeft k W G

/-- The tensor/Finsupp equivalence sends a pure tensor supported at `g` to a Finsupp supported
at `g`. -/
@[simp]
theorem tensorEquivFinsupp_single_tmul (g : G) (r : k) (w : W) :
    tensorEquivFinsupp k G W (_root_.MonoidAlgebra.single g r ⊗ₜ[k] w) =
      Finsupp.single g (r • w) := by
  simp [tensorEquivFinsupp, TensorProduct.finsuppScalarLeft_apply_tmul]

/-- The inverse of the tensor/Finsupp equivalence sends a Finsupp supported at `g` to a pure
tensor supported at `g`. -/
@[simp]
theorem tensorEquivFinsupp_symm_single (g : G) (w : W) :
    (tensorEquivFinsupp k G W).symm (Finsupp.single g w) =
      _root_.MonoidAlgebra.single g (1 : k) ⊗ₜ[k] w := by
  simp [LinearEquiv.symm_apply_eq]

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

open TensorProduct

variable {R M : Type*} [CommSemiring R] [CommMonoid M] (S : Type*) [CommSemiring S] [Algebra R S]

/-- Base change of `R[M]` to `S` sends `1 ⊗ p` to the image of `p` under the coefficient change
`R → S`. -/
@[to_additive (dont_translate := R S) scalarTensorEquiv_one_tmul
/-- Base change of `R[M]` to `S` sends `1 ⊗ p` to the image of `p` under the coefficient change
`R → S`. -/]
theorem scalarTensorEquiv_one_tmul (p : MonoidAlgebra R M) :
    scalarTensorEquiv R S (1 ⊗ₜ p) = mapRingHom M (algebraMap R S) p := by
  ext m
  simp

/-- Including `R[M]` into `S ⊗[R] R[M]` and then identifying the result with `S[M]` is the
coefficient change `R → S`. -/
@[to_additive (dont_translate := R S)
/-- Including `R[M]` into `S ⊗[R] R[M]` and then identifying the result with `S[M]` is the
coefficient change `R → S`. -/]
theorem scalarTensorEquiv_comp_includeRight :
    (scalarTensorEquiv R S (M := M) : S ⊗[R] MonoidAlgebra R M →+* MonoidAlgebra S M).comp
        (Algebra.TensorProduct.includeRight (R := R) (A := S) : MonoidAlgebra R M →ₐ[R] _) =
      mapRingHom M (algebraMap R S) :=
  RingHom.ext (scalarTensorEquiv_one_tmul S)

end MonoidAlgebra

namespace AddMonoidAlgebra

open TensorProduct

variable {R M : Type*} [CommRing R] [AddCommMonoid M] (S : Type*) [CommRing S] [Algebra R S]
  (D : Set M)

/-- The formation of the quotient by a monomial ideal commutes with base change: for every
`R`-algebra `S`, the scalar extension `S ⊗[R] (R[M] ⧸ (D))` is the quotient `S[M] ⧸ (D)` by the
ideal spanned by the same monomials over `S`. -/
def quotientSpanOf'ImageTensorEquiv :
    S ⊗[R] (AddMonoidAlgebra R M ⧸ Ideal.span (of' R M '' D)) ≃ₐ[S]
      AddMonoidAlgebra S M ⧸ Ideal.span (of' S M '' D) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S _ S _).trans <|
    Ideal.quotientEquivAlg _ _ (scalarTensorEquiv R S) <| by
      rw [← Ideal.map_coe Algebra.TensorProduct.includeRight, Ideal.map_map,
        scalarTensorEquiv_comp_includeRight, map_mapRingHom_ideal_span_of'_image]

/-- The base-change equivalence of monomial quotients sends `s ⊗ [p]` to the class of `s` times
the image of `p` under the coefficient change `R → S`. -/
@[simp]
theorem quotientSpanOf'ImageTensorEquiv_tmul (s : S) (p : AddMonoidAlgebra R M) :
    quotientSpanOf'ImageTensorEquiv S D (s ⊗ₜ Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (s • mapRingHom M (algebraMap R S) p) := by
  rw [← scalarTensorEquiv_one_tmul]
  simp [quotientSpanOf'ImageTensorEquiv]

/-- The inverse of the base-change equivalence of monomial quotients sends the class of the
monomial `single m s` over `S` to `s ⊗` the class of the monomial `single m 1` over `R`. -/
@[simp]
theorem quotientSpanOf'ImageTensorEquiv_symm_mk_single (m : M) (s : S) :
    (quotientSpanOf'ImageTensorEquiv (R := R) S D).symm (Ideal.Quotient.mk _ (single m s)) =
      s ⊗ₜ Ideal.Quotient.mk (Ideal.span (of' R M '' D)) (single m 1) := by
  rw [AlgEquiv.symm_apply_eq, quotientSpanOf'ImageTensorEquiv_tmul]
  simp

end AddMonoidAlgebra
