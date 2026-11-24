/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.TensorProduct.Maps
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Flat scalar extension of algebraically independent families

When `S` is a flat `R`-algebra, algebraic independence of a family `y : ι → A` over `R` implies
algebraic independence of `i ↦ (1 : S) ⊗ₜ[R] y i` in `S ⊗[R] A` over `S`
(`AlgebraicIndependent.one_tmul`).

If a set `s ⊆ A` is algebraically independent over `R`, then the subalgebra `Algebra.adjoin R s`
is the polynomial ring over `R` in the variables `s`, so extending its scalars to an `R`-algebra `B`
gives the polynomial ring over `B` in the same variables
(`AlgebraicIndependent.adjoinTensorAlgEquiv`).

## Main results

* `AlgebraicIndependent.one_tmul`: flat scalar extension preserves algebraic independence.
* `AlgebraicIndependent.adjoinTensorAlgEquiv`: for an algebraically independent set `s`,
  `Algebra.adjoin R s ⊗[R] B ≃ₐ[R] MvPolynomial s B`.
-/

public section

open scoped TensorProduct

namespace AlgebraicIndependent

/-- Algebraic independence of `y : ι → A` over `R` is preserved upon extending scalars to any flat
`R`-algebra `S`. -/
theorem one_tmul {ι R A : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [CommRing A] [Algebra R A] {y : ι → A} (hy : AlgebraicIndependent R y) :
    AlgebraicIndependent S fun i ↦ (1 : S) ⊗ₜ[R] y i := by
  rw [algebraicIndependent_iff_injective_aeval] at hy ⊢
  have hinj :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id R S) (MvPolynomial.aeval (R := R) y)) := by
    rw [← funext ((MvPolynomial.aeval (R := R) y).lTensor_toLinearMap_apply S)]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
      (MvPolynomial.aeval (R := R) y).toLinearMap (by rwa [AlgHom.coe_toLinearMap])
  intro p q hpq
  rw [MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm,
    MvPolynomial.aeval_one_tmul_eq_map_algebraTensorAlgEquiv_symm] at hpq
  exact (MvPolynomial.algebraTensorAlgEquiv R S).symm.injective (hinj hpq)

/-- If the set `s` is algebraically independent over `R`, then tensoring the subalgebra
`Algebra.adjoin R s` with an `R`-algebra `B` gives the polynomial ring `MvPolynomial s B`. -/
noncomputable def adjoinTensorAlgEquiv {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {s : Set A} (hs : AlgebraicIndependent R ((↑) : s → A)) (B : Type*) [CommRing B]
    [Algebra R B] : Algebra.adjoin R s ⊗[R] B ≃ₐ[R] MvPolynomial s B :=
  (Algebra.TensorProduct.congr
      (hs.aevalEquiv.trans (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]))).symm
      (AlgEquiv.refl : B ≃ₐ[R] B)).trans
    ((Algebra.TensorProduct.comm R (MvPolynomial s R) B).trans
      ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R))

end AlgebraicIndependent
