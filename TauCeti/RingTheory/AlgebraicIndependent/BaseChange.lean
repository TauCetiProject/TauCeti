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
* `AlgebraicIndependent.adjoinTensorAlgEquiv_tmul`,
  `AlgebraicIndependent.adjoinTensorAlgEquiv_symm_X`,
  `AlgebraicIndependent.adjoinTensorAlgEquiv_symm_C`: its values on pure tensors and the values of
  its inverse on variables and constants.
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

section adjoinTensorAlgEquiv

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {s : Set A}
  (hs : AlgebraicIndependent R ((↑) : s → A)) {B : Type*} [CommRing B] [Algebra R B]

/-- `adjoinTensorAlgEquiv` sends `x ⊗ₜ b` to `b` times the polynomial over `R` representing `x`,
with coefficients mapped into `B`. -/
theorem adjoinTensorAlgEquiv_tmul (x : Algebra.adjoin R s) (b : B) :
    hs.adjoinTensorAlgEquiv B (x ⊗ₜ b) =
      b • MvPolynomial.map (algebraMap R B)
        (hs.repr (Subalgebra.equivOfEq _ _ (by rw [Subtype.range_coe]) x)) := by
  simp [adjoinTensorAlgEquiv, repr]

/-- The inverse of `adjoinTensorAlgEquiv` sends the variable `X i` to `i ⊗ₜ 1`. -/
@[simp]
theorem adjoinTensorAlgEquiv_symm_X (i : s) :
    (hs.adjoinTensorAlgEquiv B).symm (MvPolynomial.X i) =
      ⟨i, Algebra.subset_adjoin i.property⟩ ⊗ₜ 1 := by
  apply (hs.adjoinTensorAlgEquiv B).injective
  simp only [AlgEquiv.apply_symm_apply, adjoinTensorAlgEquiv_tmul, one_smul, repr,
    AlgEquiv.coe_toAlgHom]
  rw [(AlgEquiv.symm_apply_eq (y := MvPolynomial.X i) _).2 (Subtype.ext (by simp)),
    MvPolynomial.map_X]

/-- The inverse of `adjoinTensorAlgEquiv` sends the constant `C b` to `1 ⊗ₜ b`. -/
@[simp]
theorem adjoinTensorAlgEquiv_symm_C (b : B) :
    (hs.adjoinTensorAlgEquiv B).symm (MvPolynomial.C b) = 1 ⊗ₜ b := by
  apply (hs.adjoinTensorAlgEquiv B).injective
  simp [adjoinTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul, -Subalgebra.equivOfEq_apply]

end adjoinTensorAlgEquiv

end AlgebraicIndependent
