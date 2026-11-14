/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.TensorProduct.MvPolynomial

/-!
# Flat scalar extension of algebraically independent families

When `S` is a flat `R`-algebra, algebraic independence of a family `y : ι → A` over `R` implies
algebraic independence of `i ↦ (1 : S) ⊗ₜ[R] y i` in `S ⊗[R] A` over `S`
(`AlgebraicIndependent.one_tmul`).

## Main results

* `AlgebraicIndependent.one_tmul`: flat scalar extension preserves algebraic independence.
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
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R S) (MvPolynomial.aeval y)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S)
      (MvPolynomial.aeval y).toLinearMap hy
  intro p q hpq
  rw [MvPolynomial.aeval_one_tmul_apply, MvPolynomial.aeval_one_tmul_apply] at hpq
  exact (MvPolynomial.algebraTensorAlgEquiv R S).symm.injective (hinj hpq)

end AlgebraicIndependent
