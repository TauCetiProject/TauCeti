/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change for algebraic independence

Under the canonical `S`-algebra isomorphism `S ⊗[R] MvPolynomial ι R ≃ₐ[S] MvPolynomial ι S`
(`MvPolynomial.algebraTensorAlgEquiv`), evaluating `MvPolynomial ι S` at the base-changed family
`fun i ↦ (1 : S) ⊗ₜ[R] x i` in `S ⊗[R] A` corresponds to `Algebra.TensorProduct.map (AlgHom.id R S)
(MvPolynomial.aeval x)` (`MvPolynomial.aeval_one_tmul_comp_algebraTensorAlgEquiv`).

Consequently:
* finiteness of `MvPolynomial.aeval x` is preserved by base change along any `R`-algebra `S`
  (`MvPolynomial.finite_aeval_one_tmul`);
* algebraic independence of `x` is preserved by flat base change (`AlgebraicIndependent.baseChange`)
  and reflected—hence characterized—by faithfully flat base change
  (`TauCeti.algebraicIndependent_one_tmul_iff`);
* linear combinations `∑ j, C i j • x j` commute with `x j ↦ (1 : S) ⊗ₜ[R] x j` after mapping the
  matrix entries along `algebraMap R S` (`Matrix.sum_map_algebraMap_smul_one_tmul`).

## Main results

* `MvPolynomial.aeval_one_tmul_comp_algebraTensorAlgEquiv`: compatibility of `MvPolynomial.aeval` on
  `(1 : S) ⊗ₜ[R] x i` with `MvPolynomial.algebraTensorAlgEquiv`.
* `MvPolynomial.finite_aeval_one_tmul`: base change preserves finiteness of `MvPolynomial.aeval`.
* `AlgebraicIndependent.baseChange`: flat base change preserves `AlgebraicIndependent`.
* `TauCeti.algebraicIndependent_one_tmul_iff`: faithfully flat base change preserves and reflects
  `AlgebraicIndependent`.
-/

public section

open scoped TensorProduct
open Function MvPolynomial

section CommSemiring

variable {ι m n R S A : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A]
  [Algebra R S] [Algebra R A]

/-- Under `S ⊗[R] MvPolynomial ι R ≃ₐ[S] MvPolynomial ι S`, evaluation at `(1 : S) ⊗ₜ[R] x i` in
`S ⊗[R] A` is `id_S ⊗ aeval x`. -/
theorem MvPolynomial.aeval_one_tmul_comp_algebraTensorAlgEquiv (x : ι → A) :
    ((aeval fun i ↦ (1 : S) ⊗ₜ[R] x i).restrictScalars R).comp
        ((algebraTensorAlgEquiv R S).toAlgHom.restrictScalars R) =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval x) := by
  refine Algebra.TensorProduct.ext (AlgHom.ext fun s ↦ ?_) (MvPolynomial.algHom_ext fun i ↦ ?_)
  · simp [algebraTensorAlgEquiv_tmul, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  · simp [algebraTensorAlgEquiv_tmul]

/-- Evaluating `algebraTensorAlgEquiv R S z` at `(1 : S) ⊗ₜ[R] x i` agrees with applying
`Algebra.TensorProduct.map (AlgHom.id R S) (aeval x)` to `z`. -/
@[simp]
theorem MvPolynomial.aeval_one_tmul_algebraTensorAlgEquiv (x : ι → A)
    (z : S ⊗[R] MvPolynomial ι R) :
    aeval (fun i ↦ (1 : S) ⊗ₜ[R] x i) (algebraTensorAlgEquiv R S z) =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval x) z :=
  AlgHom.congr_fun (aeval_one_tmul_comp_algebraTensorAlgEquiv x) z

/-- Scalar linear combinations of `(1 : S) ⊗ₜ[R] x j` with coefficients mapped from `R` to `S`
equal `(1 : S) ⊗ₜ[R] ∑ j, C i j • x j`. -/
theorem Matrix.sum_map_algebraMap_smul_one_tmul [Fintype n] (C : Matrix m n R) (x : n → A)
    (i : m) :
    ∑ j, C.map (algebraMap R S) i j • ((1 : S) ⊗ₜ[R] x j) =
      (1 : S) ⊗ₜ[R] ∑ j, C i j • x j := by
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.map_apply, TensorProduct.smul_tmul', algebraMap_smul, TensorProduct.smul_tmul]

end CommSemiring

section CommRing

variable {ι R S A : Type*} [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

/-- Extending scalars to any commutative `R`-algebra `S` preserves finiteness of polynomial
evaluation `MvPolynomial.aeval x`. -/
theorem MvPolynomial.finite_aeval_one_tmul (S : Type*) [CommRing S] [Algebra R S] {x : ι → A}
    (hfin : (aeval x : MvPolynomial ι R →ₐ[R] A).Finite) :
    (aeval fun i ↦ (1 : S) ⊗ₜ[R] x i : MvPolynomial ι S →ₐ[S] S ⊗[R] A).Finite := by
  have heq :
      (aeval fun i ↦ (1 : S) ⊗ₜ[R] x i).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id R S) (aeval x)).toRingHom.comp
          (algebraTensorAlgEquiv R S).symm.toRingHom :=
    RingHom.ext fun p ↦
      (congrArg (aeval fun i ↦ (1 : S) ⊗ₜ[R] x i)
        ((algebraTensorAlgEquiv R S).apply_symm_apply p)).symm.trans
        (aeval_one_tmul_algebraTensorAlgEquiv x ((algebraTensorAlgEquiv R S).symm p))
  rw [AlgHom.Finite, heq]
  exact (RingHom.Finite.tensorProductMap (AlgHom.Finite.id R S) hfin).comp
    (RingHom.Finite.of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective)

private theorem aeval_one_tmul_injective_iff_lTensor_injective (x : ι → A) :
    Injective (aeval fun i ↦ (1 : S) ⊗ₜ[R] x i : MvPolynomial ι S →ₐ[S] S ⊗[R] A) ↔
      Injective (LinearMap.lTensor S (aeval x : MvPolynomial ι R →ₐ[R] A).toLinearMap) := by
  have hlin :
      ((aeval fun i ↦ (1 : S) ⊗ₜ[R] x i).restrictScalars R).toLinearMap ∘ₗ
          ((algebraTensorAlgEquiv R S).restrictScalars R).toLinearMap =
        LinearMap.lTensor S (aeval x).toLinearMap := by
    refine TensorProduct.ext' fun s p ↦ ?_
    simpa using aeval_one_tmul_algebraTensorAlgEquiv (S := S) x (s ⊗ₜ[R] p)
  rw [← hlin, LinearMap.coe_comp]
  exact (Function.Injective.of_comp_iff' _ (algebraTensorAlgEquiv R S).bijective).symm

/-- **Flat base change preserves algebraic independence.** If `x : ι → A` is algebraically
independent over `R` and `S` is a flat `R`-algebra, then `fun i ↦ (1 : S) ⊗ₜ[R] x i` is
algebraically independent over `S` in `S ⊗[R] A`. -/
theorem AlgebraicIndependent.baseChange (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
    {x : ι → A} (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent S fun i ↦ (1 : S) ⊗ₜ[R] x i := by
  rw [algebraicIndependent_iff_injective_aeval, aeval_one_tmul_injective_iff_lTensor_injective]
  exact Module.Flat.lTensor_preserves_injective_linearMap (aeval x).toLinearMap hx

/-- **Faithfully flat base change characterizes algebraic independence.** Over a faithfully flat
`R`-algebra `S`, `fun i ↦ (1 : S) ⊗ₜ[R] x i` is algebraically independent over `S` in `S ⊗[R] A` if
and only if `x` is algebraically independent over `R`. -/
@[simp]
theorem TauCeti.algebraicIndependent_one_tmul_iff [Module.FaithfullyFlat R S] {x : ι → A} :
    (AlgebraicIndependent S fun i ↦ (1 : S) ⊗ₜ[R] x i) ↔ AlgebraicIndependent R x := by
  rw [algebraicIndependent_iff_injective_aeval, aeval_one_tmul_injective_iff_lTensor_injective,
    Module.FaithfullyFlat.lTensor_injective_iff_injective R S]
  exact Iff.rfl

end CommRing
