/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Multiplicative
import TauCeti.LinearAlgebra.TensorProduct.ScalarExtension
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Scalar extension of polynomial laws

A law from `M` to `N` over `R` extends to a law from `B ⊗[R] M` to
`B ⊗[R] N` over a commutative `R`-algebra `B`. Its component at a
commutative `B`-algebra `S` is the original component at `S`, transported
along the tensor cancellation equivalences. This construction preserves
homogeneity and multiplicativity.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Remark 1.4](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u v

open TensorProduct TensorProduct.AlgebraTensorModule

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] (B : Type v) [CommSemiring B] [Algebra R B]
  {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extend both modules of a polynomial law along a commutative algebra. -/
def baseChange (f : M →ₚₗ[R] N) : B ⊗[R] M →ₚₗ[B] B ⊗[R] N where
  toFun' S _ _ x :=
    letI : Algebra R S := Algebra.compHom S (algebraMap R B)
    letI : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    (cancelBaseChange R B B S N).symm (f.toFun S (cancelBaseChange R B B S M x))
  isCompat' {S} _ _ {T} _ _ φ := by
    let : Algebra R S := Algebra.compHom S (algebraMap R B)
    let : Algebra R T := Algebra.compHom T (algebraMap R B)
    let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
    funext x
    apply (cancelBaseChange R B B T N).injective
    rw [Function.comp_apply, Function.comp_apply, cancelBaseChange_rTensor,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, cancelBaseChange_rTensor]
    exact f.isCompat_apply (φ.restrictScalars R) _

/-- At an algebra in the universe of `B`, scalar extension transports the original law
along tensor cancellation. -/
theorem baseChange_toFun' (f : M →ₚₗ[R] N) (S : Type v) [CommSemiring S] [Algebra B S]
    [alg : Algebra R S] [IsScalarTower R B S] (x : S ⊗[B] (B ⊗[R] M)) :
    (f.baseChange B).toFun' S x =
      (cancelBaseChange R B B S N).symm (f.toFun S (cancelBaseChange R B B S M x)) := by
  have h : alg = Algebra.compHom S (algebraMap R B) :=
    Algebra.algebra_ext _ _ fun r ↦ IsScalarTower.algebraMap_apply R B S r
  subst alg
  rfl

/-- The scalar-extension formula holds at commutative algebras in any universe. -/
theorem baseChange_toFun (f : M →ₚₗ[R] N) (S : Type*) [CommSemiring S] [Algebra B S]
    [Algebra R S] [IsScalarTower R B S] (x : S ⊗[B] (B ⊗[R] M)) :
    (f.baseChange B).toFun S x =
      (cancelBaseChange R B B S N).symm (f.toFun S (cancelBaseChange R B B S M x)) := by
  suffices h : ∀ {T : Type v} [CommSemiring T] [Algebra B T] [Algebra R T] [IsScalarTower R B T]
      (φ : T →ₐ[B] S) (p : T ⊗[B] (B ⊗[R] M)),
      (f.baseChange B).toFun S (φ.toLinearMap.rTensor _ p) =
        (cancelBaseChange R B B S N).symm
          (f.toFun S (cancelBaseChange R B B S M (φ.toLinearMap.rTensor _ p))) by
    obtain ⟨k, φ, p, rfl⟩ := exists_lift x
    let : Algebra R (MvPolynomial (Fin k) B) := Algebra.compHom _ (algebraMap R B)
    let : IsScalarTower R B (MvPolynomial (Fin k) B) := IsScalarTower.of_algebraMap_eq' rfl
    exact h φ p
  intro T _ _ _ _ φ p
  apply (cancelBaseChange R B B S N).injective
  rw [← isCompat_apply, ← toFun'_eq_toFun, baseChange_toFun' B f, cancelBaseChange_rTensor,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, cancelBaseChange_rTensor]
  exact f.isCompat_apply (φ.restrictScalars R) _

/-- The extended law at a scalar-extended vector, evaluated on the ground algebra. -/
theorem baseChange_ground (f : M →ₚₗ[R] N) (x : B ⊗[R] M) :
    (f.baseChange B).ground x = f.toFun B x := by
  rw [ground_apply, baseChange_toFun', cancelBaseChange_self_eq_lid,
    cancelBaseChange_self_eq_lid, lid_tmul]
  simp

/-- Scalar extension preserves homogeneity of the same degree. -/
theorem IsHomogeneousOfDegree.baseChange {d : ℕ} {f : M →ₚₗ[R] N}
    (hf : f.IsHomogeneousOfDegree d) : (f.baseChange B).IsHomogeneousOfDegree d := by
  rw [isHomogeneousOfDegree_iff]
  intro S _ _ s x
  let : Algebra R S := Algebra.compHom S (algebraMap R B)
  let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
  have h (y : S ⊗[B] (B ⊗[R] M)) :
      (f.baseChange B).toFun' S y =
        (cancelBaseChange R B S S N).symm (f.toFun S (cancelBaseChange R B S S M y)) := by
    -- Cancellation has the same underlying map over `B` and over `S`.
    exact baseChange_toFun' B f S y
  rw [h, h, map_smul, hf.toFun_smul, map_smul]

section Multiplicative

/-- Scalar extension preserves multiplication and the unit after every change of scalars. -/
theorem IsMultiplicative.baseChange {M N : Type*} [Semiring M] [Algebra R M]
    [Semiring N] [Algebra R N] {f : M →ₚₗ[R] N}
    (hf : f.IsMultiplicative) : (f.baseChange B).IsMultiplicative := by
  have h (S : Type v) [CommSemiring S] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
      (y : S ⊗[B] (B ⊗[R] M)) :
      (f.baseChange B).toFun' S y =
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R B N S).symm
          (f.toFun S (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R B M S y)) := by
    let eN := TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R B N S
    let eM := TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv R B M S
    have heN : eN.symm.toLinearEquiv = (cancelBaseChange R B S S N).symm := by
      rw [AlgEquiv.toLinearEquiv_symm,
        TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_toLinearEquiv]
    have heM : eM.toLinearEquiv = cancelBaseChange R B S S M :=
      TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_toLinearEquiv R B M S
    -- The algebra equivalences act through their underlying linear equivalences.
    change _ = eN.symm.toLinearEquiv (f.toFun S (eM.toLinearEquiv y))
    rw [heN, heM]
    exact baseChange_toFun' B f S y
  refine ⟨?_, ?_⟩
  · intro S _ _
    let : Algebra R S := Algebra.compHom S (algebraMap R B)
    let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    simp only [h, map_one, hf.toFun_one]
  · intro S _ _ x y
    let : Algebra R S := Algebra.compHom S (algebraMap R B)
    let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    simp only [h, map_mul, hf.toFun_mul]

end Multiplicative

end PolynomialLaw
