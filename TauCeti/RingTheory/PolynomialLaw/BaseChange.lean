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
homogeneity and multiplicativity. Thus a law defined over `R` can be used over `B`
and evaluated on further `B`-algebras. Homogeneous multiplicative laws provide
the input for scalar extension of determinants.

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

private def transportedComponent (f : M →ₚₗ[R] N) (S : Type*) [CommSemiring S]
    [Algebra B S] [Algebra R S] [IsScalarTower R B S] (x : S ⊗[B] (B ⊗[R] M)) :=
  (cancelBaseChange R B B S N).symm (f.toFun S (cancelBaseChange R B B S M x))

private theorem transportedComponent_natural (f : M →ₚₗ[R] N)
    {S T : Type*} [CommSemiring S] [Algebra B S] [Algebra R S] [IsScalarTower R B S]
    [CommSemiring T] [Algebra B T] [Algebra R T] [IsScalarTower R B T]
    (φ : S →ₐ[B] T) (x : S ⊗[B] (B ⊗[R] M)) :
    φ.toLinearMap.rTensor _ (transportedComponent B f S x) =
      transportedComponent B f T (φ.toLinearMap.rTensor _ x) := by
  apply (cancelBaseChange R B B T N).injective
  simp only [transportedComponent, cancelBaseChange_rTensor, LinearEquiv.apply_symm_apply]
  exact f.isCompat_apply (φ.restrictScalars R) _

/-- Extend both modules of a polynomial law along a commutative algebra. -/
def baseChange (f : M →ₚₗ[R] N) : B ⊗[R] M →ₚₗ[B] B ⊗[R] N where
  toFun' S _ _ x :=
    letI : Algebra R S := Algebra.compHom S (algebraMap R B)
    letI : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    transportedComponent B f S x
  isCompat' {S} _ _ {T} _ _ φ := by
    let : Algebra R S := Algebra.compHom S (algebraMap R B)
    let : Algebra R T := Algebra.compHom T (algebraMap R B)
    let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
    let : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
    funext x
    exact transportedComponent_natural B f φ x

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
  rw [← isCompat_apply, ← toFun'_eq_toFun, baseChange_toFun' B f]
  exact transportedComponent_natural B f φ p

/-- Scalar extension preserves the identity law. -/
@[simp]
theorem baseChange_id : (id : M →ₚₗ[R] M).baseChange B = id := by
  ext S _ _ x
  let : Algebra R S := Algebra.compHom S (algebraMap R B)
  let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
  simp only [baseChange_toFun', ← LinearMap.toPolynomialLaw_id,
    LinearMap.toPolynomialLaw_toFun, LinearMap.toPolynomialLaw_toFun', LinearMap.baseChange_id,
    LinearMap.id_apply, LinearEquiv.symm_apply_apply]

/-- Scalar extension commutes with composition of polynomial laws. -/
@[simp]
theorem baseChange_comp {P : Type*} [AddCommMonoid P] [Module R P]
    (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) :
    (g.comp f).baseChange B = (g.baseChange B).comp (f.baseChange B) := by
  ext S _ _ x
  let : Algebra R S := Algebra.compHom S (algebraMap R B)
  let : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' rfl
  simp only [comp_toFun', Function.comp_apply, baseChange_toFun',
    toFun_comp_apply, LinearEquiv.apply_symm_apply]

/-- The extended law at a scalar-extended vector, evaluated on the ground algebra. -/
@[simp]
theorem ground_baseChange (f : M →ₚₗ[R] N) (x : B ⊗[R] M) :
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
    rw [baseChange_toFun', cancelBaseChange_apply_eq, cancelBaseChange_symm_apply_eq]
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
    rw [← AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.toLinearEquiv_apply]
    rw [heN, heM]
    rw [baseChange_toFun', cancelBaseChange_apply_eq, cancelBaseChange_symm_apply_eq]
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
