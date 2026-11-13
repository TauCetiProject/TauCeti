/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Linear combinations and scalar extension of algebraically independent families

If linear combinations `yᵢ = ∑ⱼ Cᵢⱼ • xⱼ` formed from a matrix `C` are algebraically independent
over a commutative ring `R`, then the rows of `C` are `R`-linearly independent
(`AlgebraicIndependent.linearIndependent_row`).

Under extension of scalars from `R` to an `R`-algebra `S`, evaluating `S[Xᵢ]` at `1 ⊗ₜ yᵢ` inside
`S ⊗[R] A` factors as the canonical isomorphism `S[Xᵢ] ≃ₐ[S] S ⊗[R] R[Xᵢ]` followed by
`id_S ⊗ aeval y` (`MvPolynomial.aeval_tmul_one_apply`). Consequently:

* finiteness and integrality of `MvPolynomial.aeval y` are preserved under arbitrary base change
  `S / R` (`MvPolynomial.finite_aeval_tmul_one`, `MvPolynomial.isIntegral_aeval_tmul_one`);
* when `S` is `R`-flat, algebraic independence of `y` over `R` implies algebraic independence of
  `1 ⊗ₜ yᵢ` over `S` (`AlgebraicIndependent.tmul_one`, `AlgebraicIndependent.includeRight_comp`).

## Main results

* `AlgebraicIndependent.linearIndependent_row`: algebraic independence of `i ↦ ∑ j, C i j • x j`
  implies `LinearIndependent R C.row`.
* `MvPolynomial.aeval_tmul_one_apply`: `aeval (1 ⊗ₜ y ·)` factors through
  `MvPolynomial.algebraTensorAlgEquiv` and `Algebra.TensorProduct.map`.
* `AlgebraicIndependent.tmul_one`, `AlgebraicIndependent.includeRight_comp`: flat scalar extension
  preserves algebraic independence.
* `MvPolynomial.finite_aeval_tmul_one`, `MvPolynomial.isIntegral_aeval_tmul_one`: scalar extension
  preserves module-finiteness and integrality of `MvPolynomial.aeval`.
-/

public section

open scoped TensorProduct

namespace MvPolynomial

section BaseChange

variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluating a polynomial over `S` at `1 ⊗ₜ[R] y i` in `S ⊗[R] A` agrees with transporting along
`(algebraTensorAlgEquiv R S).symm` and applying `id_S ⊗ aeval y`. -/
theorem aeval_tmul_one_apply {S : Type*} [CommRing S] [Algebra R S] (y : ι → A)
    (p : MvPolynomial ι S) :
    aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) p =
      Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)
        ((algebraTensorAlgEquiv R S).symm p) := by
  let φ : S ⊗[R] MvPolynomial ι R →ₐ[S] S ⊗[R] A :=
    Algebra.TensorProduct.lift (Algebra.ofId S (S ⊗[R] A))
      (Algebra.TensorProduct.includeRight.comp (aeval (R := R) y)) fun _ _ ↦ Commute.all _ _
  have hφ_eq : ∀ z, φ z = Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y) z :=
    fun z ↦ z.inductionOn
      (fun s q ↦ by
        simp [φ, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
          Algebra.TensorProduct.tmul_mul_tmul])
      fun u v hu hv ↦ by simp [map_add, hu, hv]
  have hsymm_X (i : ι) :
      (algebraTensorAlgEquiv R S).symm (X i : MvPolynomial ι S) =
        (1 : S) ⊗ₜ[R] (X i : MvPolynomial ι R) :=
    (algebraTensorAlgEquiv R S).injective (by simp)
  have hcomp : aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i) =
      φ.comp (algebraTensorAlgEquiv R S).symm.toAlgHom :=
    algHom_ext fun i ↦ by simp [φ, hsymm_X]
  rw [← hφ_eq, hcomp, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

/-- Module-finiteness of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra
`S`. -/
theorem finite_aeval_tmul_one (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hfin : (aeval (R := R) y).Finite) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).Finite := by
  have heq : (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
        (algebraTensorAlgEquiv R S).symm.toRingHom :=
    RingHom.ext fun p ↦ aeval_tmul_one_apply y p
  rw [AlgHom.Finite, heq]
  exact (RingHom.Finite.tensorProductMap (AlgHom.Finite.id R S) hfin).comp
    (RingHom.Finite.of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective)

/-- Integrality of `MvPolynomial.aeval y` is preserved under base change to any `R`-algebra `S`. -/
theorem isIntegral_aeval_tmul_one (S : Type*) [CommRing S] [Algebra R S] {y : ι → A}
    (hint : (aeval (R := R) y).toRingHom.IsIntegral) :
    (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom.IsIntegral := by
  have heq : (aeval (R := S) (fun i ↦ (1 : S) ⊗ₜ[R] y i)).toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
        (algebraTensorAlgEquiv R S).symm.toRingHom :=
    RingHom.ext fun p ↦ aeval_tmul_one_apply y p
  rw [heq]
  refine RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ (algebraTensorAlgEquiv R S).symm.surjective) ?_
  intro z
  refine z.inductionOn (fun s a ↦ ?_) (fun u v hu hv ↦ RingHom.IsIntegralElem.add _ hu hv)
  obtain ⟨q, hq_monic, hq_eval⟩ := hint a
  have ha : (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.IsIntegralElem
      ((1 : S) ⊗ₜ[R] a) := by
    refine ⟨q.map (Algebra.TensorProduct.includeRight :
        MvPolynomial ι R →ₐ[R] S ⊗[R] MvPolynomial ι R).toRingHom, hq_monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomm :
        ((Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            MvPolynomial ι R →ₐ[R] S ⊗[R] MvPolynomial ι R).toRingHom) =
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom.comp
          (aeval (R := R) y).toRingHom :=
      RingHom.ext fun p ↦ by simp
    have h1a : (1 : S) ⊗ₜ[R] a =
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom a :=
      (rfl)
    rw [hcomm, h1a, ← Polynomial.hom_eval₂, hq_eval, map_zero]
  have hs : (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom.IsIntegralElem
      (s ⊗ₜ[R] (1 : A)) := by
    simpa using RingHom.isIntegralElem_map
      (Algebra.TensorProduct.map (AlgHom.id R S) (aeval (R := R) y)).toRingHom
      (x := s ⊗ₜ[R] (1 : MvPolynomial ι R))
  simpa [Algebra.TensorProduct.tmul_mul_tmul] using RingHom.IsIntegralElem.mul _ hs ha

end BaseChange

end MvPolynomial

namespace AlgebraicIndependent

/-- If the linear combinations `i ↦ ∑ j, C i j • x j` in an `R`-algebra `A` are algebraically
independent over `R`, then the rows of `C` are `R`-linearly independent. -/
theorem linearIndependent_row {ι κ R A : Type*} [Fintype κ] [CommRing R] [CommRing A]
    [Algebra R A] {C : Matrix ι κ R} {x : κ → A}
    (hy : AlgebraicIndependent R fun i ↦ ∑ j, C i j • x j) :
    LinearIndependent R C.row := by
  let L : (κ → R) →ₗ[R] A := ∑ j : κ, (LinearMap.proj j).smulRight (x j)
  have hL : (fun i ↦ ∑ j, C i j • x j) = L ∘ C.row := by
    funext i
    simp [L, Matrix.row_apply]
  exact LinearIndependent.of_comp L (hL ▸ hy.linearIndependent)

/-- Algebraic independence of `y : ι → A` over `R` is preserved upon extending scalars to any flat
`R`-algebra `S`. -/
theorem tmul_one {ι R A : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [CommRing A] [Algebra R A] {y : ι → A} (hy : AlgebraicIndependent R y) :
    AlgebraicIndependent S fun i ↦ (1 : S) ⊗ₜ[R] y i := by
  rw [algebraicIndependent_iff_injective_aeval] at hy ⊢
  have hinj :
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id R S) (MvPolynomial.aeval y)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S)
      (MvPolynomial.aeval y).toLinearMap hy
  intro p q hpq
  rw [MvPolynomial.aeval_tmul_one_apply, MvPolynomial.aeval_tmul_one_apply] at hpq
  exact (MvPolynomial.algebraTensorAlgEquiv R S).symm.injective (hinj hpq)

/-- Composing an algebraically independent family `y : ι → A` with
`Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A` yields a family algebraically independent
over any flat `R`-algebra `S`. -/
theorem includeRight_comp {ι R A : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [CommRing A] [Algebra R A] {y : ι → A} (hy : AlgebraicIndependent R y) :
    AlgebraicIndependent S
      ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)) ∘ y) :=
  hy.tmul_one S

end AlgebraicIndependent
