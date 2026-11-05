/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Bijectivity of lifts of tensor products from bases

Let `R → S → T` be a tower of commutative semirings, `U` a commutative `R`-algebra and
`u : U →ₐ[R] T` an `R`-algebra map. The `S`-algebra map `S ⊗[R] U → T`, `x ⊗ y ↦ x * u y`, is
bijective as soon as `u` carries a basis of `U` over `R` to a basis of `T` over `S`: it carries the
basis `1 ⊗ bᵢ` of `S ⊗[R] U` over `S` (Mathlib's `Algebra.TensorProduct.basis`) to that basis of
`T`.

Dually, when the scalar-extension algebra `S` has a finite `R`-basis `b`, an `R`-linear map
`f : M →ₗ[R] N` into an `S`-module `N` exhibits `N` as the base change `S ⊗[R] M` whenever `N`
admits additive coordinate maps `c i : N → M` that extract the `b`-coordinates on `s • f m` and
reconstruct every element `n : N` as `∑ i, b i • f (c i n)`. This applies to completions and duals
such as completed group algebras and abstract measures, where `M` itself need not be free.

## Main results

* `Algebra.TensorProduct.lift_bijective_of_basis`: the lift `S ⊗[R] U → T` of `S → T` and `u` is
  bijective if `u` carries a basis of `U` over `R` to a basis of `T` over `S`.
* `LinearMap.liftBaseChange_bijective_of_basis_coord`: `f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is
  bijective when `S` has a finite `R`-basis `b` with additive coordinate maps `c i : N → M`.
* `IsBaseChange.of_basis_coord`: the corresponding `IsBaseChange S f` criterion.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

/-- **A lift of tensor products carrying a basis to a basis is bijective.** If `u : U →ₐ[R] T`
carries a basis `bᵢ` of `U` over `R` to a basis of `T` over `S`, then the `S`-algebra map
`S ⊗[R] U → T`, `x ⊗ y ↦ x * u y`, is bijective. -/
theorem lift_bijective_of_basis {R S U T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring U] [CommSemiring T] [Algebra R S] [Algebra R U] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (u : U →ₐ[R] T) {ι : Type*}
    (bU : Module.Basis ι R U) (bT : Module.Basis ι S T) (hb : ∀ i, bT i = u (bU i)) :
    Function.Bijective (lift (Algebra.ofId S T) u fun _ _ ↦ .all _ _) := by
  let b := basis S bU
  have hψ : (lift (Algebra.ofId S T) u fun _ _ ↦ .all _ _).toLinearMap =
      (b.equiv bT (Equiv.refl ι)).toLinearMap :=
    b.ext fun i ↦ by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [b, hb]
  rw [← AlgHom.coe_toLinearMap, hψ]
  exact (b.equiv bT (Equiv.refl ι)).bijective

end Algebra.TensorProduct

section BasisCoord

variable {R S M N ι C : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Fintype ι] [FunLike C N M] [AddMonoidHomClass C N M]

/-- **Bijectivity of `LinearMap.liftBaseChange` from finite-basis coordinate maps.** Let `b` be a
finite `R`-basis of `S` and `f : M →ₗ[R] N` an `R`-linear map into an `S`-module `N`. If additive
coordinate maps `c i : N → M` satisfy `c i (s • f m) = b.coord i s • m` and reconstruct every
`n : N` as `∑ i, b i • f (c i n) = n`, then `f.liftBaseChange S : S ⊗[R] M →ₗ[S] N` is
bijective. -/
theorem LinearMap.liftBaseChange_bijective_of_basis_coord
    (f : M →ₗ[R] N) (b : Module.Basis ι R S) (c : ι → C)
    (hc : ∀ i (s : S) (m : M), c i (s • f m) = b.coord i s • m)
    (hsum : ∀ n : N, ∑ i, b i • f (c i n) = n) :
    Function.Bijective (f.liftBaseChange S) := by
  classical
  let e₁ : S ⊗[R] M ≃ₗ[R] (ι → M) :=
    (TensorProduct.equivFinsuppOfBasisLeft b).trans (Finsupp.linearEquivFunOnFinite R M ι)
  let Ψ : (ι → M) →ₗ[R] N :=
    ∑ i, (LinearMap.lsmul S N (b i)).restrictScalars R ∘ₗ f ∘ₗ LinearMap.proj i
  let e₂ : (ι → M) ≃ₗ[R] N :=
    { Ψ with
      invFun n i := c i n
      left_inv d := funext fun j ↦ by
        simp [Ψ, map_sum, hc, b.repr_self, Finsupp.single_apply]
      right_inv n := by
        simpa [Ψ] using hsum n }
  have hcomm : (f.liftBaseChange S).restrictScalars R = e₂.toLinearMap.comp e₁.toLinearMap :=
    TensorProduct.ext' fun s m ↦ by
      simp only [LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
        LinearEquiv.coe_coe, e₁, e₂, Ψ, LinearEquiv.trans_apply,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Finsupp.linearEquivFunOnFinite_apply,
        Finsupp.mapRange_apply, LinearMap.sum_apply, LinearMap.lsmul_apply, LinearMap.proj_apply,
        map_smul, ← smul_assoc, ← Finset.sum_smul, b.sum_repr]
  have hfun : ⇑(f.liftBaseChange S) = ⇑(e₁.trans e₂) :=
    funext fun z ↦ LinearMap.congr_fun hcomm z
  exact hfun ▸ (e₁.trans e₂).bijective

/-- **Base-change criterion from finite-basis coordinate maps.** Under the hypotheses of
`LinearMap.liftBaseChange_bijective_of_basis_coord`, `f : M →ₗ[R] N` exhibits `N` as the base
change of `M` along `R → S`. -/
theorem IsBaseChange.of_basis_coord
    (f : M →ₗ[R] N) (b : Module.Basis ι R S) (c : ι → C)
    (hc : ∀ i (s : S) (m : M), c i (s • f m) = b.coord i s • m)
    (hsum : ∀ n : N, ∑ i, b i • f (c i n) = n) :
    IsBaseChange S f :=
  IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (f.liftBaseChange S)
      (f.liftBaseChange_bijective_of_basis_coord b c hc hsum))
    fun _ ↦ by simp

end BasisCoord
