/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Cokernel.Basic
public import TauCeti.CommutativeAlgebra.MatrixFactorization.BaseChange.Basic

/-!
# The cokernel of the reduction modulo the potential

Let `X = (X₀ --d₀--> X₁ --d₁--> X₀)` be a finite-projective matrix factorization of `w : S`.
The cokernel of its reduction modulo `w` is a module over `S/(w)`; viewed as an `S`-module, it
receives the surjection `y ↦ [1 ⊗ y]` from the odd component `X₁`. Its kernel is the image of
`d₀`: if `1 ⊗ y` lies in the image of the reduced `d₀`, then `y` differs from an element of the
image of `d₀` by `w y' = d₀ (d₁ y')`. So the cokernel of the reduction modulo `w` is the cokernel
of `d₀` over `S`.

## Main definitions

* `TauCeti.MatrixFactorization.quotientCokernelπ`: the surjection `y ↦ [1 ⊗ y]` from the odd
  component onto the cokernel of the reduction modulo `w`.

## Main results

* `TauCeti.MatrixFactorization.exact_d₀_quotientCokernelπ`: the kernel of `quotientCokernelπ` is
  the image of `d₀`.

## References

* D. Eisenbud, *Homological algebra on a complete intersection, with an application to group
  representations*, Trans. Amer. Math. Soc. **260** (1980), Section 5.
-/

public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {S : Type u} [CommRing S] {w : S}

/-- The `S`-linear surjection `y ↦ [1 ⊗ y]` from the odd component onto the cokernel of the
reduction modulo `w`, viewed as an `S`-module. Its kernel is the image of `d₀`
(`TauCeti.MatrixFactorization.exact_d₀_quotientCokernelπ`). -/
def quotientCokernelπ (X : MatrixFactorization S w) :
    X.obj.X₁.obj ⟶ (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).obj
      (cokernelFunctor.obj ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)).obj :=
  (ModuleCat.extendRestrictScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {w}))).unit.app
      X.obj.X₁.obj ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {w}))).map
      (cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X))

/-- On elements, `quotientCokernelπ` sends `y` to the class of `1 ⊗ y`. -/
theorem quotientCokernelπ_apply (X : MatrixFactorization S w) (y : X.obj.X₁) :
    quotientCokernelπ X y =
      cokernelπ ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X)
        ((1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] y) :=
  (rfl)

/-- Every element of the cokernel of the reduction is the class of `1 ⊗ y` for some `y`. -/
theorem quotientCokernelπ_surjective (X : MatrixFactorization S w) :
    Function.Surjective (quotientCokernelπ X) := by
  intro m
  obtain ⟨z, rfl⟩ :=
    cokernelπ_surjective ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).obj X) m
  obtain ⟨y, rfl⟩ := TensorProduct.exists_one_tmul_eq (Ideal.span {w}) z
  exact ⟨y, quotientCokernelπ_apply X y⟩

/-- The even differential and `y ↦ [1 ⊗ y]` form an exact pair: the cokernel of the reduction
modulo `w` is the cokernel of `d₀` over `S`. -/
theorem exact_d₀_quotientCokernelπ (X : MatrixFactorization S w) :
    Function.Exact X.obj.d₀.hom.hom (quotientCokernelπ X).hom := by
  intro y
  rw [quotientCokernelπ_apply]
  constructor
  · -- If `1 ⊗ y = d₀' (1 ⊗ x)`, then `y - d₀ x = w y' = d₀ (d₁ y')`.
    intro h
    obtain ⟨z, hz⟩ := (exact_d₀_cokernelπ _ _).1 h
    obtain ⟨x, rfl⟩ := TensorProduct.exists_one_tmul_eq (M := X.obj.X₀) (Ideal.span {w}) z
    have : (1 : S ⧸ Ideal.span {w}) ⊗ₜ[S] (y - X.obj.d₀.hom.hom x) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.2 hz.symm
    obtain ⟨y', hy'⟩ := (TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq w _).1 this
    refine ⟨x + X.obj.d₁.hom.hom y', ?_⟩
    rw [map_add, d₁_comp_d₀_apply, hy', add_sub_cancel]
  · rintro ⟨x, rfl⟩
    exact (exact_d₀_cokernelπ _ _).2
      ⟨(1 : S ⧸ Ideal.span {w}) ⊗ₜ[S, Ideal.Quotient.mk (Ideal.span {w})] x, rfl⟩

/-- `y ↦ [1 ⊗ y]` is natural with respect to morphisms of matrix factorizations. -/
@[simp]
theorem quotientCokernelπ_naturality_apply {X Y : MatrixFactorization S w} (g : X ⟶ Y)
    (y : X.obj.X₁) :
    (cokernelFunctor.map ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g)).hom
        (quotientCokernelπ X y) = quotientCokernelπ Y (g.hom.f₁.hom y) :=
  cokernelπ_naturality_apply ((baseChangeFunctor (Ideal.Quotient.mk (Ideal.span {w}))).map g) _

end TauCeti.MatrixFactorization
