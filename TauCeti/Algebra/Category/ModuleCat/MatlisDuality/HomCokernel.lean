/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.FiniteLength
public import TauCeti.CategoryTheory.Linear.HomCokernel.Basic
import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Matlis duality on Hom cokernels

The linear Hom equivalence for finite-length target modules identifies the cokernels of
precomposition and dual postcomposition, with injective dualizing coefficients whose residue-field
Hom modules have length one.
-/

public section

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

namespace ModuleCat

universe u v w t

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  [Module.Injective R E] [Small.{v} R] {A : Type t} [Ring A] [Algebra R A]
  (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)

include hE in
/-- Dualizing morphisms identifies the cokernel of precomposition with `f` and the
cokernel of postcomposition with its Matlis dual, when the target `B` has finite length over `R`,
`E` is injective, and `Hom_R(R/𝔪, E)` has length one for every maximal ideal `𝔪`. -/
noncomputable def matlisDualOpHomCokernelEquiv {X Y B : ModuleCat.{max v w} Aᵐᵒᵖ}
    (hB : IsFiniteLength R B) (f : X ⟶ Y) :
    HomCokernel R f B ≃ₗ[R]
      CovariantHomCokernel R (matlisDualOpMap R E f) (matlisDualOpObj R E B) := by
  letI : Module R (Y ⟶ B) := Linear.homModule Y B
  letI : Module R (X ⟶ B) := Linear.homModule X B
  let e₀ : (Y ⟶ B) ≃ₗ[R] _ := matlisDualOpHomLinearEquiv hE hB
  let e₁ : (X ⟶ B) ≃ₗ[R] _ := matlisDualOpHomLinearEquiv hE hB
  refine Submodule.Quotient.equiv _ _ e₁
    ((Linear.leftComp R B f).map_range_eq_range_of_comp_eq e₀.surjective ?_)
  ext g
  simp [e₀, e₁]

/-- The quotient comparison sends the class of a morphism to the class of its Matlis dual. -/
@[simp]
theorem matlisDualOpHomCokernelEquiv_mk {X Y B : ModuleCat.{max v w} Aᵐᵒᵖ}
    (hB : IsFiniteLength R B) (f : X ⟶ Y) (g : X ⟶ B) :
    let _ := Linear.homModule (R := R) X B
    matlisDualOpHomCokernelEquiv hE hB f (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (matlisDualOpMap R E g) := by
  simp only [matlisDualOpHomCokernelEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.coe_coe, matlisDualOpHomLinearEquiv_apply]

end ModuleCat
