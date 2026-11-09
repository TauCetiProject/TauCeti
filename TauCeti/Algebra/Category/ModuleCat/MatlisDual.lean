/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.RingTheory.MatlisDuality.Basic

/-!
# The Matlis dual on bundled modules over an algebra

Let `R` be a commutative ring and `A` an `R`-algebra. This file packages the Matlis dual
`D_R = Hom_R(-, E)` of `TauCeti/RingTheory/MatlisDuality/Basic.lean` as contravariant
additive functors between `ModuleCat A` and `ModuleCat Aᵐᵒᵖ`, and evaluation as a natural
isomorphism on modules of finite length over `R`, when `E` is an injective hull of `R ⧸ J(R)` and
`R ⧸ J(R)` is semisimple.

## Main definitions

* `ModuleCat.matlisDual` and `ModuleCat.matlisDualOp`: `D_R` as a contravariant additive functor
  from left to right modules and from right to left modules.
* `TauCeti.IsInjectiveEnvelope.moduleCatEvalIso` and
  `TauCeti.IsInjectiveEnvelope.moduleCatEvalIsoOp`: biduality for bundled modules of finite length.

## Implementation notes

A module over an `R`-algebra `A` is bundled in `ModuleCat A`, which remembers only the action of
`A`, so its `R`-action is recovered through the algebra map, by `ModuleCat.moduleOfAlgebra`. On the
dual of a module this equals the `R`-action on the values only propositionally, not definitionally.
The bundled duals `ModuleCat.matlisDualObj` and `ModuleCat.matlisDualOpObj` are therefore not
reducible to `MatlisDual`, and are compared with it by `ModuleCat.matlisDualObjEquiv` and
`ModuleCat.matlisDualOpObjEquiv`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Section II.3.
-/

public section

noncomputable section

open CategoryTheory Opposite TauCeti TauCeti.MatlisDual

universe u v t w

namespace ModuleCat

attribute [local instance] moduleOfAlgebra isScalarTower_moduleOfAlgebra

variable (R : Type u) [CommRing R] {A : Type t} [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E]

section Left

/-- The Matlis dual of a left `A`-module, as a bundled right `A`-module. -/
def matlisDualObj (M : ModuleCat.{w} A) : ModuleCat.{max w v} Aᵐᵒᵖ :=
  ModuleCat.of Aᵐᵒᵖ (MatlisDual R E M)

/-- The underlying module of the bundled dual of a left module is its Matlis dual. -/
def matlisDualObjEquiv (M : ModuleCat.{w} A) : matlisDualObj R E M ≃ₗ[Aᵐᵒᵖ] MatlisDual R E M :=
  LinearEquiv.refl _ _

/-- The underlying `R`-module of the bundled dual of a left module is the module of linear maps. -/
def matlisDualObjLinearEquiv (M : ModuleCat.{w} A) : matlisDualObj R E M ≃ₗ[R] (M →ₗ[R] E) :=
  ((matlisDualObjEquiv R E M).restrictScalars R).trans (equivLinearMap R E M)

theorem matlisDualObjLinearEquiv_apply (M : ModuleCat.{w} A) (φ : matlisDualObj R E M) :
    matlisDualObjLinearEquiv R E M φ = equivLinearMap R E M (matlisDualObjEquiv R E M φ) :=
  (rfl)

/-- The right action on the bundled dual of a left module is precomposition with the left action. -/
@[simp]
theorem matlisDualObjLinearEquiv_smul (M : ModuleCat.{w} A) (a : Aᵐᵒᵖ) (φ : matlisDualObj R E M)
    (x : M) :
    matlisDualObjLinearEquiv R E M (a • φ) x = matlisDualObjLinearEquiv R E M φ (a.unop • x) := by
  simp [matlisDualObjLinearEquiv_apply]

/-- The dual of a morphism of left modules. -/
def matlisDualMap {M M' : ModuleCat.{w} A} (g : M ⟶ M') :
    matlisDualObj R E M' ⟶ matlisDualObj R E M :=
  ModuleCat.ofHom ((matlisDualObjEquiv R E M).symm.toLinearMap ∘ₗ map g.hom ∘ₗ
    (matlisDualObjEquiv R E M').toLinearMap)

@[simp]
theorem matlisDualObjEquiv_map_apply {M M' : ModuleCat.{w} A} (g : M ⟶ M')
    (φ : matlisDualObj R E M') (x : M) :
    equivLinearMap R E M (matlisDualObjEquiv R E M (matlisDualMap R E g φ)) x =
      equivLinearMap R E M' (matlisDualObjEquiv R E M' φ) (g x) :=
  map_apply g.hom (matlisDualObjEquiv R E M' φ) x

/-- The Matlis dual `D_R = Hom_R(-, E)`, from left to right `A`-modules. -/
@[expose, simps]
def matlisDual : (ModuleCat.{w} A)ᵒᵖ ⥤ ModuleCat.{max w v} Aᵐᵒᵖ where
  obj M := matlisDualObj R E M.unop
  map g := matlisDualMap R E g.unop
  map_id M := by
    ext φ
    apply (matlisDualObjEquiv R E M.unop).injective
    ext x
    simp
  map_comp g h := by
    ext φ
    apply (matlisDualObjEquiv R E _).injective
    ext x
    simp

theorem matlisDualMap_add {M M' : ModuleCat.{w} A} (g h : M ⟶ M') :
    matlisDualMap R E (g + h) = matlisDualMap R E g + matlisDualMap R E h := by
  ext φ
  apply (matlisDualObjEquiv R E _).injective
  ext x
  refine (matlisDualObjEquiv_map_apply R E (g + h) φ x).trans ?_
  simp [ModuleCat.hom_add, map_add]

instance : (matlisDual R E (A := A)).Additive where
  map_add := matlisDualMap_add R E _ _

end Left

section Right

/-- The Matlis dual of a right `A`-module, as a bundled left `A`-module. -/
def matlisDualOpObj (N : ModuleCat.{w} Aᵐᵒᵖ) : ModuleCat.{max w v} A :=
  ModuleCat.of A (MatlisDual R E N)

/-- The underlying module of the bundled dual of a right module is its Matlis dual. -/
def matlisDualOpObjEquiv (N : ModuleCat.{w} Aᵐᵒᵖ) : matlisDualOpObj R E N ≃ₗ[A] MatlisDual R E N :=
  LinearEquiv.refl _ _

/-- The dual of a morphism of right modules. -/
def matlisDualOpMap {N N' : ModuleCat.{w} Aᵐᵒᵖ} (g : N ⟶ N') :
    matlisDualOpObj R E N' ⟶ matlisDualOpObj R E N :=
  ModuleCat.ofHom ((matlisDualOpObjEquiv R E N).symm.toLinearMap ∘ₗ mapOp g.hom ∘ₗ
    (matlisDualOpObjEquiv R E N').toLinearMap)

@[simp]
theorem matlisDualOpObjEquiv_map_apply {N N' : ModuleCat.{w} Aᵐᵒᵖ} (g : N ⟶ N')
    (φ : matlisDualOpObj R E N') (x : N) :
    equivLinearMap R E N (matlisDualOpObjEquiv R E N (matlisDualOpMap R E g φ)) x =
      equivLinearMap R E N' (matlisDualOpObjEquiv R E N' φ) (g x) :=
  mapOp_apply g.hom (matlisDualOpObjEquiv R E N' φ) x

/-- The Matlis dual `D_R = Hom_R(-, E)`, from right to left `A`-modules. -/
@[expose, simps]
def matlisDualOp : (ModuleCat.{w} Aᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{max w v} A where
  obj N := matlisDualOpObj R E N.unop
  map g := matlisDualOpMap R E g.unop
  map_id N := by
    ext φ
    apply (matlisDualOpObjEquiv R E N.unop).injective
    ext x
    simp
  map_comp g h := by
    ext φ
    apply (matlisDualOpObjEquiv R E _).injective
    ext x
    simp

theorem matlisDualOpMap_add {N N' : ModuleCat.{w} Aᵐᵒᵖ} (g h : N ⟶ N') :
    matlisDualOpMap R E (g + h) = matlisDualOpMap R E g + matlisDualOpMap R E h := by
  ext φ
  apply (matlisDualOpObjEquiv R E _).injective
  ext x
  refine (matlisDualOpObjEquiv_map_apply R E (g + h) φ x).trans ?_
  simp [ModuleCat.hom_add, map_add]

instance : (matlisDualOp R E (A := A)).Additive where
  map_add := matlisDualOpMap_add R E _ _

end Right

end ModuleCat

namespace TauCeti

open ModuleCat

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

section Eval

variable {R : Type u} [CommRing R] [IsSemisimpleRing (R ⧸ Ring.jacobson R)] {E : Type v}
  [AddCommGroup E] [Module R E] [Small.{v} R] {f : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type t}
  [Ring A] [Algebra R A] (hf : IsInjectiveEnvelope f)

include hf

/-- Matlis biduality for a left `A`-module `M` of finite length over `R`, as an isomorphism
`M ≅ D_R (D_R M)` of bundled modules. -/
def IsInjectiveEnvelope.moduleCatEvalIso (M : ModuleCat.{v} A) (hM : IsFiniteLength R M) :
    M ≅ matlisDualOpObj R E (matlisDualObj R E M) :=
  ((hf.matlisDualEvalEquiv hM).trans
    ((MatlisDual.congrOp (matlisDualObjEquiv R E M)).trans
      (matlisDualOpObjEquiv R E (matlisDualObj R E M)).symm)).toModuleIso

/-- The isomorphism `M ≅ D_R (D_R M)` is evaluation. -/
@[simp]
theorem IsInjectiveEnvelope.moduleCatEvalIso_hom_apply (M : ModuleCat.{v} A)
    (hM : IsFiniteLength R M) (x : M) (φ : matlisDualObj R E M) :
    equivLinearMap R E _ (matlisDualOpObjEquiv R E _ ((hf.moduleCatEvalIso M hM).hom x)) φ =
      equivLinearMap R E M (matlisDualObjEquiv R E M φ) x := by
  simp [moduleCatEvalIso]

/-- Matlis biduality for a right `A`-module `N` of finite length over `R`, as an isomorphism
`N ≅ D_R (D_R N)` of bundled modules. -/
def IsInjectiveEnvelope.moduleCatEvalIsoOp (N : ModuleCat.{v} Aᵐᵒᵖ) (hN : IsFiniteLength R N) :
    N ≅ matlisDualObj R E (matlisDualOpObj R E N) :=
  ((hf.matlisDualEvalEquivOp (A := A) hN).trans
    ((MatlisDual.congr (matlisDualOpObjEquiv R E N)).trans
      (matlisDualObjEquiv R E (matlisDualOpObj R E N)).symm)).toModuleIso

/-- The isomorphism `N ≅ D_R (D_R N)` is evaluation. -/
@[simp]
theorem IsInjectiveEnvelope.moduleCatEvalIsoOp_hom_apply (N : ModuleCat.{v} Aᵐᵒᵖ)
    (hN : IsFiniteLength R N) (x : N) (φ : matlisDualOpObj R E N) :
    equivLinearMap R E _ (matlisDualObjEquiv R E _ ((hf.moduleCatEvalIsoOp N hN).hom x)) φ =
      equivLinearMap R E N (matlisDualOpObjEquiv R E N φ) x := by
  simp [moduleCatEvalIsoOp]

/-- The isomorphism `M ≅ D_R (D_R M)` is natural in `M`. -/
theorem IsInjectiveEnvelope.moduleCatEvalIso_hom_naturality {M M' : ModuleCat.{v} A} (g : M ⟶ M')
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    g ≫ (hf.moduleCatEvalIso M' hM').hom =
      (hf.moduleCatEvalIso M hM).hom ≫ matlisDualOpMap R E (matlisDualMap R E g) := by
  ext x
  apply (matlisDualOpObjEquiv R E _).injective
  ext φ
  simp

/-- The isomorphism `N ≅ D_R (D_R N)` is natural in `N`. -/
theorem IsInjectiveEnvelope.moduleCatEvalIsoOp_hom_naturality {N N' : ModuleCat.{v} Aᵐᵒᵖ}
    (g : N ⟶ N') (hN : IsFiniteLength R N) (hN' : IsFiniteLength R N') :
    g ≫ (hf.moduleCatEvalIsoOp N' hN').hom =
      (hf.moduleCatEvalIsoOp N hN).hom ≫ matlisDualMap R E (matlisDualOpMap R E g) := by
  ext x
  apply (matlisDualObjEquiv R E _).injective
  ext φ
  simp

/-- Evaluation on the dual `D_R M` of `M` is precomposition with the inverse of evaluation on `M`.
This is the triangle identity of the Matlis duality. -/
theorem IsInjectiveEnvelope.moduleCatEvalIsoOp_matlisDualObj_hom (M : ModuleCat.{v} A)
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R (matlisDualObj R E M)) :
    (hf.moduleCatEvalIsoOp (A := A) (matlisDualObj R E M) hM').hom =
      matlisDualMap R E (hf.moduleCatEvalIso M hM).inv := by
  ext φ
  apply (matlisDualObjEquiv R E _).injective
  ext Ψ
  obtain ⟨x, rfl⟩ : ∃ x, (hf.moduleCatEvalIso M hM).hom x = Ψ :=
    ⟨(hf.moduleCatEvalIso M hM).inv Ψ, by simp⟩
  simp

end Eval

end TauCeti
