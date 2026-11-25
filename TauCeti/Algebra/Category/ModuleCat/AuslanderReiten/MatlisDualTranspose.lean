/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import TauCeti.Algebra.Module.AuslanderReiten.PresentationNaturality
public import TauCeti.Algebra.Module.Projective.FinitePresentation

/-!
# The bundled translate `D Tr X` of a presented module

Let `R` be a commutative ring, `A` an `R`-algebra, `E` an `R`-module and `D = Hom_R(-, E)`. For
an `A`-module `X` with a presentation `P` by finitely generated projectives, the dual
`τX = D Tr X` of its transpose is a left `A`-module, bundled here as an object of `ModuleCat A`.
A lift `(t₀, t₁)` of a map `t : X → X'` to the presentations induces `D Tr(t) : τX → τX'`, and
`τX` is the bundled Matlis dual of the right module `Tr X`.

## Main definitions

* `ModuleCat.matlisDualTranspose R E P`: the module `τX = D Tr X`.
* `ModuleCat.matlisDualTransposeEquiv`: the carrier of `τX` is `Hom_R(Tr X, E)`.
* `ModuleCat.matlisDualTransposeMap`: the map `D Tr(t) : τX → τX'` induced by a lift of `t`,
  functorial in the lift (`_id`, `_comp`).
* `ModuleCat.matlisDualOpTransposeIso`: the bundled Matlis dual of `Tr X` is `τX`, compatibly with
  maps (`ModuleCat.matlisDualOp_map_comp_matlisDualOpTransposeIso_hom`).

## Implementation notes

An object of `ModuleCat A` remembers only its `A`-action. Its `R`-action, and the `R`-linear
structure of `ModuleCat A`, come from the scoped instances of `ModuleCat.Algebra`. On the carrier
`Hom_R(Tr X, E)` of `τX` this action agrees with the native `R`-action only propositionally. The
bundled translate `ModuleCat.matlisDualTranspose` is therefore a plain definition, so that
instance search sees only the categorical action on it, and `ModuleCat.matlisDualTransposeEquiv`
identifies its carrier with `Hom_R(Tr X, E)` as `A`-modules only.
-/

public section

namespace ModuleCat

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable (R : Type u) {A : Type v} (E : Type w) [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup E] [Module R E] {X : ModuleCat.{max u v w} A}
  (P : FiniteProjectivePresentation X)

/-- The **Auslander–Reiten translate** `τX = D Tr X = Hom_R(Tr X, E)` of a module `X` with a
presentation `P` by finitely generated projectives, as an object of `ModuleCat A`. -/
@[expose] def matlisDualTranspose : ModuleCat.{max u v w} A :=
  ModuleCat.of A (MatlisDual R E (AuslanderReitenTranspose P.p))

/-- The carrier of `τX = D Tr X` is `Hom_R(Tr X, E)`, as `A`-modules. Through it, morphisms into
`τX` are the `A`-linear maps into `Hom_R(Tr X, E)` (`ModuleCat.homLinearEquivOfLinearEquiv`). -/
def matlisDualTransposeEquiv :
    MatlisDual R E (AuslanderReitenTranspose P.p) ≃ₗ[A] matlisDualTranspose R E P :=
  LinearEquiv.refl _ _

@[simp]
theorem matlisDualTransposeEquiv_apply (φ : MatlisDual R E (AuslanderReitenTranspose P.p)) :
    matlisDualTransposeEquiv R E P φ = φ :=
  (rfl)

@[simp]
theorem matlisDualTransposeEquiv_symm_apply (φ : matlisDualTranspose R E P) :
    (matlisDualTransposeEquiv R E P).symm φ = φ :=
  (rfl)

variable {X' : ModuleCat.{max u v w} A} (P' : FiniteProjectivePresentation X')
  {t₀ : P.P₀ →ₗ[A] P'.P₀} {t₁ : P.P₁ →ₗ[A] P'.P₁}

/-- The map `D Tr(t) : D Tr X → D Tr X'` induced by a lift `(t₀, t₁)` of a map `X → X'` to the
presentations: the Matlis dual of the map of transposes. -/
noncomputable def matlisDualTransposeMap (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁) :
    matlisDualTranspose R E P ⟶ matlisDualTranspose R E P' :=
  ofHom (LinearMap.auslanderReitenTranslateMap t₀ t₁ ht₁)

/-- `D Tr(t)` evaluates through the map of transposes. -/
@[simp]
theorem matlisDualTransposeMap_apply (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (φ : matlisDualTranspose R E P) (x : AuslanderReitenTranspose P'.p) :
    MatlisDual.equivLinearMap R E _ ((matlisDualTransposeMap R E P P' ht₁).hom φ) x =
      MatlisDual.equivLinearMap R E _ φ (AuslanderReitenTranspose.map t₀ t₁ ht₁ x) := by
  rw [matlisDualTransposeMap]
  exact LinearMap.auslanderReitenTranslateMap_apply t₀ t₁ ht₁ φ x

/-- `D Tr(t)` is the Matlis dual of the map of transposes, on the carriers of `τX` and `τX'`. -/
theorem matlisDualTransposeMap_eq (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁) :
    matlisDualTransposeMap R E P P' ht₁ =
      ofHom ((matlisDualTransposeEquiv R E P').toLinearMap ∘ₗ
        MatlisDual.mapOp (AuslanderReitenTranspose.map t₀ t₁ ht₁) ∘ₗ
          (matlisDualTransposeEquiv R E P).symm.toLinearMap) := by
  ext φ : 2
  refine (MatlisDual.equivLinearMap R E _).injective (LinearMap.ext fun x ↦ ?_)
  rw [matlisDualTransposeMap_apply]
  exact (MatlisDual.mapOp_apply _ _ x).symm

/-- The identity lift induces the identity of `D Tr X`. -/
@[simp]
theorem matlisDualTransposeMap_id (ht₁ : LinearMap.id ∘ₗ P.p = P.p ∘ₗ LinearMap.id) :
    matlisDualTransposeMap R E P P ht₁ = 𝟙 _ := by
  rw [matlisDualTransposeMap, LinearMap.auslanderReitenTranslateMap_id, ModuleCat.ofHom_id]
  -- `τX` is the bundled module of `Hom_R(Tr X, E)`.
  rfl

/-- The maps `D Tr(t)` compose along composed lifts. -/
theorem matlisDualTransposeMap_comp {X'' : ModuleCat.{max u v w} A}
    (P'' : FiniteProjectivePresentation X'') {t₀' : P'.P₀ →ₗ[A] P''.P₀}
    {t₁' : P'.P₁ →ₗ[A] P''.P₁} (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁)
    (ht₁' : t₀' ∘ₗ P'.p = P''.p ∘ₗ t₁') (ht₁'' : (t₀' ∘ₗ t₀) ∘ₗ P.p = P''.p ∘ₗ (t₁' ∘ₗ t₁)) :
    matlisDualTransposeMap R E P P'' ht₁'' =
      matlisDualTransposeMap R E P P' ht₁ ≫ matlisDualTransposeMap R E P' P'' ht₁' := by
  rw [matlisDualTransposeMap, matlisDualTransposeMap, matlisDualTransposeMap,
    ← LinearMap.auslanderReitenTranslateMap_comp_map t₀ t₁ ht₁ t₀' t₁' ht₁', ModuleCat.ofHom_comp]
  -- The two sides differ only in the universe spelling of the objects `of A (Hom_R(Tr X, E))`
  -- and `τX`, which `rw` does not identify.
  rfl

/-- The bundled dual of `Tr X`, with the action of `R` through `Aᵐᵒᵖ`, is `τX = D Tr X`. -/
noncomputable def matlisDualOpTransposeIso :
    (matlisDualOp R E).obj (Opposite.op (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))) ≅
      matlisDualTranspose R E P :=
  (matlisDualOpObjEquivOfLinearEquiv R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p))).toModuleIso

/-- The dual of the map of transposes is `D Tr(t)`, through `ModuleCat.matlisDualOpTransposeIso`. -/
theorem matlisDualOp_map_comp_matlisDualOpTransposeIso_hom (ht₁ : t₀ ∘ₗ P.p = P'.p ∘ₗ t₁) :
    (matlisDualOp R E).map (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)).op ≫
        (matlisDualOpTransposeIso R E P').hom =
      (matlisDualOpTransposeIso R E P).hom ≫ matlisDualTransposeMap R E P P' ht₁ := by
  ext φ : 2
  refine (MatlisDual.equivLinearMap R E _).injective (LinearMap.ext fun τ ↦ ?_)
  -- `simp` does not apply `ModuleCat.hom_comp` here: the objects `D (Tr X)` and `τX` live in
  -- `ModuleCat` under two spellings of the same universe. Evaluate both sides instead.
  have h₁ := matlisDualOpObjEquivOfLinearEquiv_apply R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P'.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P'.p))
    (matlisDualOpMap R E (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)) φ) τ
  have h₂ := matlisDualOpObjEquiv_map_apply R E (ofHom (AuslanderReitenTranspose.map t₀ t₁ ht₁)) φ τ
  have h₃ := matlisDualOpObjEquivOfLinearEquiv_apply R E (of Aᵐᵒᵖ (AuslanderReitenTranspose P.p))
    (LinearEquiv.refl Aᵐᵒᵖ (AuslanderReitenTranspose P.p)) φ
    (AuslanderReitenTranspose.map t₀ t₁ ht₁ τ)
  exact h₁.trans (h₂.trans (h₃.symm.trans (matlisDualTransposeMap_apply R E P P' ht₁ _ τ).symm))

end ModuleCat
