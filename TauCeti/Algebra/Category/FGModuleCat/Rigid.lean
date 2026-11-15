/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Dual
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Subcategory

/-!
# Left duals of finite-dimensional vector spaces, and their duals in `ModuleCat`

The algebraic dual is both a left and a right dual in `FGModuleCat K`. Mathlib supplies the
right pairing. Here the left pairing is obtained from the right pairing of the dual space by
`CategoryTheory.exactPairingCongrRight`, using `FGModuleCat.dualEvalIso` for the classical
double-dual evaluation isomorphism. In particular this choice
does not use a braiding to construct the left dual. Its evaluation is the usual contraction,
and its adjoint mates are ordinary transposes.

For Mathlib's right pairing, `FGModuleCat.evaluation_hom_hom` and
`FGModuleCat.coevaluation_hom_hom` record that its evaluation and coevaluation are the
contraction `contractLeft` and the coevaluation `coevaluation` of linear algebra.

The resulting `LeftRigidCategory` and `RigidCategory` instances also give rigidity of
categories of group actions through Mathlib's existing instances.

Both pairings are also transported along the inclusion of `FGModuleCat K` into `ModuleCat K` by
`CategoryTheory.Functor.mapExactPairing`: a finite-dimensional space `V` is exactly paired with its
dual space on the right (`ModuleCat.exactPairingDual`) and on the left
(`ModuleCat.leftExactPairingDual`) in `ModuleCat K`, with the same contractions and coevaluations
(`ModuleCat.exactPairingDual_evaluation_apply`, `ModuleCat.exactPairingDual_coevaluation_hom`,
`ModuleCat.leftExactPairingDual_evaluation_apply` and
`ModuleCat.leftExactPairingDual_coevaluation_hom`). These are the componentwise pairings of graded
duals such as `TauCeti.VecTwisted.dual`.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module

namespace FGModuleCat

universe u

variable (K : Type u) [Field K]

/-- The left exact pairing of a vector space with its algebraic dual, transported from the
right exact pairing of the dual along the double-dual evaluation isomorphism. -/
@[instance_reducible]
def leftExactPairing (V : FGModuleCat.{u} K) : ExactPairing (dual K V) V := by
  letI : ExactPairing (dual K V) (dual K (dual K V)) :=
    FGModuleCat.exactPairing K (dual K V)
  exact exactPairingCongrRight (dualEvalIso V).symm

/-- The left dual of a finite-dimensional vector space is its algebraic dual. -/
instance leftDual (V : FGModuleCat.{u} K) : HasLeftDual V where
  leftDual := dual K V
  exact := leftExactPairing K V

/-- Finite-dimensional vector spaces have canonical left duals. -/
instance leftRigidCategory : LeftRigidCategory (FGModuleCat.{u} K) where

/-- Finite-dimensional vector spaces form a rigid category, with algebraic duals on both sides. -/
instance rigidCategory : RigidCategory (FGModuleCat.{u} K) where

variable {K}

/-- The chosen left dual is the algebraic dual used for the right dual. -/
@[simp]
theorem leftDual_eq (V : FGModuleCat.{u} K) : (ᘁV : FGModuleCat K) = dual K V :=
  (rfl)

/-- Right evaluation is the contraction of a linear functional with a vector. -/
@[simp]
theorem evaluation_hom_hom (V : FGModuleCat.{u} K) :
    (ε_ V Vᘁ).hom.hom = contractLeft K V :=
  (rfl)

/-- Right coevaluation is the coevaluation of linear algebra. -/
@[simp]
theorem coevaluation_hom_hom (V : FGModuleCat.{u} K) :
    (η_ V Vᘁ).hom.hom = coevaluation K V :=
  (rfl)

/-- Left evaluation is ordinary evaluation of a linear functional. -/
@[simp]
theorem leftEvaluation_apply (V : FGModuleCat.{u} K) (x : V) (f : Module.Dual K V) :
    (ε_ (ᘁV) V).hom.hom (A := V.obj ⊗ (ᘁV).obj) (B := 𝟙_ (ModuleCat K))
      (x ⊗ₜ[K] f) = f x := by
  -- Reduce the chosen dual in the dependent tensor-product types before simplifying maps.
  dsimp +instances [FGModuleCatDual, ExactPairing.evaluation, HasLeftDual.exact,
    HasLeftDual.leftDual, leftDual, leftExactPairing, exactPairingCongrRight,
    FGModuleCat.exactPairing, FGModuleCatEvaluation]
  simp only [ModuleCat.hom_whiskerRight, obj_carrier, dualEvalIso_inv, evalEquiv_toLinearMap]
  exact contractLeft_apply (Module.Dual.eval K V x) f

/-- Left coevaluation is coevaluation of the dual, with its double-dual factor identified
with the original space by inverse evaluation. -/
@[simp]
theorem leftCoevaluation_hom (V : FGModuleCat.{u} K) :
    (η_ (ᘁV) V).hom.hom =
      (Module.evalEquiv K V).symm.toLinearMap.lTensor (Module.Dual K V) ∘ₗ
        coevaluation K (Module.Dual K V) := by
  dsimp +instances [FGModuleCatDual, ExactPairing.coevaluation, HasLeftDual.exact,
    HasLeftDual.leftDual, leftDual, leftExactPairing, exactPairingCongrRight,
    FGModuleCat.exactPairing, FGModuleCatCoevaluation]
  simp only [ModuleCat.hom_whiskerLeft, obj_carrier, dualEvalIso_hom]
  rfl

/-- A left adjoint mate evaluates a functional by precomposition with the original map. -/
@[simp]
theorem leftAdjointMate_hom {V W : FGModuleCat.{u} K} (f : V ⟶ W) :
    (ᘁf).hom.hom = f.hom.hom.dualMap := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have h := congrArg
    (fun g : V ⊗ (ᘁW) ⟶ 𝟙_ (FGModuleCat K) => g.hom.hom (x ⊗ₜ[K] φ))
    (leftAdjointMate_comp_evaluation f)
  simp only [hom_hom_comp, LinearMap.comp_apply] at h
  -- The tensor maps have definitionally equal carriers hidden by the chosen-dual wrappers.
  erw [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul] at h
  erw [leftEvaluation_apply, leftEvaluation_apply] at h
  exact h

end FGModuleCat

namespace ModuleCat

universe u

variable {K : Type u} [Field K]

/-- A finite-dimensional vector space is exactly paired with its dual space in `ModuleCat K`:
the image of the pairing `FGModuleCat.exactPairing` under the inclusion of `FGModuleCat K`. -/
@[instance_reducible]
def exactPairingDual (V : ModuleCat.{u} K) [Module.Finite K V] :
    ExactPairing V (ModuleCat.of K (Module.Dual K V)) :=
  (ModuleCat.isFG K).ι.mapExactPairing (FGModuleCat.of K V) (FGModuleCat.of K V)ᘁ

/-- The dual space of a finite-dimensional vector space is exactly paired with the space in
`ModuleCat K`: the image of `FGModuleCat.leftExactPairing` under the inclusion of
`FGModuleCat K`. -/
@[instance_reducible]
def leftExactPairingDual (V : ModuleCat.{u} K) [Module.Finite K V] :
    ExactPairing (ModuleCat.of K (Module.Dual K V)) V :=
  (ModuleCat.isFG K).ι.mapExactPairing (ᘁ(FGModuleCat.of K V)) (FGModuleCat.of K V)

/-- The evaluation of `ModuleCat.exactPairingDual` is the contraction of a linear functional with
a vector. -/
@[simp]
theorem exactPairingDual_evaluation_apply (V : ModuleCat.{u} K) [Module.Finite K V]
    (f : Module.Dual K V) (v : V) :
    (@ExactPairing.evaluation _ _ _ V (ModuleCat.of K (Module.Dual K V))
      (exactPairingDual V)).hom (A := ModuleCat.of K (Module.Dual K V) ⊗ V) (f ⊗ₜ v) = f v := by
  -- `exactPairingDual V` is by definition the image of the pairing of `FGModuleCat.of K V` with
  -- its dual.
  refine (congrArg (fun φ ↦ φ.hom (f ⊗ₜ v))
    (ObjectProperty.ι_mapExactPairing_evaluation (FGModuleCat.of K V)
      (FGModuleCat.of K V)ᘁ)).trans ?_
  rw [FGModuleCat.evaluation_hom_hom]
  exact contractLeft_apply f v

/-- The coevaluation of `ModuleCat.exactPairingDual` is the coevaluation of linear algebra. -/
@[simp]
theorem exactPairingDual_coevaluation_hom (V : ModuleCat.{u} K) [Module.Finite K V] :
    (@ExactPairing.coevaluation _ _ _ V (ModuleCat.of K (Module.Dual K V))
      (exactPairingDual V)).hom = coevaluation K V :=
  (congrArg (fun φ ↦ φ.hom) (ObjectProperty.ι_mapExactPairing_coevaluation
    (FGModuleCat.of K V) (FGModuleCat.of K V)ᘁ)).trans
    (FGModuleCat.coevaluation_hom_hom (FGModuleCat.of K V))

/-- The evaluation of `ModuleCat.leftExactPairingDual` is ordinary evaluation of a linear
functional. -/
@[simp]
theorem leftExactPairingDual_evaluation_apply (V : ModuleCat.{u} K) [Module.Finite K V]
    (v : V) (f : Module.Dual K V) :
    (@ExactPairing.evaluation _ _ _ (ModuleCat.of K (Module.Dual K V)) V
      (leftExactPairingDual V)).hom (A := V ⊗ ModuleCat.of K (Module.Dual K V)) (v ⊗ₜ f) =
      f v := by
  -- `leftExactPairingDual V` is by definition the image of the pairing of the dual of
  -- `FGModuleCat.of K V` with `FGModuleCat.of K V`.
  exact (congrArg (fun φ ↦ φ.hom (v ⊗ₜ f))
    (ObjectProperty.ι_mapExactPairing_evaluation (ᘁ(FGModuleCat.of K V))
      (FGModuleCat.of K V))).trans
    (FGModuleCat.leftEvaluation_apply (FGModuleCat.of K V) v f)

/-- The coevaluation of `ModuleCat.leftExactPairingDual` is coevaluation of the dual, with its
double-dual factor identified with the original space by inverse evaluation. -/
@[simp]
theorem leftExactPairingDual_coevaluation_hom (V : ModuleCat.{u} K) [Module.Finite K V] :
    (@ExactPairing.coevaluation _ _ _ (ModuleCat.of K (Module.Dual K V)) V
      (leftExactPairingDual V)).hom =
      (Module.evalEquiv K V).symm.toLinearMap.lTensor (Module.Dual K V) ∘ₗ
        coevaluation K (Module.Dual K V) :=
  (congrArg (fun φ ↦ φ.hom) (ObjectProperty.ι_mapExactPairing_coevaluation
    (ᘁ(FGModuleCat.of K V)) (FGModuleCat.of K V))).trans
    (FGModuleCat.leftCoevaluation_hom (FGModuleCat.of K V))

end ModuleCat
