/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Dual

/-!
# Left duals of finite-dimensional vector spaces

The algebraic dual is both a left and a right dual in `FGModuleCat K`. Mathlib supplies the
right pairing. Here the left pairing is obtained from the right pairing of the dual space by
`CategoryTheory.exactPairingCongrRight`, using `FGModuleCat.dualEvalIso` for the classical
double-dual evaluation isomorphism. In particular this choice
does not use a braiding to construct the left dual. Its evaluation is the usual contraction,
and its adjoint mates are ordinary transposes.

The resulting `LeftRigidCategory` and `RigidCategory` instances also give rigidity of
categories of group actions through Mathlib's existing instances.
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

/-- Left evaluation is ordinary evaluation of a linear functional. -/
@[simp]
theorem leftEvaluation_apply (V : FGModuleCat.{u} K) (x : V) (f : Module.Dual K V) :
    (ε_ (ᘁV) V).hom.hom (x ⊗ₜ[K] f) = f x := by
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
