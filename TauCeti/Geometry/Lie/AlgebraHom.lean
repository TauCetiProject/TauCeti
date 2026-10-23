/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Units.Basic
public import TauCeti.Geometry.Lie.AutomaticSmoothness
public import TauCeti.Geometry.Lie.Functor

/-!
# The Lie map of an algebra homomorphism on units

A homomorphism between finite-dimensional normed real algebras induces a smooth homomorphism
between their groups of units. In the canonical algebra coordinates on the two Lie algebras,
its differential is the original algebra homomorphism. This lets actions of associative algebras
be compared with the differentiated actions of their unit groups and embedded Lie subgroups.

The coordinate calculation uses naturality of the exponential and uniqueness of its generator,
as developed in `TauCeti.eq_of_forall_exp_smul_eq`.
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

namespace AlgHom

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [NormedRing B] [NormedAlgebra ℝ B] [FiniteDimensional ℝ B]

local instance : CompleteSpace A := FiniteDimensional.complete ℝ A
local instance : CompleteSpace B := FiniteDimensional.complete ℝ B

attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The smooth homomorphism on unit groups induced by a finite-dimensional real algebra
homomorphism. -/
def unitsSmoothHom (f : A →ₐ[ℝ] B) :
    ContMDiffMonoidMorphism 𝓘(ℝ, A) 𝓘(ℝ, B) ∞ Aˣ Bˣ := by
  let h : Aˣ →ₜ* Bˣ :=
    ⟨Units.map f.toMonoidHom,
      f.toLinearMap.continuous_of_finiteDimensional.units_map f.toMonoidHom⟩
  exact h.toContMDiffMonoidMorphism _ _

/-- The smooth unit-group homomorphism is the usual map on units. -/
@[simp]
theorem unitsSmoothHom_apply (f : A →ₐ[ℝ] B) (a : Aˣ) :
    f.unitsSmoothHom a = Units.map f.toMonoidHom a := by
  simp only [unitsSmoothHom, ContinuousMonoidHom.coe_toContMDiffMonoidMorphism]
  rfl

/-- In the canonical algebra coordinates, the differential of the induced homomorphism on
units is the algebra homomorphism itself. -/
@[simp↓ high]
theorem unitsLieAlgebraLieEquiv_lieMap_unitsSmoothHom (f : A →ₐ[ℝ] B)
    (X : LeftInvariantDerivation 𝓘(ℝ, A) Aˣ) :
    TauCeti.Lie.unitsLieAlgebraLieEquiv (lieMap f.unitsSmoothHom X) =
      f (TauCeti.Lie.unitsLieAlgebraLieEquiv X) := by
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_apply,
    TauCeti.Lie.unitsLieAlgebraLieEquiv_apply]
  apply TauCeti.eq_of_forall_exp_smul_eq
  intro t
  have h := congrArg Units.val (map_lieExp f.unitsSmoothHom (t • X))
  have h' : NormedSpace.exp (t • unitsLieAlgebraEquiv (lieMap f.unitsSmoothHom X)) =
      NormedSpace.exp (f (t • unitsLieAlgebraEquiv X)) := by
    simpa [NormedSpace.map_exp f f.toLinearMap.continuous_of_finiteDimensional] using h.symm
  simpa only [map_smul] using h'

end AlgHom
