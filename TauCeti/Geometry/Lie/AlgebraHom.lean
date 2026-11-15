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
as developed in `TauCeti.eq_of_forall_exp_smul_eq`. More generally, any smooth group homomorphism
into a complete normed real algebra `A` lifts via `ContMDiffMonoidMorphism.toUnitsSmoothHom` to a
smooth homomorphism into `Aˣ`, whose Lie differential in canonical algebra coordinates is uniquely
determined by the initial velocity along exponential rays
(`ContMDiffMonoidMorphism.hasDerivAt_lieExp_smul_val_zero`,
`ContMDiffMonoidMorphism.unitsLieAlgebraEquiv_lieMap_eq_of_hasDerivAt`).
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

namespace AlgHom

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  [NormedRing B] [NormedAlgebra ℝ B] [FiniteDimensional ℝ B]

local instance : CompleteSpace A := FiniteDimensional.completeSpace ℝ A
local instance : CompleteSpace B := FiniteDimensional.completeSpace ℝ B

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

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

section CompleteSpace

variable [CompleteSpace A]

/-- Any smooth monoid homomorphism from a group `G` into a complete normed real algebra `A` lifts
to a smooth homomorphism into the Lie group of units `Aˣ`. -/
def toUnitsSmoothHom (f : ContMDiffMonoidMorphism I 𝓘(ℝ, A) ∞ G A) :
    ContMDiffMonoidMorphism I 𝓘(ℝ, A) ∞ G Aˣ where
  toMonoidHom := f.toMonoidHom.toHomUnits
  contMDiff_toFun :=
    ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val f.contMDiff_toFun

/-- Coercing `f.toUnitsSmoothHom g` back to `A` recovers `f g`. -/
@[simp]
theorem coe_toUnitsSmoothHom_apply (f : ContMDiffMonoidMorphism I 𝓘(ℝ, A) ∞ G A) (g : G) :
    ((f.toUnitsSmoothHom g : Aˣ) : A) = f g :=
  (rfl)

end CompleteSpace

section LieGroup

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [FiniteDimensional ℝ A]

local instance : CompleteSpace A := FiniteDimensional.completeSpace ℝ A
attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Along a Lie-algebra ray `s ↦ exp(s • Z)`, a smooth homomorphism into `Aˣ` has initial velocity
`unitsLieAlgebraEquiv (lieMap φ Z)` in the ambient normed algebra `A`. -/
theorem hasDerivAt_lieExp_smul_val_zero
    (φ : ContMDiffMonoidMorphism I 𝓘(ℝ, A) ∞ G Aˣ) (Z : LeftInvariantDerivation I G) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    HasDerivAt (fun s : ℝ ↦ (φ (lieExp (s • Z)) : A))
      (unitsLieAlgebraEquiv (lieMap φ Z)) 0 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  have hfun : (fun s : ℝ ↦ (φ (lieExp (s • Z)) : A)) =
      fun s : ℝ ↦
        (TauCeti.expUnitHom (unitsLieAlgebraEquiv (lieMap φ Z)) (Multiplicative.ofAdd s) : A) := by
    funext s
    rw [map_lieExp φ (s • Z), map_smul (lieMap φ) s Z, lieExp_eq_expUnit,
      unitsLieAlgebraEquiv.map_smul, TauCeti.expUnitHom_apply]
  rw [hfun]
  exact TauCeti.hasDerivAt_expUnitHom_val_zero (unitsLieAlgebraEquiv (lieMap φ Z))

/-- Uniqueness of the Lie differential of a smooth representation into `Aˣ` from the initial
velocity of its exponential curve at `0`. -/
theorem unitsLieAlgebraEquiv_lieMap_eq_of_hasDerivAt
    (φ : ContMDiffMonoidMorphism I 𝓘(ℝ, A) ∞ G Aˣ) (Z : LeftInvariantDerivation I G)
    {a : A}
    (h : let _ : T2Space G := I.t2Space_of_lieGroup ∞
      HasDerivAt (fun s : ℝ ↦ (φ (lieExp (s • Z)) : A)) a 0) :
    unitsLieAlgebraEquiv (lieMap φ Z) = a := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  exact (φ.hasDerivAt_lieExp_smul_val_zero Z).unique h

end LieGroup

end ContMDiffMonoidMorphism
