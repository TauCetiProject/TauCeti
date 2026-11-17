/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.Units.Compatibility
public import TauCeti.Geometry.Lie.Functor

/-!
# Differentiating smooth homomorphisms into units along exponential rays

For a smooth homomorphism `φ : G → Aˣ` from a finite-dimensional real Lie group into the group of
units of a finite-dimensional real normed algebra `A`, the Lie-group exponential is natural
(`map_lieExp`) and on `Aˣ` agrees with the Banach-algebra exponential (`lieExp_eq_expUnit`).
Consequently, differentiating the exponential ray `s ↦ (φ (lieExp (s • Z)) : A)` at `0` recovers
`unitsLieAlgebraEquiv (lieMap φ Z)` via `TauCeti.hasDerivAt_expUnitHom_val_zero`. This uniquely
determines the Lie differential of any smooth representation into `Aˣ` from its initial velocity
along one-parameter subgroups, without depending on algebra-homomorphism or adjoint theory.

## Main results

* `ContMDiffMonoidMorphism.hasDerivAt_lieExp_smul_val_zero`: the exponential ray
  `s ↦ (φ (lieExp (s • Z)) : A)` has derivative `unitsLieAlgebraEquiv (lieMap φ Z)` at `0`.
* `ContMDiffMonoidMorphism.unitsLieAlgebraEquiv_lieMap_eq_of_hasDerivAt`: uniqueness of
  `unitsLieAlgebraEquiv (lieMap φ Z)` from the derivative of `s ↦ (φ (lieExp (s • Z)) : A)` at `0`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Theorem 3.28, for characterizing the differential of a Lie-group homomorphism into a matrix/unit
  group as the velocity at `t = 0` along exponential curves.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace ContMDiffMonoidMorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

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

end ContMDiffMonoidMorphism
