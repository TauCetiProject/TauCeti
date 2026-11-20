/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import TauCeti.Analysis.Normed.Algebra.Character.Unitization

import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import TauCeti.Analysis.Normed.Algebra.Character.Pullback
import TauCeti.Topology.ContinuousMap.Ideals

/-!
# Character space of `C₀(Y, 𝕜)`

For a compact Hausdorff space `X` and `RCLike 𝕜`, Mathlib's `WeakDual.CharacterSpace.homeoEval`
identifies `X` with `characterSpace 𝕜 C(X, 𝕜)` by point evaluation.

This file extends point-evaluation duality to weakly locally compact Hausdorff spaces `Y` by
combining `WeakDual.CharacterSpace.homeoEval` on `OnePoint Y`, Mathlib's unitization equivalence
`ZeroAtInftyContinuousMap.unitizationAlgEquiv : Unitization 𝕜 C₀(Y, 𝕜) ≃ₐ[𝕜] C(OnePoint Y, 𝕜)`,
and the unitization character-space homeomorphisms from
`TauCeti.Analysis.Normed.Algebra.Character.Unitization`:

* `WeakDual.CharacterSpace.unitizationZeroAtInftyHomeoEval`: point evaluation identifies
  `OnePoint Y` with `characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜))`, sending `∞` to
  `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` and `(y : Y)` to `u ↦ u.fst + u.snd y`;
* `WeakDual.CharacterSpace.zeroAtInftyHomeoEval`: restricting to finite points gives the
  nonunital evaluation homeomorphism `Y ≃ₜ characterSpace 𝕜 C₀(Y, 𝕜)`, `y ↦ (f ↦ f y)`;
* `WeakDual.CharacterSpace.onePointCongr_zeroAtInftyHomeoEval_trans_onePointHomeomorphUnitization`:
  extending `zeroAtInftyHomeoEval Y 𝕜` to `OnePoint Y` and composing with
  `onePointHomeomorphUnitization 𝕜 C₀(Y, 𝕜)` recovers `unitizationZeroAtInftyHomeoEval Y 𝕜`.

## References

* J. B. Conway, *A Course in Functional Analysis*, §VIII.2.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §2.1.
-/

public section

open OnePoint WeakDual
open scoped ZeroAtInfty

namespace WeakDual.CharacterSpace

section ZeroAtInftyEval

variable (Y 𝕜 : Type*) [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y] [RCLike 𝕜]

/-- Point evaluation identifies `OnePoint Y` with the character space of
`Unitization 𝕜 C₀(Y, 𝕜)`, sending `∞` to `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` and `(y : Y)` to
`u ↦ u.fst + u.snd y`. -/
noncomputable def unitizationZeroAtInftyHomeoEval :
    OnePoint Y ≃ₜ characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜)) :=
  (homeoEval (OnePoint Y) 𝕜).trans
    (AlgEquiv.characterSpaceHomeomorph (A := Unitization 𝕜 C₀(Y, 𝕜)) (B := C(OnePoint Y, 𝕜))
      (ZeroAtInftyContinuousMap.unitizationAlgEquiv Y 𝕜 𝕜))

/-- `unitizationZeroAtInftyHomeoEval Y 𝕜` sends `∞` to `Unitization.augmentation 𝕜 C₀(Y, 𝕜)`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_apply_infty :
    unitizationZeroAtInftyHomeoEval Y 𝕜 ∞ = Unitization.augmentation 𝕜 C₀(Y, 𝕜) := by
  ext u
  simp [unitizationZeroAtInftyHomeoEval]

/-- `(unitizationZeroAtInftyHomeoEval Y 𝕜).symm` sends `Unitization.augmentation 𝕜 C₀(Y, 𝕜)` to `∞`.
-/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_symm_apply_augmentation :
    (unitizationZeroAtInftyHomeoEval Y 𝕜).symm (Unitization.augmentation 𝕜 C₀(Y, 𝕜)) = ∞ := by
  rw [Homeomorph.symm_apply_eq]
  exact (unitizationZeroAtInftyHomeoEval_apply_infty Y 𝕜).symm

/-- `unitizationZeroAtInftyHomeoEval Y 𝕜` evaluates `u` at a finite point `y : Y` as
`u.fst + u.snd y`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_apply_coe (y : Y) (u : Unitization 𝕜 C₀(Y, 𝕜)) :
    unitizationZeroAtInftyHomeoEval Y 𝕜 y u = u.fst + u.snd y := by
  simp [unitizationZeroAtInftyHomeoEval]

/-- Natural homeomorphism between a weakly locally compact Hausdorff space `Y` and
`characterSpace 𝕜 C₀(Y, 𝕜)` given by point evaluation `y ↦ (f ↦ f y)`. This is the nonunital
counterpart of `WeakDual.CharacterSpace.homeoEval`. -/
noncomputable def zeroAtInftyHomeoEval :
    Y ≃ₜ characterSpace 𝕜 C₀(Y, 𝕜) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph.trans <|
    ((unitizationZeroAtInftyHomeoEval Y 𝕜).subtype fun p ↦ by
      rw [← OnePoint.compl_infty, Set.mem_compl_singleton_iff,
        ← unitizationZeroAtInftyHomeoEval_apply_infty Y 𝕜]
      exact (unitizationZeroAtInftyHomeoEval Y 𝕜).injective.ne_iff.symm).trans
      (unitizationComplAugmentationHomeomorph 𝕜 C₀(Y, 𝕜)).symm

/-- `zeroAtInftyHomeoEval Y 𝕜 y` evaluates `f : C₀(Y, 𝕜)` at `y`. -/
@[simp]
theorem zeroAtInftyHomeoEval_apply (y : Y) (f : C₀(Y, 𝕜)) :
    zeroAtInftyHomeoEval Y 𝕜 y f = f y := by
  simp [zeroAtInftyHomeoEval]

/-- On finite points `y : Y`, `unitizationZeroAtInftyHomeoEval Y 𝕜 y` is the unital extension of
`zeroAtInftyHomeoEval Y 𝕜 y`. -/
theorem unitizationZeroAtInftyHomeoEval_coe_eq_unitizationExtend (y : Y) :
    unitizationZeroAtInftyHomeoEval Y 𝕜 y =
      (unitizationExtend (zeroAtInftyHomeoEval Y 𝕜 y)).val := by
  ext u
  simp

/-- On a punctured character `φ` of `Unitization 𝕜 C₀(Y, 𝕜)`,
`(unitizationZeroAtInftyHomeoEval Y 𝕜).symm φ.1` equals
`(zeroAtInftyHomeoEval Y 𝕜).symm (unitizationRestrict φ)`. -/
@[simp]
theorem unitizationZeroAtInftyHomeoEval_symm_apply_coe
    (φ : {φ : characterSpace 𝕜 (Unitization 𝕜 C₀(Y, 𝕜)) //
      φ ≠ Unitization.augmentation 𝕜 C₀(Y, 𝕜)}) :
    (unitizationZeroAtInftyHomeoEval Y 𝕜).symm φ.val =
      ((zeroAtInftyHomeoEval Y 𝕜).symm (unitizationRestrict φ) : OnePoint Y) := by
  rw [Homeomorph.symm_apply_eq, unitizationZeroAtInftyHomeoEval_coe_eq_unitizationExtend,
    Homeomorph.apply_symm_apply, unitizationExtend_unitizationRestrict]

/-- Extending `zeroAtInftyHomeoEval Y 𝕜` to `OnePoint Y` and composing with
`onePointHomeomorphUnitization 𝕜 C₀(Y, 𝕜)` recovers `unitizationZeroAtInftyHomeoEval Y 𝕜`. -/
theorem onePointCongr_zeroAtInftyHomeoEval_trans_onePointHomeomorphUnitization :
    (zeroAtInftyHomeoEval Y 𝕜).onePointCongr.trans
        (onePointHomeomorphUnitization 𝕜 C₀(Y, 𝕜)) =
      unitizationZeroAtInftyHomeoEval Y 𝕜 := by
  ext p u
  induction p using OnePoint.rec with
  | infty => simp
  | coe y => simp

end ZeroAtInftyEval

end WeakDual.CharacterSpace
