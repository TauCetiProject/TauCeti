/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Hecke.ChangeModulus
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# Riemann hypotheses in half-plane form over number fields

The extended Riemann hypothesis for Dedekind zeta and the generalized Riemann hypothesis for a
ray class character assert the absence of positive meromorphic orders to the right of the critical
line. They ignore the choice of a value at a pole and reject the identically zero function
(the fallback in `meromorphicContinuation` when no continuation exists). The hypothesis for a
character is independent of its presentation, and for the trivial character it is the hypothesis
for Dedekind zeta. Over `ℚ`, the latter is Mathlib's `RiemannHypothesis`.
-/

public section

open scoped NumberField
open TauCeti TauCeti.LFunctions

namespace NumberField

/-- The extended Riemann hypothesis for `K`: its continued Dedekind zeta function has no zeros
in `Re s > 1 / 2`, where zeros are points of positive meromorphic order. -/
def ExtendedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ZeroFreeRightOf (1 / 2) (dedekindZetaC K)

/-- The zero-free half-plane characterization of the extended Riemann hypothesis. -/
theorem extendedRiemannHypothesis_iff (K : Type*) [Field K] [NumberField K] :
    ExtendedRiemannHypothesis K ↔ ZeroFreeRightOf (1 / 2) (dedekindZetaC K) := (Iff.rfl)

end NumberField

namespace TauCeti.LFunctions

/-- Over `ℚ` the two zeta functions have the same zero-free right half-planes, even though their
values at the pole need not agree. -/
@[simp] theorem zeroFreeRightOf_dedekindZetaC_rat_iff {σ : ℝ} :
    ZeroFreeRightOf σ (dedekindZetaC ℚ) ↔ ZeroFreeRightOf σ riemannZeta :=
  zeroFreeRightOf_congr fun s _ ↦ dedekindZetaC_rat_eventuallyEq_riemannZeta s

end TauCeti.LFunctions

namespace NumberField

/-- The extended Riemann hypothesis for the rational field is the Riemann hypothesis. -/
@[simp] theorem extendedRiemannHypothesis_rat_iff :
    ExtendedRiemannHypothesis ℚ ↔ RiemannHypothesis := by
  rw [extendedRiemannHypothesis_iff, zeroFreeRightOf_dedekindZetaC_rat_iff,
    ← riemannHypothesis_iff_zeroFreeRightOf]

end NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- The generalized Riemann hypothesis for a ray class character: its continued L-function has
no zeros in `Re s > 1 / 2`, where zeros are points of positive meromorphic order. -/
def GeneralizedRiemannHypothesis (χ : RayClassCharacter 𝔪) : Prop :=
  ZeroFreeRightOf (1 / 2) (heckeLFunctionC χ)

/-- The zero-free half-plane characterization of the hypothesis for a ray class character. -/
theorem generalizedRiemannHypothesis_iff (χ : RayClassCharacter 𝔪) :
    χ.GeneralizedRiemannHypothesis ↔ ZeroFreeRightOf (1 / 2) (heckeLFunctionC χ) := (Iff.rfl)

/-- Inducing a ray class character to a multiple of its modulus preserves its generalized
Riemann hypothesis. -/
@[simp] theorem generalizedRiemannHypothesis_induced_iff (χ : RayClassCharacter 𝔪)
    (h : 𝔪 ∣ 𝔫) :
    (χ.induced h).GeneralizedRiemannHypothesis ↔ χ.GeneralizedRiemannHypothesis := by
  simp only [generalizedRiemannHypothesis_iff,
    χ.zeroFreeRightOf_heckeLFunctionC_induced h (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- A ray class character satisfies its generalized Riemann hypothesis exactly when its primitive
source does. -/
theorem generalizedRiemannHypothesis_primitive_iff (χ : RayClassCharacter 𝔪) :
    χ.GeneralizedRiemannHypothesis ↔
      (PrimitiveRayClassCharacter.of χ).character.GeneralizedRiemannHypothesis := by
  simp only [generalizedRiemannHypothesis_iff,
    χ.zeroFreeRightOf_heckeLFunctionC_primitive (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The generalized Riemann hypothesis for a trivial ray class character, at any modulus, is the
extended Riemann hypothesis of the base field. -/
@[simp] theorem generalizedRiemannHypothesis_one_iff :
    (1 : RayClassCharacter 𝔪).GeneralizedRiemannHypothesis ↔
      NumberField.ExtendedRiemannHypothesis K := by
  simp only [generalizedRiemannHypothesis_iff, NumberField.extendedRiemannHypothesis_iff,
    zeroFreeRightOf_heckeLFunctionC_one (𝔪 := 𝔪) (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end TauCeti.GlobalNumberFields.RayClassCharacter
