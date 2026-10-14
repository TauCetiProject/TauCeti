/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support

/-!
# Differential forms under an involution

This file splits a fixed-coefficient rough differential form into the parts invariant and
anti-invariant under pullback by a self-map.  When the self-map is a differentiable involution,
the two averaging operators are complementary projectors onto the `+1` and `-1` eigenspaces of
pullback.  Proper self-maps preserve compact topological support under both projectors.

These projectors give the descent decomposition used for differential forms on a two-sheeted
cover.  The construction is the usual averaging by a finite group action; see Bott and Tu,
*Differential Forms in Algebraic Topology*, Chapter I, Section 6.
-/

public section

noncomputable section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {E H X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℝ F] {k : ℕ}

/-- The part of a rough form fixed by pullback: `(φ + τ⁎φ) / 2`. -/
def invariantPart (τ : X → X) (φ : RoughForm I X F k) : RoughForm I X F k :=
  (2 : ℝ)⁻¹ • (φ + mpullback I I τ φ)

/-- The part of a rough form negated by pullback: `(φ - τ⁎φ) / 2`. -/
def antiInvariantPart (τ : X → X) (φ : RoughForm I X F k) : RoughForm I X F k :=
  (2 : ℝ)⁻¹ • (φ - mpullback I I τ φ)

/-- Evaluation of the invariant part at a point. -/
@[simp]
theorem invariantPart_apply (τ : X → X) (φ : RoughForm I X F k) (x : X) :
    invariantPart τ φ x =
      (2 : ℝ)⁻¹ • (φ x + (φ (τ x)).compContinuousLinearMap (mfderiv I I τ x)) := by
  ext v
  simp only [invariantPart, Pi.smul_apply, Pi.add_apply, mpullback_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2

/-- Evaluation of the anti-invariant part at a point. -/
@[simp]
theorem antiInvariantPart_apply (τ : X → X) (φ : RoughForm I X F k) (x : X) :
    antiInvariantPart τ φ x =
      (2 : ℝ)⁻¹ • (φ x - (φ (τ x)).compContinuousLinearMap (mfderiv I I τ x)) := by
  ext v
  simp only [antiInvariantPart, Pi.smul_apply, Pi.sub_apply, mpullback_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 2

/-- Every rough form is the sum of its invariant and anti-invariant parts. -/
theorem invariantPart_add_antiInvariantPart (τ : X → X) (φ : RoughForm I X F k) :
    invariantPart τ φ + antiInvariantPart τ φ = φ := by
  rw [invariantPart, antiInvariantPart]
  module

/-- The invariant part is the original form exactly when the form is fixed by pullback. -/
theorem invariantPart_eq_self_iff (τ : X → X) (φ : RoughForm I X F k) :
    invariantPart τ φ = φ ↔ mpullback I I τ φ = φ := by
  rw [invariantPart]
  constructor <;> intro h
  · linear_combination (norm := module) (2 : ℝ) • h
  · rw [h]
    module

/-- The anti-invariant part is the original form exactly when pullback negates the form. -/
theorem antiInvariantPart_eq_self_iff (τ : X → X) (φ : RoughForm I X F k) :
    antiInvariantPart τ φ = φ ↔ mpullback I I τ φ = -φ := by
  rw [antiInvariantPart]
  constructor <;> intro h
  · linear_combination (norm := module) (-2 : ℝ) • h
  · rw [h]
    module

/-- The invariant part vanishes exactly when pullback negates the form. -/
theorem invariantPart_eq_zero_iff (τ : X → X) (φ : RoughForm I X F k) :
    invariantPart τ φ = 0 ↔ mpullback I I τ φ = -φ := by
  rw [invariantPart]
  constructor <;> intro h
  · linear_combination (norm := module) (2 : ℝ) • h
  · rw [h]
    module

/-- The anti-invariant part vanishes exactly when the form is fixed by pullback. -/
theorem antiInvariantPart_eq_zero_iff (τ : X → X) (φ : RoughForm I X F k) :
    antiInvariantPart τ φ = 0 ↔ mpullback I I τ φ = φ := by
  rw [antiInvariantPart]
  constructor <;> intro h
  · linear_combination (norm := module) (-2 : ℝ) • h
  · rw [h]
    module

section Involution

variable {τ : X → X}

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
/-- Pulling a form back twice by a differentiable involution fixes it. -/
@[simp]
theorem mpullback_mpullback_of_involutive (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    mpullback I I τ (mpullback I I τ φ) = φ := by
  rw [← mpullback_comp hτd hτd]
  have hcomp : τ ∘ τ = id := funext hτ
  rw [hcomp, mpullback_id]

/-- Pullback fixes the invariant part of a form. -/
@[simp]
theorem mpullback_invariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    mpullback I I τ (invariantPart τ φ) = invariantPart τ φ := by
  rw [invariantPart, mpullback_smul, mpullback_add,
    mpullback_mpullback_of_involutive hτ hτd]
  module

/-- Pullback negates the anti-invariant part of a form. -/
@[simp]
theorem mpullback_antiInvariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    mpullback I I τ (antiInvariantPart τ φ) = -antiInvariantPart τ φ := by
  rw [antiInvariantPart, mpullback_smul]
  have hneg (ψ : RoughForm I X F k) : mpullback I I τ (-ψ) = -mpullback I I τ ψ := by
    rw [← neg_one_smul ℝ ψ, mpullback_smul, neg_one_smul]
  rw [sub_eq_add_neg, mpullback_add, hneg,
    mpullback_mpullback_of_involutive hτ hτd]
  module

/-- Taking the invariant part twice has no further effect. -/
@[simp]
theorem invariantPart_invariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    invariantPart τ (invariantPart τ φ) = invariantPart τ φ :=
  (invariantPart_eq_self_iff τ _).2 (mpullback_invariantPart hτ hτd φ)

/-- Taking the anti-invariant part twice has no further effect. -/
@[simp]
theorem antiInvariantPart_antiInvariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    antiInvariantPart τ (antiInvariantPart τ φ) = antiInvariantPart τ φ :=
  (antiInvariantPart_eq_self_iff τ _).2 (mpullback_antiInvariantPart hτ hτd φ)

/-- The anti-invariant part of an invariant form vanishes. -/
@[simp]
theorem antiInvariantPart_invariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    antiInvariantPart τ (invariantPart τ φ) = 0 :=
  (antiInvariantPart_eq_zero_iff τ _).2 (mpullback_invariantPart hτ hτd φ)

/-- The invariant part of an anti-invariant form vanishes. -/
@[simp]
theorem invariantPart_antiInvariantPart (hτ : Function.Involutive τ)
    (hτd : MDifferentiable I I τ) (φ : RoughForm I X F k) :
    invariantPart τ (antiInvariantPart τ φ) = 0 :=
  (invariantPart_eq_zero_iff τ _).2 (mpullback_antiInvariantPart hτ hτd φ)

end Involution

/-- The invariant part of a compactly supported form has compact support under a proper map. -/
theorem isCompact_tsupport_invariantPart {τ : X → X} (hτ : IsProperMap τ)
    {φ : RoughForm I X F k} (hφ : IsCompact φ.tsupport) :
    IsCompact (invariantPart τ φ).tsupport := by
  rw [invariantPart]
  exact (hφ.union (φ.isCompact_tsupport_mpullback hτ hφ)).of_isClosed_subset
    (RoughForm.isClosed_tsupport _)
    ((RoughForm.tsupport_smul_subset _ _).trans (RoughForm.tsupport_add_subset _ _))

/-- The anti-invariant part of a compactly supported form has compact support under a proper map. -/
theorem isCompact_tsupport_antiInvariantPart {τ : X → X} (hτ : IsProperMap τ)
    {φ : RoughForm I X F k} (hφ : IsCompact φ.tsupport) :
    IsCompact (antiInvariantPart τ φ).tsupport := by
  rw [antiInvariantPart]
  exact (hφ.union (φ.isCompact_tsupport_mpullback hτ hφ)).of_isClosed_subset
    (RoughForm.isClosed_tsupport _)
    ((RoughForm.tsupport_smul_subset _ _).trans (RoughForm.tsupport_sub_subset _ _))

end TauCeti
