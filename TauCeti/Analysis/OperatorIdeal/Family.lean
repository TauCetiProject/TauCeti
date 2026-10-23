/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Families of operator ideals

An operator-ideal family assigns an extended nonnegative gauge to every bounded operator between
Hilbert spaces. The gauge is subadditive, absolutely homogeneous, dominates the operator norm, and
satisfies the two-sided ideal inequality. Its finite locus therefore selects a rectangular operator
ideal, while the extended value `∞` allows one family to describe both members and nonmembers.

A symmetric operator-ideal family additionally identifies the gauges of an operator and its
adjoint. This requires source and target to live in the same universe, since taking adjoints swaps
them.

This file provides the common algebraic API of these families: zero and negation laws,
definiteness, finite-sum subadditivity, one-sided ideal inequalities, contraction bounds, and
extensionality. Concrete trace-class, Hilbert--Schmidt, Ky Fan, and Schatten families can use these
results without repeating their ideal calculus.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open scoped ENNReal

universe u v w

namespace TauCeti

/-- A rectangular family of extended nonnegative operator gauges on Hilbert spaces.

The four fields are subadditivity, absolute homogeneity, domination of the operator norm, and the
two-sided ideal inequality. The family is universe-polymorphic in the source and target spaces, so
one object supplies a gauge on every Hilbert-space pair in the chosen universes. -/
structure OperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  /-- The extended nonnegative gauge on bounded operators between a Hilbert-space pair. -/
  gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ≥0∞
  /-- The gauge is subadditive. -/
  gauge_add_le : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A B : E →L[𝕜] F), gauge (A + B) ≤ gauge A + gauge B
  /-- The gauge is absolutely homogeneous. -/
  gauge_smul : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) (A : E →L[𝕜] F), gauge (c • A) = ‖c‖ₑ * gauge A
  /-- The gauge dominates the extended operator norm. -/
  enorm_le_gauge : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), ‖A‖ₑ ≤ gauge A
  /-- The gauge satisfies the two-sided ideal inequality. -/
  gauge_comp_le : ∀ {E H : Type v} {F G : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E),
      gauge (L ∘L A ∘L R) ≤ ‖L‖ₑ * gauge A * ‖R‖ₑ

attribute [simp] OperatorIdealFamily.gauge_smul

/-- A symmetric operator-ideal family is an operator-ideal family whose diagonal-universe gauge
is invariant under adjoints. -/
structure SymmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜]
    extends OperatorIdealFamily.{u, v, v} 𝕜 where
  /-- Taking the adjoint preserves the gauge. -/
  gauge_adjoint : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), gauge (ContinuousLinearMap.adjoint A) = gauge A

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable (Φ : OperatorIdealFamily.{u, v, w} 𝕜)
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Two operator-ideal families are equal when all of their gauges agree. -/
@[ext]
theorem ext {Φ Ψ : OperatorIdealFamily.{u, v, w} 𝕜}
    (h : ∀ {E : Type v} {F : Type w}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), Φ.gauge A = Ψ.gauge A) : Φ = Ψ := by
  cases Φ
  cases Ψ
  congr
  funext E F _ _ _ _ _ _ A
  exact h A

/-- Every operator-ideal gauge vanishes at the zero operator. -/
@[simp]
theorem gauge_zero : Φ.gauge (0 : E →L[𝕜] F) = 0 := by
  simpa using Φ.gauge_smul (0 : 𝕜) (0 : E →L[𝕜] F)

/-- An operator-ideal gauge vanishes exactly at the zero operator. -/
@[simp]
theorem gauge_eq_zero_iff (A : E →L[𝕜] F) : Φ.gauge A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ Φ.gauge_zero⟩
  have hzero : ‖A‖ₑ = 0 := le_antisymm (h ▸ Φ.enorm_le_gauge A) bot_le
  exact (ENormedAddMonoid.enorm_eq_zero A).mp hzero

/-- Negating an operator does not change its operator-ideal gauge. -/
@[simp]
theorem gauge_neg (A : E →L[𝕜] F) : Φ.gauge (-A) = Φ.gauge A := by
  simpa using Φ.gauge_smul (-1 : 𝕜) A

/-- The gauge of a finite sum is at most the sum of the gauges. -/
theorem gauge_sum_le {ι : Type*} (s : Finset ι) (A : ι → E →L[𝕜] F) :
    Φ.gauge (∑ i ∈ s, A i) ≤ ∑ i ∈ s, Φ.gauge (A i) := by
  simpa only [Finset.sum_filter] using
    Finset.le_sum_of_subadditive Φ.gauge Φ.gauge_zero.le Φ.gauge_add_le s (fun i ↦ A i)

/-- Composition on the left satisfies the one-sided ideal inequality. -/
theorem gauge_comp_left_le {G : Type w}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) :
    Φ.gauge (L ∘L A) ≤ ‖L‖ₑ * Φ.gauge A := by
  calc
    Φ.gauge (L ∘L A) ≤ ‖L‖ₑ * Φ.gauge A * ‖ContinuousLinearMap.id 𝕜 E‖ₑ := by
      simpa using Φ.gauge_comp_le L A (ContinuousLinearMap.id 𝕜 E)
    _ ≤ ‖L‖ₑ * Φ.gauge A := mul_le_of_le_one_right' <| by
      rw [enorm_eq_nnnorm]
      exact_mod_cast ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)

/-- Composition on the right satisfies the one-sided ideal inequality. -/
theorem gauge_comp_right_le {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    Φ.gauge (A ∘L R) ≤ Φ.gauge A * ‖R‖ₑ := by
  calc
    Φ.gauge (A ∘L R) ≤ ‖ContinuousLinearMap.id 𝕜 F‖ₑ * Φ.gauge A * ‖R‖ₑ := by
      simpa using Φ.gauge_comp_le (ContinuousLinearMap.id 𝕜 F) A R
    _ ≤ Φ.gauge A * ‖R‖ₑ := by
      have hid : ‖ContinuousLinearMap.id 𝕜 F‖ₑ ≤ 1 := by
        rw [enorm_eq_nnnorm]
        exact_mod_cast ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F)
      have hmul : ‖ContinuousLinearMap.id 𝕜 F‖ₑ * Φ.gauge A ≤ Φ.gauge A :=
        mul_le_of_le_one_left' hid
      simpa only [mul_comm, mul_left_comm] using mul_le_mul_right hmul ‖R‖ₑ

/-- Left composition by a contraction does not increase an operator-ideal gauge. -/
theorem gauge_comp_left_le_self {G : Type w}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    {L : F →L[𝕜] G} (hL : ‖L‖ ≤ 1) (A : E →L[𝕜] F) :
    Φ.gauge (L ∘L A) ≤ Φ.gauge A := by
  refine (Φ.gauge_comp_left_le L A).trans ?_
  rw [enorm_eq_nnnorm]
  exact mul_le_of_le_one_left' (by exact_mod_cast hL)

/-- Right composition by a contraction does not increase an operator-ideal gauge. -/
theorem gauge_comp_right_le_self {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (A : E →L[𝕜] F) {R : H →L[𝕜] E} (hR : ‖R‖ ≤ 1) :
    Φ.gauge (A ∘L R) ≤ Φ.gauge A := by
  refine (Φ.gauge_comp_right_le A R).trans ?_
  rw [enorm_eq_nnnorm]
  exact mul_le_of_le_one_right' (by exact_mod_cast hR)

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Two symmetric operator-ideal families are equal when all of their gauges agree. -/
@[ext]
theorem ext {Φ Ψ : SymmetricOperatorIdealFamily.{u, v} 𝕜}
    (h : ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : E →L[𝕜] F), Φ.gauge A = Ψ.gauge A) : Φ = Ψ := by
  cases Φ with
  | mk Φ hΦ =>
    cases Ψ with
    | mk Ψ hΨ =>
      have hbase : Φ = Ψ := OperatorIdealFamily.ext h
      subst Ψ
      rfl

end SymmetricOperatorIdealFamily

attribute [simp] SymmetricOperatorIdealFamily.gauge_adjoint

end TauCeti
