/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Equality of approximation-number sequences

Two continuous linear maps have the same approximation numbers when their
`ℝ≥0`-valued singular-value sequences agree at every index. The two maps may
act between different seminormed spaces, including spaces in different universes.
This relation is reflexive, symmetric, and transitive. Equal sequences also
have equal Ky Fan prefix gauges, so properties determined solely by approximation
numbers can be transported between these operators.

## Provenance

Adapted from `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/SameSequence.lean`
in [AIQ-Kitware/aiq-dkps-formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc., Apache-2.0), using TauCeti's nonnegative `singularValue` sequence.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G H I J : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  [SeminormedAddCommGroup I] [NormedSpace 𝕜 I]
  [SeminormedAddCommGroup J] [NormedSpace 𝕜 J]

/-- Equality of the zero-based approximation-number sequences of two maps,
possibly between different seminormed spaces. -/
def SameSingularValues (S : E →L[𝕜] F) (T : G →L[𝕜] H) : Prop :=
  ∀ n : ℕ, S.singularValue n = T.singularValue n

/-- Two maps have the same approximation-number sequence if and only if their
nonnegative singular values agree at every index. -/
theorem sameSingularValues_iff (S : E →L[𝕜] F) (T : G →L[𝕜] H) :
    SameSingularValues S T ↔ ∀ n : ℕ, S.singularValue n = T.singularValue n :=
  Iff.rfl

/-- Every bounded map has the same approximation numbers as itself. -/
@[simp] theorem sameSingularValues_refl (T : E →L[𝕜] F) : SameSingularValues T T :=
  fun _ => rfl

/-- Equality of approximation-number sequences is symmetric. -/
theorem sameSingularValues_symm {S : E →L[𝕜] F} {T : G →L[𝕜] H}
    (h : SameSingularValues S T) : SameSingularValues T S :=
  fun n => (h n).symm

/-- Equality of approximation-number sequences is transitive. -/
theorem sameSingularValues_trans {S : E →L[𝕜] F} {T : G →L[𝕜] H}
    {U : I →L[𝕜] J} (hST : SameSingularValues S T)
    (hTU : SameSingularValues T U) : SameSingularValues S U :=
  fun n => (hST n).trans (hTU n)

/-- Equality of approximation-number sequences implies equality of all Ky Fan gauges. -/
theorem SameSingularValues.kyFanGauge_eq {S : E →L[𝕜] F} {T : G →L[𝕜] H}
    (h : SameSingularValues S T) (k : ℕ) :
    S.kyFanGauge k = T.kyFanGauge k := by
  simp only [kyFanGauge_def]
  exact Finset.sum_congr rfl (fun n _ => h n)

end ContinuousLinearMap
