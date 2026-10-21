/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The nuclear gauge of a bounded operator

The nuclear gauge is the sum of the approximation numbers, with values in `ℝ≥0∞`.
Its finite values select the trace-class operators on Hilbert spaces. The supremum of the
Ky Fan prefixes gives the gauge, so Ky Fan dominance and the triangle inequality pass to
this sum. Homogeneity, adjoint invariance and the two-sided ideal estimate supply the
laws needed to construct the trace-class operator ideal.

The gauge is lower semicontinuous in operator norm. Finite gauge forces approximation
numbers to tend to zero. Over a locally compact scalar field this implies compactness
when the target is complete, and the identity on an infinite-dimensional Banach space
has infinite gauge.
Finite-rank operators have finite gauge, computed by any prefix beyond their rank.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987, Chapter 2.
-/

public section

open Filter
open scoped ENNReal NNReal Topology

namespace ContinuousLinearMap

section Normed

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The nuclear gauge is the extended sum of the zero-indexed approximation numbers.
On Hilbert spaces its finite-gauge operators are the trace-class operators. -/
noncomputable def nuclearENorm (T : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' n, (T.singularValue n : ℝ≥0∞)

/-- The nuclear gauge as a sum of approximation numbers. -/
theorem nuclearENorm_def (T : E →L[𝕜] F) :
    T.nuclearENorm = ∑' n, (T.singularValue n : ℝ≥0∞) := (rfl)

/-- The nuclear gauge is the supremum of the Ky Fan prefix gauges. -/
theorem nuclearENorm_eq_iSup_kyFanGauge (T : E →L[𝕜] F) :
    T.nuclearENorm = ⨆ k, (T.kyFanGauge k : ℝ≥0∞) := by
  simp only [nuclearENorm_def, ENNReal.tsum_eq_iSup_nat, kyFanGauge_def, ENNReal.ofNNReal_finsetSum]

/-- Every Ky Fan prefix is bounded by the nuclear gauge. -/
theorem kyFanGauge_le_nuclearENorm (T : E →L[𝕜] F) (k : ℕ) :
    (T.kyFanGauge k : ℝ≥0∞) ≤ T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  exact le_iSup (fun k ↦ (T.kyFanGauge k : ℝ≥0∞)) k

/-- The nuclear gauge dominates the operator norm. -/
theorem enorm_le_nuclearENorm (T : E →L[𝕜] F) : ‖T‖ₑ ≤ T.nuclearENorm := by
  simpa [enorm_eq_nnnorm] using T.kyFanGauge_le_nuclearENorm 1

@[simp]
theorem nuclearENorm_zero : (0 : E →L[𝕜] F).nuclearENorm = 0 := by
  simp [nuclearENorm_def]

/-- Absolute homogeneity of the nuclear gauge, including its infinite values. -/
@[simp]
theorem nuclearENorm_smul (c : 𝕜) (T : E →L[𝕜] F) :
    (c • T).nuclearENorm = ‖c‖ₑ * T.nuclearENorm := by
  simp [nuclearENorm_def, singularValue_smul, ENNReal.tsum_mul_left, enorm_eq_nnnorm]

/-- Negation preserves the nuclear gauge. -/
@[simp]
theorem nuclearENorm_neg (T : E →L[𝕜] F) : (-T).nuclearENorm = T.nuclearENorm := by
  simpa using nuclearENorm_smul (-1 : 𝕜) T

/-- The nuclear gauge satisfies the two-sided ideal bound. -/
theorem nuclearENorm_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    (A ∘L T ∘L B).nuclearENorm ≤ ‖A‖ₑ * T.nuclearENorm * ‖B‖ₑ := by
  simp only [nuclearENorm_def, enorm_eq_nnnorm, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_le_tsum fun n ↦ by
    exact_mod_cast singularValue_comp_comp_le A T B n

/-- Domination of every Ky Fan prefix implies domination of the nuclear gauges. -/
theorem nuclearENorm_le_of_forall_kyFanGauge_le {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : ∀ k, S.kyFanGauge k ≤ T.kyFanGauge k) : S.nuclearENorm ≤ T.nuclearENorm := by
  simp only [nuclearENorm_eq_iSup_kyFanGauge]
  exact iSup_mono fun k ↦ ENNReal.coe_le_coe.mpr (h k)

/-- The nuclear gauge is finite exactly when the approximation numbers are summable. -/
theorem nuclearENorm_ne_top_iff_summable (T : E →L[𝕜] F) :
    T.nuclearENorm ≠ ∞ ↔ Summable T.singularValue :=
  ENNReal.tsum_coe_ne_top_iff_summable

/-- A rank cutoff turns the nuclear gauge into a finite Ky Fan prefix. -/
theorem nuclearENorm_eq_kyFanGauge_of_rank_le (T : E →L[𝕜] F) {k : ℕ}
    (hT : T.rank ≤ k) : T.nuclearENorm = (T.kyFanGauge k : ℝ≥0∞) := by
  rw [nuclearENorm_def, kyFanGauge_def, ENNReal.ofNNReal_finsetSum]
  exact tsum_eq_sum fun n hn ↦ by
    have hkn : k ≤ n := by simpa using hn
    simp [singularValue_eq_zero_of_rank_le (hT.trans (Nat.cast_le.mpr hkn))]

/-- Finite-rank operators have finite nuclear gauge. -/
theorem nuclearENorm_ne_top_of_rank_le (T : E →L[𝕜] F) {k : ℕ} (hT : T.rank ≤ k) :
    T.nuclearENorm ≠ ∞ := by
  rw [T.nuclearENorm_eq_kyFanGauge_of_rank_le hT]
  exact ENNReal.coe_ne_top

/-- The nuclear gauge is lower semicontinuous in the operator norm topology. -/
theorem lowerSemicontinuous_nuclearENorm :
    LowerSemicontinuous (nuclearENorm : (E →L[𝕜] F) → ℝ≥0∞) :=
  lowerSemicontinuous_tsum fun n ↦
    (ENNReal.continuous_coe.comp (continuous_singularValue n)).lowerSemicontinuous

end Normed

section Separated

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The nuclear gauge vanishes exactly at zero for maps into a separated normed space. -/
@[simp]
theorem nuclearENorm_eq_zero (T : E →L[𝕜] F) :
    T.nuclearENorm = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  exact T.opENorm_eq_zero_iff.mp (le_antisymm (h ▸ T.enorm_le_nuclearENorm) bot_le)

end Separated

section Compact

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Finite nuclear gauge implies compactness for a complete target over a locally compact field. -/
theorem isCompactOperator_of_nuclearENorm_ne_top {T : E →L[𝕜] F}
    (hT : T.nuclearENorm ≠ ∞) : IsCompactOperator T := by
  have hz := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hT
  exact isCompactOperator_of_tendsto_singularValue (ENNReal.tendsto_coe.mp hz)

end Compact

section Identity

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [LocallyCompactSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The identity on an infinite-dimensional Banach space has infinite nuclear gauge. -/
theorem nuclearENorm_id_eq_top (hE : ¬ FiniteDimensional 𝕜 E) :
    (ContinuousLinearMap.id 𝕜 E).nuclearENorm = ∞ := by
  by_contra h
  exact hE (FiniteDimensional.of_isCompactOperator_id
    ((ContinuousLinearMap.id 𝕜 E).isCompactOperator_of_nuclearENorm_ne_top h))

end Identity

section Hilbert

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The nuclear gauge is subadditive for operators from a Hilbert space. -/
theorem nuclearENorm_add_le (S T : E →L[𝕜] F) :
    (S + T).nuclearENorm ≤ S.nuclearENorm + T.nuclearENorm := by
  rw [nuclearENorm_eq_iSup_kyFanGauge]
  refine iSup_le fun k ↦ ?_
  calc ((S + T).kyFanGauge k : ℝ≥0∞)
      ≤ (S.kyFanGauge k : ℝ≥0∞) + T.kyFanGauge k := by
        exact_mod_cast kyFanGauge_add_le S T k
    _ ≤ S.nuclearENorm + T.nuclearENorm :=
      add_le_add (S.kyFanGauge_le_nuclearENorm k) (T.kyFanGauge_le_nuclearENorm k)

/-- Taking adjoints preserves the nuclear gauge. -/
@[simp]
theorem nuclearENorm_adjoint [CompleteSpace F] (T : E →L[𝕜] F) :
    T.adjoint.nuclearENorm = T.nuclearENorm := by
  simp [nuclearENorm_def]

end Hilbert

end ContinuousLinearMap
