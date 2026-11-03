/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Equivalence
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import TauCeti.Analysis.OperatorIdeal.Family
public import TauCeti.Analysis.OperatorIdeal.OperatorNorm
public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic

/-!
# The operator-ideal family induced by a symmetric gauge

A symmetric gauge `Φ` on finitely supported nonnegative sequences extends to a gauge `Φ∞` on all
`ℝ≥0∞`-valued sequences (`TauCeti.SymmetricGauge.extend`). Applying `Φ∞` to the approximation
numbers of a bounded operator gives the extended gauge `Φ(T) = Φ∞(n ↦ aₙ(T))`. Its finite locus is
the symmetrically normed operator ideal attached to `Φ`: the supremum gauge gives the operator
norm, the sum gives the nuclear gauge, and the `ℓᵖ` gauges give the Schatten classes.

The induced gauge is absolutely homogeneous, dominates the operator norm and satisfies the
two-sided ideal inequality on bounded maps between arbitrary seminormed spaces, because the
approximation numbers have these properties termwise. It depends only on the approximation-number
sequence, so it is unchanged under adjoints of Hilbert-space operators. It is monotone for Ky Fan
domination: since symmetric gauges are monotone for weak majorization of antitone sequences, if
every Ky Fan prefix `Kₖ(S)` is at most `Kₖ(T)` then `Φ(S) ≤ Φ(T)`. Combined with the Ky Fan
triangle inequality `Kₖ(S + T) ≤ Kₖ(S) + Kₖ(T)` and the subadditivity of `Φ∞`, this gives
subadditivity of the induced gauge on Hilbert spaces.

These four laws make the induced gauges an operator-ideal family over every pair of Hilbert
spaces, and adjoint invariance makes its diagonal-universe restriction a symmetric family.

Since the approximation numbers decrease from `a₀(T) = ‖T‖`, the supremum gauge induces the
operator-norm family: it is the `p = ∞` endpoint of the Schatten scale.

## Main definitions

* `TauCeti.SymmetricGauge.opGauge`: the gauge `Φ(T) = Φ∞(n ↦ aₙ(T))` of a bounded map.
* `TauCeti.SymmetricGauge.operatorIdealFamily`: the rectangular operator-ideal family with gauge
  `Φ(T)`.
* `TauCeti.SymmetricGauge.symmetricOperatorIdealFamily`: its adjoint-invariant view on the
  diagonal universe.

## Main results

* `TauCeti.SymmetricGauge.enorm_le_opGauge`: `‖T‖ ≤ Φ(T)`.
* `TauCeti.SymmetricGauge.opGauge_supGauge`: the supremum gauge induces the operator norm.
* `TauCeti.SymmetricGauge.operatorIdealFamily_supGauge`: the family induced by the supremum
  gauge is the operator-norm family.
* `TauCeti.SymmetricGauge.opGauge_smul`: `Φ(c T) = ‖c‖ Φ(T)`.
* `TauCeti.SymmetricGauge.opGauge_comp_comp_le`: `Φ(A T B) ≤ ‖A‖ Φ(T) ‖B‖`.
* `TauCeti.SymmetricGauge.opGauge_comp_comp_le_self`: `Φ(A T B) ≤ Φ(T)` for contractions `A`, `B`.
* `TauCeti.SymmetricGauge.opGauge_le_of_forall_kyFanGauge_le`: Ky Fan domination implies
  domination of the induced gauges.
* `TauCeti.SymmetricGauge.opGauge_add_le`: `Φ(S + T) ≤ Φ(S) + Φ(T)` for maps out of a Hilbert
  space.
* `TauCeti.SymmetricGauge.opGauge_adjoint`: `Φ(T†) = Φ(T)`, with source and target in arbitrary
  universes.
* `TauCeti.SymmetricGauge.opGauge_eq_of_sameSingularValues`: operators with the same
  approximation numbers have the same induced gauge.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators in
  Hilbert Space*, Translations of Mathematical Monographs 18, AMS (1969), Chapter III.
* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Mathematical Surveys and Monographs
  120, AMS (2005), Chapter 1.
-/

public section

open ContinuousLinearMap
open scoped ENNReal NNReal

universe u v w

namespace TauCeti

namespace SymmetricGauge

variable (Φ : SymmetricGauge)

section Seminormed

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The gauge `Φ(T) = Φ∞(n ↦ aₙ(T))` induced by a symmetric gauge `Φ` on a bounded linear map
`T`: the extension of `Φ` evaluated on the approximation numbers of `T`. On Hilbert spaces its
finite values select the symmetrically normed operator ideal attached to `Φ`. -/
noncomputable def opGauge (T : E →L[𝕜] F) : ℝ≥0∞ :=
  Φ.extend fun n ↦ (T.singularValue n : ℝ≥0∞)

/-- The induced gauge is the extended symmetric gauge of the approximation numbers. -/
theorem opGauge_def (T : E →L[𝕜] F) :
    Φ.opGauge T = Φ.extend fun n ↦ (T.singularValue n : ℝ≥0∞) := (rfl)

/-- The induced gauge dominates the operator norm. -/
theorem enorm_le_opGauge (T : E →L[𝕜] F) : ‖T‖ₑ ≤ Φ.opGauge T :=
  calc ‖T‖ₑ = (T.singularValue 0 : ℝ≥0∞) := by rw [singularValue_zero, enorm_eq_nnnorm]
    _ ≤ ⨆ n, (T.singularValue n : ℝ≥0∞) := le_iSup (fun n ↦ (T.singularValue n : ℝ≥0∞)) 0
    _ ≤ Φ.opGauge T := Φ.iSup_le_extend _

/-- The supremum gauge induces the operator norm: `supₙ aₙ(T) = ‖T‖`. -/
@[simp]
theorem opGauge_supGauge (T : E →L[𝕜] F) : supGauge.opGauge T = ‖T‖ₑ := by
  rw [opGauge_def, extend_supGauge, ← ENNReal.coe_iSup T.bddAbove_range_singularValue,
    iSup_singularValue, enorm_eq_nnnorm]

/-- Absolute homogeneity of the induced gauge, including its infinite values. -/
@[simp]
theorem opGauge_smul (c : 𝕜) (T : E →L[𝕜] F) : Φ.opGauge (c • T) = ‖c‖ₑ * Φ.opGauge T := by
  have h : (fun n ↦ ((c • T).singularValue n : ℝ≥0∞)) =
      ‖c‖ₑ • fun n ↦ (T.singularValue n : ℝ≥0∞) := by
    ext n
    simp [singularValue_smul, enorm_eq_nnnorm]
  rw [opGauge_def, opGauge_def, h, extend_smul]

@[simp]
theorem opGauge_zero : Φ.opGauge (0 : E →L[𝕜] F) = 0 := by
  simpa using Φ.opGauge_smul (0 : 𝕜) (0 : E →L[𝕜] F)

/-- Negation preserves the induced gauge. -/
@[simp]
theorem opGauge_neg (T : E →L[𝕜] F) : Φ.opGauge (-T) = Φ.opGauge T := by
  simpa using Φ.opGauge_smul (-1 : 𝕜) T

/-- The induced gauge satisfies the two-sided ideal inequality `Φ(A T B) ≤ ‖A‖ Φ(T) ‖B‖`. -/
theorem opGauge_comp_comp_le (A : G →L[𝕜] H) (T : F →L[𝕜] G) (B : E →L[𝕜] F) :
    Φ.opGauge (A ∘L T ∘L B) ≤ ‖A‖ₑ * Φ.opGauge T * ‖B‖ₑ :=
  calc Φ.opGauge (A ∘L T ∘L B)
      ≤ Φ.extend ((‖A‖ₑ * ‖B‖ₑ) • fun n ↦ (T.singularValue n : ℝ≥0∞)) :=
        Φ.extend_mono fun n ↦ by
          simpa [enorm_eq_nnnorm, mul_right_comm] using
            ENNReal.coe_le_coe.2 (singularValue_comp_comp_le A T B n)
    _ = ‖A‖ₑ * Φ.opGauge T * ‖B‖ₑ := by rw [extend_smul, opGauge_def, mul_right_comm]

/-- Composition on both sides by contractions does not increase the induced gauge. -/
theorem opGauge_comp_comp_le_self {A : G →L[𝕜] H} (hA : ‖A‖ ≤ 1) (T : F →L[𝕜] G)
    {B : E →L[𝕜] F} (hB : ‖B‖ ≤ 1) : Φ.opGauge (A ∘L T ∘L B) ≤ Φ.opGauge T := by
  refine (Φ.opGauge_comp_comp_le A T B).trans ?_
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact (mul_le_of_le_one_right' (by exact_mod_cast hB)).trans
    (mul_le_of_le_one_left' (by exact_mod_cast hA))

/-- **Ky Fan dominance.** If every Ky Fan prefix of `S` is at most the corresponding prefix of `T`,
then the induced gauge of `S` is at most that of `T`. The two maps may act between different
spaces. -/
theorem opGauge_le_of_forall_kyFanGauge_le {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : ∀ k, S.kyFanGauge k ≤ T.kyFanGauge k) : Φ.opGauge S ≤ Φ.opGauge T :=
  Φ.extend_le_extend_of_forall_sum_le
    (fun _ _ hmn ↦ ENNReal.coe_le_coe.2 (S.antitone_singularValue hmn)) fun k ↦ by
      simpa only [kyFanGauge_def, ENNReal.ofNNReal_finsetSum] using ENNReal.coe_le_coe.2 (h k)

/-- Operators with the same approximation-number sequence have the same induced gauge. -/
theorem opGauge_eq_of_sameSingularValues {S : G →L[𝕜] H} {T : E →L[𝕜] F}
    (h : SameSingularValues S T) : Φ.opGauge S = Φ.opGauge T := by
  simp only [opGauge_def, (sameSingularValues_iff S T).1 h]

end Seminormed

section InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Subadditivity of the induced gauge.** For bounded maps from a Hilbert space to an inner
product space, `Φ(S + T) ≤ Φ(S) + Φ(T)`. -/
theorem opGauge_add_le [CompleteSpace E] (S T : E →L[𝕜] F) :
    Φ.opGauge (S + T) ≤ Φ.opGauge S + Φ.opGauge T := by
  -- By the Ky Fan triangle inequality, `a(S + T)` is weakly majorized by `a(S) + a(T)`.
  refine (Φ.extend_le_extend_of_forall_sum_le
    (b := (fun n ↦ (S.singularValue n : ℝ≥0∞)) + fun n ↦ (T.singularValue n : ℝ≥0∞))
    (fun _ _ hmn ↦ ENNReal.coe_le_coe.2 ((S + T).antitone_singularValue hmn))
    fun k ↦ ?_).trans (Φ.extend_add_le _ _)
  simpa only [kyFanGauge_def, Pi.add_apply, Finset.sum_add_distrib, ENNReal.ofNNReal_finsetSum,
    ENNReal.coe_add] using ENNReal.coe_le_coe.2 (kyFanGauge_add_le S T k)

/-- **Adjoint invariance of the induced gauge.** A bounded operator between Hilbert spaces and its
adjoint have the same induced gauge. Source and target may lie in different universes. -/
@[simp]
theorem opGauge_adjoint [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    Φ.opGauge (adjoint T) = Φ.opGauge T := by
  simp only [opGauge_def, singularValue_adjoint]

end InnerProductSpace

/-- The rectangular operator-ideal family induced by a symmetric gauge `Φ`, with gauge
`T ↦ Φ∞(n ↦ aₙ(T))` on bounded operators between Hilbert spaces in arbitrary source and target
universes. -/
noncomputable def operatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] (Φ : SymmetricGauge) :
    OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := Φ.opGauge A
  gauge_add_le := Φ.opGauge_add_le
  gauge_smul := Φ.opGauge_smul
  enorm_le_gauge := Φ.enorm_le_opGauge
  gauge_comp_le := Φ.opGauge_comp_comp_le

@[simp]
theorem operatorIdealFamily_gauge {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    (Φ.operatorIdealFamily.{u, v, w} 𝕜).gauge A = Φ.opGauge A := (rfl)

/-- The symmetric operator-ideal family induced by a symmetric gauge `Φ`: the diagonal-universe
restriction of `TauCeti.SymmetricGauge.operatorIdealFamily`, whose gauge is invariant under
adjoints. -/
noncomputable def symmetricOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] (Φ : SymmetricGauge) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := Φ.operatorIdealFamily.{u, v, v} 𝕜
  gauge_adjoint A := Φ.opGauge_adjoint A

@[simp]
theorem symmetricOperatorIdealFamily_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    (Φ.symmetricOperatorIdealFamily.{u, v} 𝕜).toOperatorIdealFamily =
      Φ.operatorIdealFamily.{u, v, v} 𝕜 := (rfl)

/-- **The operator-norm endpoint of the Schatten scale.** The family induced by the supremum
gauge, with gauge `supₙ aₙ(T)`, is the operator-norm family. -/
theorem operatorIdealFamily_supGauge (𝕜 : Type u) [RCLike 𝕜] :
    supGauge.operatorIdealFamily.{u, v, w} 𝕜 = OperatorIdealFamily.opNorm 𝕜 := by
  ext
  simp

/-- The symmetric family induced by the supremum gauge is the symmetric operator-norm family. -/
theorem symmetricOperatorIdealFamily_supGauge (𝕜 : Type u) [RCLike 𝕜] :
    supGauge.symmetricOperatorIdealFamily.{u, v} 𝕜 = SymmetricOperatorIdealFamily.opNorm 𝕜 := by
  ext
  simp

end SymmetricGauge

end TauCeti
