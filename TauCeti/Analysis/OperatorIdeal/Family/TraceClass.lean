/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import TauCeti.Analysis.OperatorIdeal.Nuclear.Basic

/-!
# The trace-class operator-ideal family

The trace-class family assigns to a bounded operator `T` between real or complex Hilbert spaces
its nuclear gauge `ν(T) = ∑' n, aₙ(T)`, the extended sum of its zero-based approximation numbers
(`ContinuousLinearMap.nuclearENorm`). The four operator-ideal laws are the subadditivity,
homogeneity, operator-norm domination and two-sided ideal inequality of the nuclear gauge, and
adjoint invariance of the approximation numbers makes the diagonal family symmetric.

An operator lies in the trace-class ideal exactly when its approximation numbers are summable.
Finite nuclear gauge forces compactness
(`ContinuousLinearMap.isCompactOperator_of_nuclearENorm_ne_top`), while the identity of an
infinite-dimensional Hilbert space has infinite nuclear gauge
(`ContinuousLinearMap.nuclearENorm_id_eq_top`) and so is a bounded operator outside the ideal.
The nuclear gauge is lower semicontinuous in operator norm, so the normed carriers are complete.
The trace-class family is the `p = 1` member of the Schatten scale.

## Main declarations

* `TauCeti.OperatorIdealFamily.traceClass`: the trace-class operator-ideal family.
* `TauCeti.OperatorIdealFamily.gauge_traceClass`: its gauge is the nuclear gauge.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_traceClass_iff`: membership in the ideal is
  summability of the approximation numbers.
* `TauCeti.OperatorIdealFamily.traceClass_isComplete`: its normed carriers are complete.
* `TauCeti.OperatorIdealFamily.schatten_one`: the Schatten family at `p = 1` is the trace-class
  family.
* `TauCeti.SymmetricOperatorIdealFamily.traceClass`: the adjoint-invariant diagonal family.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapters 1–2.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987, Chapter 2.
-/

public section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The **trace-class operator-ideal family**, whose gauge is the nuclear gauge
`ν(T) = ∑' n, aₙ(T)`: the extended sum of the approximation numbers. -/
noncomputable def traceClass : OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge T := T.nuclearENorm
  gauge_add_le S T := S.nuclearENorm_add_le T
  gauge_smul c T := T.nuclearENorm_smul c
  enorm_le_gauge T := T.enorm_le_nuclearENorm
  gauge_comp_le L A R := L.nuclearENorm_comp_comp_le A R

variable {𝕜}
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The trace-class gauge is the nuclear gauge. -/
@[simp]
theorem gauge_traceClass (T : E →L[𝕜] F) :
    (traceClass.{u, v, w} 𝕜).gauge T = T.nuclearENorm := (rfl)

/-- An operator is trace class exactly when its approximation numbers are summable. -/
theorem mem_finiteSubmodule_traceClass_iff (T : E →L[𝕜] F) :
    T ∈ ((traceClass.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ↔
      Summable T.singularValue := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply, gauge_traceClass, lt_top_iff_ne_top,
    T.nuclearENorm_ne_top_iff_summable]

/-- The trace-class operator-ideal family has complete normed carriers. -/
instance traceClass_isComplete : (traceClass.{u, v, w} 𝕜).IsComplete :=
  isComplete_of_lowerSemicontinuous fun _ _ _ _ _ _ _ _ ↦
    ContinuousLinearMap.lowerSemicontinuous_nuclearENorm

/-- **The trace-class endpoint of the Schatten scale.** The Schatten family at `p = 1` is the
trace-class family. -/
theorem schatten_one : schatten.{u, v, w} 𝕜 1 le_rfl = traceClass 𝕜 := by
  ext
  simp [ContinuousLinearMap.nuclearENorm_def]

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

/-- The adjoint-invariant diagonal-universe trace-class family. -/
noncomputable def traceClass (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := OperatorIdealFamily.traceClass.{u, v, v} 𝕜
  gauge_adjoint T := T.nuclearENorm_adjoint

/-- The underlying rectangular family of the symmetric trace-class family. -/
@[simp]
theorem traceClass_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    (traceClass.{u, v} 𝕜).toOperatorIdealFamily = OperatorIdealFamily.traceClass.{u, v, v} 𝕜 :=
  (rfl)

/-- The symmetric Schatten family at `p = 1` is the symmetric trace-class family. -/
theorem schatten_one (𝕜 : Type u) [RCLike 𝕜] :
    schatten.{u, v} 𝕜 1 le_rfl = traceClass 𝕜 := by
  ext E F _ _ _ _ _ _ T
  have h := congrArg (fun Φ : OperatorIdealFamily.{u, v, v} 𝕜 ↦ Φ.gauge T)
    (OperatorIdealFamily.schatten_one (𝕜 := 𝕜))
  rwa [← schatten_toOperatorIdealFamily, ← traceClass_toOperatorIdealFamily] at h

end SymmetricOperatorIdealFamily

end TauCeti
