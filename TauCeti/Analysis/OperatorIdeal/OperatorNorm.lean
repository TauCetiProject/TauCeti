/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Carrier

/-!
# The operator-norm ideal family

The extended operator norm `A ↦ ‖A‖ₑ` is the smallest operator-ideal family: every family
dominates it by the law `OperatorIdealFamily.enorm_le_gauge`. Its ideal consists of all bounded
operators, and its carrier is complete because the operator norm is continuous.

Taking adjoints preserves the operator norm, so its diagonal-universe restriction is a symmetric
family.

## Main declarations

* `TauCeti.OperatorIdealFamily.opNorm`: the operator-ideal family with gauge `‖A‖ₑ`.
* `TauCeti.OperatorIdealFamily.finiteSubmodule_opNorm`: every bounded operator lies in its ideal.
* `TauCeti.OperatorIdealFamily.opNorm_isComplete`: the operator-norm family is complete.
* `TauCeti.SymmetricOperatorIdealFamily.opNorm`: the adjoint-invariant diagonal family.
-/

public section

noncomputable section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The operator-ideal family whose gauge is the extended operator norm. -/
def opNorm : OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := ‖A‖ₑ
  gauge_add_le A B := enorm_add_le A B
  gauge_smul c A := enorm_smul c A
  enorm_le_gauge _ := le_rfl
  gauge_comp_le L A R := by
    calc ‖L ∘L A ∘L R‖ₑ ≤ ‖L‖ₑ * ‖A ∘L R‖ₑ := ContinuousLinearMap.opENorm_comp_le _ _
      _ ≤ ‖L‖ₑ * (‖A‖ₑ * ‖R‖ₑ) := by gcongr; exact ContinuousLinearMap.opENorm_comp_le _ _
      _ = ‖L‖ₑ * ‖A‖ₑ * ‖R‖ₑ := (mul_assoc _ _ _).symm

variable {𝕜}
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

@[simp]
theorem gauge_opNorm (A : E →L[𝕜] F) : (opNorm.{u, v, w} 𝕜).gauge A = ‖A‖ₑ := (rfl)

variable (E F) in
/-- Every bounded operator lies in the ideal of the operator-norm family. -/
@[simp]
theorem finiteSubmodule_opNorm : ((opNorm.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule = ⊤ :=
  eq_top_iff.2 fun A _ ↦ by simp

/-- The operator-norm family is complete. -/
instance opNorm_isComplete : (opNorm.{u, v, w} 𝕜).IsComplete :=
  isComplete_of_lowerSemicontinuous fun _ _ _ _ _ _ _ _ ↦ by
    simpa using continuous_enorm.lowerSemicontinuous

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

/-- The adjoint-invariant diagonal-universe operator-norm family. -/
def opNorm (𝕜 : Type u) [RCLike 𝕜] : SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := OperatorIdealFamily.opNorm.{u, v, v} 𝕜
  gauge_adjoint A := ContinuousLinearMap.adjoint.enorm_map A

/-- The underlying rectangular family of the symmetric operator-norm family. -/
@[simp]
theorem opNorm_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    (opNorm.{u, v} 𝕜).toOperatorIdealFamily = OperatorIdealFamily.opNorm.{u, v, v} 𝕜 :=
  (rfl)

end SymmetricOperatorIdealFamily

end TauCeti
