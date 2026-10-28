/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family
public import TauCeti.Analysis.OperatorIdeal.Carrier

/-!
# The normed ideals of an operator-ideal family

An operator-ideal family `Φ` restricts, on each Hilbert-space pair `E`, `F`, to the operator gauge
`Φ.operatorGauge E F`. Its finite-gauge submodule is the operator ideal of the family, which is
stable under composition with bounded operators on either side, and its carrier is the normed
space of operators of finite gauge.

A family is complete (`OperatorIdealFamily.IsComplete`) when all of its carriers are Banach spaces.
This holds as soon as every gauge is lower semicontinuous for the operator-norm topology.

## Main declarations

* `TauCeti.OperatorIdealFamily.operatorGauge`: the operator gauge of a family on a Hilbert-space
  pair.
* `TauCeti.OperatorIdealFamily.comp_left_mem_finiteSubmodule`,
  `TauCeti.OperatorIdealFamily.comp_right_mem_finiteSubmodule`: the ideal is stable under
  composition.
* `TauCeti.OperatorIdealFamily.IsComplete`: every carrier of the family is complete.
* `TauCeti.OperatorIdealFamily.isComplete_of_lowerSemicontinuous`: a family with lower
  semicontinuous gauges is complete.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  AMS, 1969, Chapter III.
-/

public section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable (Φ : OperatorIdealFamily.{u, v, w} 𝕜)
variable (E : Type v) (F : Type w)
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge of an operator-ideal family on the bounded operators between a Hilbert-space
pair. -/
def operatorGauge : OperatorGauge 𝕜 E F where
  toFun := Φ.gauge
  map_add_le' := Φ.gauge_add_le
  map_smul' := Φ.gauge_smul
  enorm_le' := Φ.enorm_le_gauge

variable {Φ E F}

@[simp]
theorem operatorGauge_apply (A : E →L[𝕜] F) : Φ.operatorGauge E F A = Φ.gauge A := (rfl)

/-- The ideal of a family is stable under composition on the left with a bounded operator. -/
theorem comp_left_mem_finiteSubmodule {G : Type w}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : A ∈ (Φ.operatorGauge E F).finiteSubmodule) :
    L ∘L A ∈ (Φ.operatorGauge E G).finiteSubmodule := by
  simp only [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (Φ.gauge_comp_left_le L A).trans_lt (ENNReal.mul_lt_top enorm_lt_top hA)

/-- The ideal of a family is stable under composition on the right with a bounded operator. -/
theorem comp_right_mem_finiteSubmodule {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (hA : A ∈ (Φ.operatorGauge E F).finiteSubmodule) (R : H →L[𝕜] E) :
    A ∘L R ∈ (Φ.operatorGauge H F).finiteSubmodule := by
  simp only [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (Φ.gauge_comp_right_le A R).trans_lt (ENNReal.mul_lt_top hA enorm_lt_top)

/-! ### Completeness -/

variable (Φ) in
/-- An operator-ideal family is complete when the normed carrier of every Hilbert-space pair is a
Banach space. -/
class IsComplete : Prop where
  /-- Every carrier of the family is complete. -/
  completeSpace_carrier : ∀ (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    CompleteSpace (Φ.operatorGauge E F).Carrier

instance [Φ.IsComplete] : CompleteSpace (Φ.operatorGauge E F).Carrier :=
  IsComplete.completeSpace_carrier E F

/-- An operator-ideal family whose gauges are lower semicontinuous for the operator-norm topology
is complete. -/
theorem isComplete_of_lowerSemicontinuous
    (h : ∀ (E : Type v) (F : Type w)
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      LowerSemicontinuous fun A : E →L[𝕜] F ↦ Φ.gauge A) :
    Φ.IsComplete :=
  ⟨fun E F _ _ _ _ _ _ ↦ OperatorGauge.completeSpace_carrier_of_lowerSemicontinuous (h E F)⟩

end OperatorIdealFamily

end TauCeti
