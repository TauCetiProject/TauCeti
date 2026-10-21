/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt
public import TauCeti.Analysis.OperatorIdeal.Family.KyFan.Basic
public import TauCeti.Analysis.OperatorIdeal.Family.TraceClass

/-!
# Ky Fan dominance of operator-ideal families

An operator-ideal family `Φ` is *Ky Fan dominant* when domination of every Ky Fan prefix
`Kₖ(A) = a₀(A) + ⋯ + aₖ₋₁(A)` by the corresponding prefix `Kₖ(B)` implies `Φ(A) ≤ Φ(B)`. The
operators `A` and `B` may act between different Hilbert-space pairs. This is Ky Fan's dominance
principle for symmetrically normed ideals: a Ky Fan dominant gauge depends only on the
approximation numbers, and is monotone for their weak majorization.

The four ideal-family laws do not force this property, so it is a separate class. It holds for
the operator-norm family, where `‖A‖ = K₁(A)`, for the Ky Fan families, and for the trace-class
family, whose gauge is the supremum of all Ky Fan prefixes. It also holds for every family
induced by a symmetric gauge, since symmetric gauges are monotone for weak majorization of
antitone sequences; in particular for the Schatten and Hilbert–Schmidt families.

Dominance gives a comparison principle for ideal membership: if `B` lies in the ideal of a Ky Fan
dominant family and every Ky Fan prefix of `A` is at most that of `B`, then `A` lies in the ideal
too. It also shows that operators with the same approximation numbers have the same gauge, so a
Ky Fan dominant family on a single universe is invariant under adjoints.

## Main declarations

* `TauCeti.OperatorIdealFamily.IsKyFanDominant`: Ky Fan prefix domination implies gauge
  domination.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_of_forall_kyFanGauge_le`: membership in the
  ideal of a Ky Fan dominant family transfers along Ky Fan prefix domination.
* `TauCeti.OperatorIdealFamily.gauge_eq_of_sameSingularValues`: a Ky Fan dominant gauge depends
  only on the approximation numbers.
* `TauCeti.OperatorIdealFamily.gauge_adjoint`: a Ky Fan dominant gauge on one universe is
  invariant under adjoints.
* Instances for the operator-norm, Ky Fan, trace-class, Schatten and Hilbert–Schmidt families,
  and for every family induced by a symmetric gauge.

## References

* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators in
  Hilbert Space*, Translations of Mathematical Monographs 18, AMS (1969), Chapter III, §4.
* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., Mathematical Surveys and Monographs
  120, AMS (2005), Chapter 1.
-/

public section

open ContinuousLinearMap
open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- An operator-ideal family is **Ky Fan dominant** when domination of every Ky Fan prefix
`Kₖ(A) ≤ Kₖ(B)` implies domination of the gauges `Φ(A) ≤ Φ(B)`. The operators may act between
different Hilbert-space pairs. -/
class IsKyFanDominant (Φ : OperatorIdealFamily.{u, v, w} 𝕜) : Prop where
  /-- Ky Fan prefix domination implies gauge domination. -/
  gauge_le_of_forall_kyFanGauge_le : ∀ {E G : Type v} {F H : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} {B : G →L[𝕜] H},
    (∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) → Φ.gauge A ≤ Φ.gauge B

export IsKyFanDominant (gauge_le_of_forall_kyFanGauge_le)

section Consequences

variable {Φ : OperatorIdealFamily.{u, v, w} 𝕜} [Φ.IsKyFanDominant]
variable {E G : Type v} {F H : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- **Membership transport under Ky Fan dominance.** If `B` lies in the ideal of a Ky Fan
dominant family and every Ky Fan prefix of `A` is at most that of `B`, then `A` lies in the
ideal. -/
theorem mem_finiteSubmodule_of_forall_kyFanGauge_le {A : E →L[𝕜] F} {B : G →L[𝕜] H}
    (hB : B ∈ (Φ.operatorGauge G H).finiteSubmodule)
    (h : ∀ k, A.kyFanGauge k ≤ B.kyFanGauge k) :
    A ∈ (Φ.operatorGauge E F).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hB ⊢
  exact (gauge_le_of_forall_kyFanGauge_le h).trans_lt hB

/-- Operators with the same approximation numbers have the same gauge in a Ky Fan dominant
family, even when they act between different Hilbert-space pairs. -/
theorem gauge_eq_of_sameSingularValues {A : E →L[𝕜] F} {B : G →L[𝕜] H}
    (h : SameSingularValues A B) : Φ.gauge A = Φ.gauge B :=
  (gauge_le_of_forall_kyFanGauge_le fun k ↦ (h.kyFanGauge_eq k).le).antisymm
    (gauge_le_of_forall_kyFanGauge_le fun k ↦ (h.kyFanGauge_eq k).ge)

end Consequences

/-- A Ky Fan dominant family whose sources and targets lie in one universe is invariant under
adjoints. -/
@[simp]
theorem gauge_adjoint (Φ : OperatorIdealFamily.{u, v, v} 𝕜) [Φ.IsKyFanDominant]
    {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    Φ.gauge (adjoint A) = Φ.gauge A :=
  gauge_eq_of_sameSingularValues ((sameSingularValues_iff _ _).2 (singularValue_adjoint A))

/-- Every finite Ky Fan family is Ky Fan dominant. -/
instance isKyFanDominant_kyFan (k : ℕ) (hk : 0 < k) :
    (kyFan.{u, v, w} 𝕜 k hk).IsKyFanDominant where
  gauge_le_of_forall_kyFanGauge_le h := by
    simpa using h k

/-- The operator-norm family is Ky Fan dominant, since `‖A‖ = K₁(A)`. -/
instance isKyFanDominant_opNorm : (opNorm.{u, v, w} 𝕜).IsKyFanDominant := by
  rw [← kyFan_one]
  infer_instance

/-- The trace-class family is Ky Fan dominant, since its gauge is the supremum of all Ky Fan
prefixes. -/
instance isKyFanDominant_traceClass : (traceClass.{u, v, w} 𝕜).IsKyFanDominant where
  gauge_le_of_forall_kyFanGauge_le h := by
    simpa using nuclearENorm_le_of_forall_kyFanGauge_le h

/-- **Ky Fan dominance of induced families.** The operator-ideal family induced by a symmetric
gauge is Ky Fan dominant. -/
instance _root_.TauCeti.SymmetricGauge.isKyFanDominant_operatorIdealFamily
    (Φ : SymmetricGauge) : (Φ.operatorIdealFamily.{u, v, w} 𝕜).IsKyFanDominant where
  gauge_le_of_forall_kyFanGauge_le h := by
    simpa using Φ.opGauge_le_of_forall_kyFanGauge_le h

/-- Every finite-exponent Schatten family is Ky Fan dominant. -/
instance isKyFanDominant_schatten (p : ℝ) (hp : 1 ≤ p) :
    (schatten.{u, v, w} 𝕜 p hp).IsKyFanDominant := by
  rw [schatten_def]
  infer_instance

/-- The Hilbert–Schmidt family is Ky Fan dominant. -/
instance isKyFanDominant_hilbertSchmidt : (hilbertSchmidt.{u, v, w} 𝕜).IsKyFanDominant := by
  rw [← schatten_two]
  infer_instance

end OperatorIdealFamily

end TauCeti
