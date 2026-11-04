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
* `TauCeti.OperatorIdealFamily.gauge_adjoint`, `TauCeti.OperatorIdealFamily.gauge_star`,
  `TauCeti.OperatorIdealFamily.adjoint_mem_finiteSubmodule_iff`: a Ky Fan dominant gauge on one
  universe is invariant under adjoints, so over `ℂ` it also controls the real and imaginary parts
  of an endomorphism (`TauCeti.OperatorIdealFamily.gauge_realPart_le`,
  `TauCeti.OperatorIdealFamily.gauge_imaginaryPart_le`).
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

/-- On endomorphisms, a Ky Fan dominant gauge is invariant under `star`. -/
@[simp]
theorem gauge_star (Φ : OperatorIdealFamily.{u, v, v} 𝕜) [Φ.IsKyFanDominant]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) :
    Φ.gauge (star A) = Φ.gauge A := by
  rw [star_eq_adjoint, gauge_adjoint]

/-- Membership in the ideal of a Ky Fan dominant family on one universe is invariant under
adjoints. -/
theorem adjoint_mem_finiteSubmodule_iff {Φ : OperatorIdealFamily.{u, v, v} 𝕜} [Φ.IsKyFanDominant]
    {E F : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] (A : E →L[𝕜] F) :
    adjoint A ∈ (Φ.operatorGauge F E).finiteSubmodule ↔
      A ∈ (Φ.operatorGauge E F).finiteSubmodule := by
  simp [OperatorGauge.mem_finiteSubmodule]

/-- On endomorphisms, membership in the ideal of a Ky Fan dominant family is invariant under
`star`. -/
theorem star_mem_finiteSubmodule_iff {Φ : OperatorIdealFamily.{u, v, v} 𝕜} [Φ.IsKyFanDominant]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) :
    star A ∈ (Φ.operatorGauge E E).finiteSubmodule ↔
      A ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  simp [OperatorGauge.mem_finiteSubmodule]

section Complex

open scoped ComplexStarModule

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- In a Ky Fan dominant family over `ℂ`, the real part of an endomorphism has gauge at most that
of the operator. -/
theorem gauge_realPart_le (Φ : OperatorIdealFamily.{0, v, v} ℂ) [Φ.IsKyFanDominant]
    (A : E →L[ℂ] E) :
    Φ.gauge (ℜ A : E →L[ℂ] E) ≤ Φ.gauge A := by
  have h2 : ‖(2 : ℂ)⁻¹‖ₑ = 2⁻¹ := by
    rw [enorm_eq_nnnorm]
    norm_num
  calc Φ.gauge (ℜ A : E →L[ℂ] E)
      = Φ.gauge ((2 : ℂ)⁻¹ • (A + star A)) := by
        rw [realPart_apply_coe, ← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    _ = 2⁻¹ * Φ.gauge (A + star A) := by rw [Φ.gauge_smul, h2]
    _ ≤ 2⁻¹ * (Φ.gauge A + Φ.gauge (star A)) := by gcongr; exact Φ.gauge_add_le _ _
    _ = Φ.gauge A := by
        rw [gauge_star, ← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- In a Ky Fan dominant family over `ℂ`, the imaginary part of an endomorphism has gauge at most
that of the operator. -/
theorem gauge_imaginaryPart_le (Φ : OperatorIdealFamily.{0, v, v} ℂ) [Φ.IsKyFanDominant]
    (A : E →L[ℂ] E) :
    Φ.gauge (ℑ A : E →L[ℂ] E) ≤ Φ.gauge A := by
  simpa [enorm_eq_nnnorm] using gauge_realPart_le Φ (-Complex.I • A)

variable {Φ : OperatorIdealFamily.{0, v, v} ℂ} [Φ.IsKyFanDominant]

/-- The ideal of a Ky Fan dominant family over `ℂ` is closed under taking the real part of an
endomorphism. -/
theorem realPart_mem_finiteSubmodule {A : E →L[ℂ] E}
    (hA : A ∈ (Φ.operatorGauge E E).finiteSubmodule) :
    (ℜ A : E →L[ℂ] E) ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_realPart_le Φ A).trans_lt hA

/-- The ideal of a Ky Fan dominant family over `ℂ` is closed under taking the imaginary part of an
endomorphism. -/
theorem imaginaryPart_mem_finiteSubmodule {A : E →L[ℂ] E}
    (hA : A ∈ (Φ.operatorGauge E E).finiteSubmodule) :
    (ℑ A : E →L[ℂ] E) ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_imaginaryPart_le Φ A).trans_lt hA

/-- An endomorphism lies in the ideal of a Ky Fan dominant family over `ℂ` if and only if its real
and imaginary parts do. -/
theorem mem_finiteSubmodule_iff_realPart_and_imaginaryPart (A : E →L[ℂ] E) :
    A ∈ (Φ.operatorGauge E E).finiteSubmodule ↔
      (ℜ A : E →L[ℂ] E) ∈ (Φ.operatorGauge E E).finiteSubmodule ∧
        (ℑ A : E →L[ℂ] E) ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  refine ⟨fun hA ↦ ⟨realPart_mem_finiteSubmodule hA, imaginaryPart_mem_finiteSubmodule hA⟩,
    fun ⟨hre, him⟩ ↦ ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart A]
  exact Submodule.add_mem _ hre (Submodule.smul_mem _ _ him)

end Complex

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
