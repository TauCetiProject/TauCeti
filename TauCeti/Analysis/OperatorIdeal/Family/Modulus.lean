/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import TauCeti.Analysis.InnerProductSpace.Modulus
public import TauCeti.Analysis.OperatorIdeal.Family.Carrier

/-!
# Operator-ideal gauges of moduli, adjoints, and Jordan–Cartesian parts

Every operator-ideal family whose sources and targets lie in one universe assigns the same gauge
to a bounded operator `A : E →L[𝕜] F`, to its modulus `|A| = √(A† A) : E →L[𝕜] E`, and to its
adjoint `A† : F →L[𝕜] E`, without assuming Ky Fan dominance. It also bounds the gauges of the
positive and negative parts of any endomorphism `A : E →L[𝕜] E` (for any real algebra structure
compatible with the `𝕜`-action) and, over `ℂ`, of its real and imaginary parts by `Φ(A)`.
Consequently, every operator ideal in one universe is closed under moduli, adjoints, Cartesian
parts, and positive and negative parts, so linear functionals defined on the positive cone of an
operator ideal extend across self-adjoint and Cartesian decompositions.

## Main declarations

* `TauCeti.OperatorIdealFamily.gauge_modulus`, `TauCeti.OperatorIdealFamily.gauge_adjoint`,
  `TauCeti.OperatorIdealFamily.gauge_star`: `Φ(|A|) = Φ(A)`, `Φ(A†) = Φ(A)`, and `Φ(star A) = Φ(A)`.
* `TauCeti.OperatorIdealFamily.modulus_mem_finiteSubmodule_iff`,
  `TauCeti.OperatorIdealFamily.adjoint_mem_finiteSubmodule_iff`,
  `TauCeti.OperatorIdealFamily.star_mem_finiteSubmodule_iff`: ideal invariance under moduli,
  adjoints, and `star`.
* `TauCeti.OperatorIdealFamily.gauge_posPart_le`, `TauCeti.OperatorIdealFamily.gauge_negPart_le`,
  `TauCeti.OperatorIdealFamily.posPart_mem_finiteSubmodule`,
  `TauCeti.OperatorIdealFamily.negPart_mem_finiteSubmodule`,
  `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_iff_posPart_and_negPart`: gauge bounds and ideal
  closure under positive and negative parts.
* `TauCeti.OperatorIdealFamily.gauge_realPart_le`,
  `TauCeti.OperatorIdealFamily.gauge_imaginaryPart_le`,
  `TauCeti.OperatorIdealFamily.realPart_mem_finiteSubmodule`,
  `TauCeti.OperatorIdealFamily.imaginaryPart_mem_finiteSubmodule`,
  `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_iff_realPart_and_imaginaryPart`: gauge bounds and
  ideal closure under real and imaginary parts over `ℂ`.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open ContinuousLinearMap
open scoped ENNReal

universe u v

namespace TauCeti

namespace OperatorIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every operator-ideal family in one universe assigns the same gauge to an operator and to its
modulus `|A| = √(A† A)`. -/
@[simp]
theorem gauge_modulus (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] F) :
    Φ.gauge A.modulus = Φ.gauge A := by
  -- Polar factorization `A = W |A|` and `W† A = |A|` relates `A` and `|A|` by contractions on
  -- the left, so the two-sided ideal inequality gives `Φ(|A|) = Φ(A)`.
  obtain ⟨W, hW, hW', hWA, hW'A⟩ := exists_contraction_of_gram_eq
    (A := A.modulus) (T := A) (by rw [adjoint_modulus, modulus_comp_modulus])
  exact le_antisymm (hW'A ▸ Φ.gauge_comp_left_le_self hW' A)
    (by nth_rw 1 [← hWA]; exact Φ.gauge_comp_left_le_self hW A.modulus)

/-- Membership in the ideal of an operator-ideal family in one universe is invariant under taking
the modulus. -/
theorem modulus_mem_finiteSubmodule_iff {Φ : OperatorIdealFamily.{u, v, v} 𝕜} (A : E →L[𝕜] F) :
    A.modulus ∈ (Φ.operatorGauge E E).finiteSubmodule ↔
      A ∈ (Φ.operatorGauge E F).finiteSubmodule := by simp [OperatorGauge.mem_finiteSubmodule]

private theorem gauge_adjoint_le (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] F) :
    Φ.gauge (adjoint A) ≤ Φ.gauge A := by
  -- From `A = W |A|` and `|A| = W† A` with contractive `W†`, `A† = |A| W† = W† A W†`.
  obtain ⟨W, -, hW', hWA, hW'A⟩ := exists_contraction_of_gram_eq
    (A := A.modulus) (T := A) (by rw [adjoint_modulus, modulus_comp_modulus])
  have hadj : adjoint A = (adjoint W ∘L A) ∘L adjoint W := by
    nth_rw 1 [← hWA]; rw [adjoint_comp, adjoint_modulus, ← hW'A]
  exact hadj ▸ (Φ.gauge_comp_right_le_self _ hW').trans (Φ.gauge_comp_left_le_self hW' A)

/-- Every operator-ideal family whose sources and targets lie in one universe is invariant under
adjoints. -/
@[simp]
theorem gauge_adjoint (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] F) :
    Φ.gauge (adjoint A) = Φ.gauge A :=
  (gauge_adjoint_le Φ A).antisymm (by simpa using gauge_adjoint_le Φ (adjoint A))

/-- On endomorphisms, every operator-ideal gauge in one universe is invariant under `star`. -/
@[simp]
theorem gauge_star (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] E) :
    Φ.gauge (star A) = Φ.gauge A := by rw [star_eq_adjoint, gauge_adjoint]

/-- Membership in the ideal of an operator-ideal family in one universe is invariant under
adjoints. -/
theorem adjoint_mem_finiteSubmodule_iff {Φ : OperatorIdealFamily.{u, v, v} 𝕜} (A : E →L[𝕜] F) :
    adjoint A ∈ (Φ.operatorGauge F E).finiteSubmodule ↔
      A ∈ (Φ.operatorGauge E F).finiteSubmodule := by simp [OperatorGauge.mem_finiteSubmodule]

/-- On endomorphisms, membership in the ideal of an operator-ideal family in one universe is
invariant under `star`. -/
theorem star_mem_finiteSubmodule_iff {Φ : OperatorIdealFamily.{u, v, v} 𝕜} (A : E →L[𝕜] E) :
    star A ∈ (Φ.operatorGauge E E).finiteSubmodule ↔
      A ∈ (Φ.operatorGauge E E).finiteSubmodule := by simp [OperatorGauge.mem_finiteSubmodule]

section PosNegPart

variable [Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]

/-- In any operator-ideal family in one universe, the positive part of an endomorphism has gauge at
most that of the operator. -/
theorem gauge_posPart_le (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] E) :
    Φ.gauge A⁺ ≤ Φ.gauge A := by
  -- On the self-adjoint locus `2 • A⁺ = |A| + A`, so subadditivity, homogeneity, and
  -- `Φ(|A|) = Φ(A)` bound `Φ(A⁺)` by `Φ(A)`; outside it, `A⁺ = 0`.
  by_cases ha : IsSelfAdjoint A
  · have h2 : (2 : 𝕜) • A⁺ = A.modulus + A := by
      rw [two_smul, ← two_nsmul, ← CFC.abs_add_self A ha, modulus_eq_abs]
    have h2norm : ‖(2 : 𝕜)‖ₑ = 2 := by rw [enorm_eq_nnnorm]; norm_num
    calc Φ.gauge A⁺
        = 2⁻¹ * (2 * Φ.gauge A⁺) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
      _ = 2⁻¹ * Φ.gauge ((2 : 𝕜) • A⁺) := by rw [Φ.gauge_smul, h2norm]
      _ = 2⁻¹ * Φ.gauge (A.modulus + A) := by rw [h2]
      _ ≤ 2⁻¹ * (Φ.gauge A.modulus + Φ.gauge A) := by gcongr; exact Φ.gauge_add_le _ _
      _ = Φ.gauge A := by
          rw [gauge_modulus, ← two_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  · simp [CFC.posPart_eq_zero_of_not_isSelfAdjoint ha]

/-- In any operator-ideal family in one universe, the negative part of an endomorphism has gauge at
most that of the operator. -/
theorem gauge_negPart_le (Φ : OperatorIdealFamily.{u, v, v} 𝕜) (A : E →L[𝕜] E) :
    Φ.gauge A⁻ ≤ Φ.gauge A := by simpa using gauge_posPart_le Φ (-A)

/-- Every operator ideal in one universe is closed under taking the positive part of an
endomorphism. -/
theorem posPart_mem_finiteSubmodule {Φ : OperatorIdealFamily.{u, v, v} 𝕜} {A : E →L[𝕜] E}
    (hA : A ∈ (Φ.operatorGauge E E).finiteSubmodule) :
    A⁺ ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_posPart_le Φ A).trans_lt hA

/-- Every operator ideal in one universe is closed under taking the negative part of an
endomorphism. -/
theorem negPart_mem_finiteSubmodule {Φ : OperatorIdealFamily.{u, v, v} 𝕜} {A : E →L[𝕜] E}
    (hA : A ∈ (Φ.operatorGauge E E).finiteSubmodule) :
    A⁻ ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_negPart_le Φ A).trans_lt hA

/-- A self-adjoint endomorphism lies in the ideal of an operator-ideal family in one universe if
and only if its positive and negative parts do. -/
theorem mem_finiteSubmodule_iff_posPart_and_negPart {Φ : OperatorIdealFamily.{u, v, v} 𝕜}
    {A : E →L[𝕜] E} (hA : IsSelfAdjoint A) :
    A ∈ (Φ.operatorGauge E E).finiteSubmodule ↔
      A⁺ ∈ (Φ.operatorGauge E E).finiteSubmodule ∧
        A⁻ ∈ (Φ.operatorGauge E E).finiteSubmodule := by
  refine ⟨fun h ↦ ⟨posPart_mem_finiteSubmodule h, negPart_mem_finiteSubmodule h⟩,
    fun ⟨hp, hn⟩ ↦ ?_⟩
  rw [← CFC.posPart_sub_negPart A hA]; exact Submodule.sub_mem _ hp hn

end PosNegPart

section Complex

open scoped ComplexStarModule

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- In any operator-ideal family in one universe over `ℂ`, the real part of an endomorphism has
gauge at most that of the operator. -/
theorem gauge_realPart_le (Φ : OperatorIdealFamily.{0, v, v} ℂ) (A : G →L[ℂ] G) :
    Φ.gauge (ℜ A : G →L[ℂ] G) ≤ Φ.gauge A := by
  have h2 : ‖(2 : ℂ)⁻¹‖ₑ = 2⁻¹ := by rw [enorm_eq_nnnorm]; norm_num
  calc Φ.gauge (ℜ A : G →L[ℂ] G)
      = Φ.gauge ((2 : ℂ)⁻¹ • (A + star A)) := by
        rw [realPart_apply_coe, ← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_ofNat]
    _ = 2⁻¹ * Φ.gauge (A + star A) := by rw [Φ.gauge_smul, h2]
    _ ≤ 2⁻¹ * (Φ.gauge A + Φ.gauge (star A)) := by gcongr; exact Φ.gauge_add_le _ _
    _ = Φ.gauge A := by
        rw [gauge_star, ← two_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- In any operator-ideal family in one universe over `ℂ`, the imaginary part of an endomorphism has
gauge at most that of the operator. -/
theorem gauge_imaginaryPart_le (Φ : OperatorIdealFamily.{0, v, v} ℂ) (A : G →L[ℂ] G) :
    Φ.gauge (ℑ A : G →L[ℂ] G) ≤ Φ.gauge A := by
  simpa [enorm_eq_nnnorm] using gauge_realPart_le Φ (-Complex.I • A)

/-- Every operator ideal in one universe over `ℂ` is closed under taking the real part of an
endomorphism. -/
theorem realPart_mem_finiteSubmodule {Φ : OperatorIdealFamily.{0, v, v} ℂ} {A : G →L[ℂ] G}
    (hA : A ∈ (Φ.operatorGauge G G).finiteSubmodule) :
    (ℜ A : G →L[ℂ] G) ∈ (Φ.operatorGauge G G).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_realPart_le Φ A).trans_lt hA

/-- Every operator ideal in one universe over `ℂ` is closed under taking the imaginary part of an
endomorphism. -/
theorem imaginaryPart_mem_finiteSubmodule {Φ : OperatorIdealFamily.{0, v, v} ℂ} {A : G →L[ℂ] G}
    (hA : A ∈ (Φ.operatorGauge G G).finiteSubmodule) :
    (ℑ A : G →L[ℂ] G) ∈ (Φ.operatorGauge G G).finiteSubmodule := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hA ⊢
  exact (gauge_imaginaryPart_le Φ A).trans_lt hA

/-- An endomorphism lies in the ideal of an operator-ideal family in one universe over `ℂ` if and
only if its real and imaginary parts do. -/
theorem mem_finiteSubmodule_iff_realPart_and_imaginaryPart {Φ : OperatorIdealFamily.{0, v, v} ℂ}
    (A : G →L[ℂ] G) :
    A ∈ (Φ.operatorGauge G G).finiteSubmodule ↔
      (ℜ A : G →L[ℂ] G) ∈ (Φ.operatorGauge G G).finiteSubmodule ∧
        (ℑ A : G →L[ℂ] G) ∈ (Φ.operatorGauge G G).finiteSubmodule := by
  refine ⟨fun hA ↦ ⟨realPart_mem_finiteSubmodule hA, imaginaryPart_mem_finiteSubmodule hA⟩,
    fun ⟨hre, him⟩ ↦ ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart A]
  exact Submodule.add_mem _ hre (Submodule.smul_mem _ _ him)

end Complex

end OperatorIdealFamily

end TauCeti
