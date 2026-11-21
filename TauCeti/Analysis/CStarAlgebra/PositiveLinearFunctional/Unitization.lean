/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Algebra.Algebra.Unitization
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional.Basic

/-!
# Canonical extension of positive functionals to the unitization

Every positive continuous linear functional `ω : A →P[ℂ] ℂ` on a (possibly nonunital) complex
C⋆-algebra `A` extends canonically to a positive continuous linear functional
`ω.extendUnitization : Unitization ℂ A →P[ℂ] ℂ` of the same operator norm via
`ω.extendUnitization (c, a) = c * ‖ω‖ + ω a`. For any `x = (c, a) : Unitization ℂ A`, taking the
limit along an increasing approximate unit `e` of `A` gives
`‖ω (c • e + e * a)‖ ≤ ‖ω‖ * ‖c • e + e * a‖ = ‖ω‖ * ‖(e : A⁺¹) * x‖ ≤ ‖ω‖ * ‖x‖`, so the
extension has operator norm `‖ω‖`, and positivity then follows from
`ContinuousLinearMap.monotone_iff_opNorm_eq_map_one`.

## Main definitions and results

* `PositiveContinuousLinearMap.extendUnitization`: the canonical norm-preserving extension of
  `ω : A →P[ℂ] ℂ` to `Unitization ℂ A →P[ℂ] ℂ`.
* `PositiveContinuousLinearMap.extendUnitization_apply`, `extendUnitization_inr`,
  `extendUnitization_one`, `extendUnitization_zero`, `extendUnitization_add`,
  `opNorm_extendUnitization`, and `extendUnitization_comp_inr`: evaluation, additivity, and norm
  preservation of `extendUnitization`.
* `PositiveContinuousLinearMap.eq_extendUnitization_iff`: universal characterization showing that
  `ω.extendUnitization` is the unique norm-preserving positive extension of `ω` to
  `Unitization ℂ A`.

## References

* B. Blackadar, *Operator Algebras*, II.6.2.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.3.9.
-/

public section

noncomputable section

open Filter Topology Unitization
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The underlying continuous linear functional of `extendUnitization`: `x ↦ x.fst * ‖ω‖ + ω x.snd`.
It has operator norm bounded by `‖ω‖`, hence equal to `‖ω‖` since it sends `1` to `‖ω‖`. -/
private def extendUnitizationCLM (ω : A →P[ℂ] ℂ) : Unitization ℂ A →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd
      map_add' := fun x y => by
        simp only [Unitization.fst_add, Unitization.snd_add, map_add]
        ring
      map_smul' := fun c x => by
        simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul, smul_eq_mul,
          RingHom.id_apply]
        ring }
    ‖(ω : A →L[ℂ] ℂ)‖
    fun x => by
      have hl := CStarAlgebra.increasingApproximateUnit A
      have hconv : Tendsto (fun e : A => x.fst * ω e + ω (e * x.snd))
          (CStarAlgebra.approximateUnit A) (𝓝 (x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd)) :=
        ((ω.tendsto_nhds_opNorm hl).const_mul x.fst).add
          ((ω.continuous.tendsto x.snd).comp (hl.tendsto_mul_right x.snd))
      refine le_of_tendsto (hx := hl.neBot) hconv.norm ?_
      filter_upwards [hl.eventually_norm] with e he
      have hmul : ((x.fst • e + e * x.snd : A) : A⁺¹) = (e : A⁺¹) * x :=
        (Unitization.inr_mul_eq_inr e x).symm
      have hval : x.fst * ω e + ω (e * x.snd) = ω (x.fst • e + e * x.snd) := by
        simp [map_add, map_smul]
      calc ‖x.fst * ω e + ω (e * x.snd)‖
          = ‖(ω : A →L[ℂ] ℂ) (x.fst • e + e * x.snd)‖ := by
            rw [hval, PositiveContinuousLinearMap.coe_toContinuousLinearMap]
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x.fst • e + e * x.snd‖ := (ω : A →L[ℂ] ℂ).le_opNorm _
        _ = ‖(ω : A →L[ℂ] ℂ)‖ * ‖(e : A⁺¹) * x‖ := by
          rw [← Unitization.norm_inr (𝕜 := ℂ), hmul]
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * (‖(e : A⁺¹)‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ‖(ω : A →L[ℂ] ℂ)‖ * ‖x‖ := by
          rw [Unitization.norm_inr]
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg x) he) (norm_nonneg _)

private theorem opNorm_extendUnitizationCLM (ω : A →P[ℂ] ℂ) :
    ‖extendUnitizationCLM ω‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  refine le_antisymm (LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _) ?_
  have h1 : extendUnitizationCLM ω 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    simp [extendUnitizationCLM]
  have hle := (extendUnitizationCLM ω).le_opNorm 1
  rw [h1, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at hle
  have hnorm1 : ‖(1 : Unitization ℂ A)‖ = 1 := norm_one
  rwa [hnorm1, mul_one] at hle

/-- The canonical norm-preserving extension of a positive continuous linear functional
`ω : A →P[ℂ] ℂ` to `Unitization ℂ A`, given by `x ↦ x.fst * ‖ω‖ + ω x.snd`. -/
def extendUnitization (ω : A →P[ℂ] ℂ) : Unitization ℂ A →P[ℂ] ℂ :=
  { toContinuousLinearMap := extendUnitizationCLM ω
    monotone' := (ContinuousLinearMap.monotone_iff_opNorm_eq_map_one
      (f := extendUnitizationCLM ω)).mpr <| by
        rw [opNorm_extendUnitizationCLM]
        simp [extendUnitizationCLM] }

/-- Explicit evaluation formula for `ω.extendUnitization`. -/
theorem extendUnitization_apply (ω : A →P[ℂ] ℂ) (x : Unitization ℂ A) :
    ω.extendUnitization x = x.fst * (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) + ω x.snd :=
  (rfl)

/-- `ω.extendUnitization` agrees with `ω` on elements of `A`. -/
@[simp]
theorem extendUnitization_inr (ω : A →P[ℂ] ℂ) (a : A) :
    ω.extendUnitization (a : Unitization ℂ A) = ω a := by
  simp [extendUnitization_apply]

/-- `ω.extendUnitization` evaluates to `‖ω‖` at `1`. -/
@[simp]
theorem extendUnitization_one (ω : A →P[ℂ] ℂ) :
    ω.extendUnitization 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
  simp [extendUnitization_apply]

/-- Extending the zero functional yields the zero functional on `Unitization ℂ A`. -/
@[simp]
theorem extendUnitization_zero :
    (0 : A →P[ℂ] ℂ).extendUnitization = 0 := by
  ext x
  simp [extendUnitization_apply, PositiveContinuousLinearMap.toContinuousLinearMap_zero]

/-- The canonical unitization extension is additive on positive continuous linear functionals. -/
@[simp]
theorem extendUnitization_add (ω₁ ω₂ : A →P[ℂ] ℂ) :
    (ω₁ + ω₂).extendUnitization = ω₁.extendUnitization + ω₂.extendUnitization := by
  ext x
  simp only [extendUnitization_apply, PositiveContinuousLinearMap.opNorm_add,
    Complex.ofReal_add, add_apply]
  ring

/-- The canonical unitization extension preserves the operator norm. -/
@[simp]
theorem opNorm_extendUnitization (ω : A →P[ℂ] ℂ) :
    ‖(ω.extendUnitization : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ :=
  opNorm_extendUnitizationCLM ω

/-- Restricting `ω.extendUnitization` along `Unitization.inrNonUnitalStarAlgHom ℂ A` recovers
`ω`. -/
@[simp]
theorem extendUnitization_comp_inr (ω : A →P[ℂ] ℂ) :
    ω.extendUnitization.comp (.ofClass (Unitization.inrNonUnitalStarAlgHom ℂ A)) = ω := by
  ext a
  simp

/-- Universal characterization of `ω.extendUnitization`: a positive continuous linear functional
on `Unitization ℂ A` equals `ω.extendUnitization` if and only if it restricts to `ω` on `A` and
has the same operator norm as `ω`. -/
theorem eq_extendUnitization_iff {ω : A →P[ℂ] ℂ} {ψ : Unitization ℂ A →P[ℂ] ℂ} :
    ψ = ω.extendUnitization ↔
      (∀ a : A, ψ (a : Unitization ℂ A) = ω a) ∧
        ‖(ψ : Unitization ℂ A →L[ℂ] ℂ)‖ = ‖(ω : A →L[ℂ] ℂ)‖ := by
  refine ⟨fun h => h ▸ ⟨ω.extendUnitization_inr, ω.opNorm_extendUnitization⟩,
    fun ⟨hinr, hnorm⟩ => ?_⟩
  have h1 : ψ 1 = (‖(ω : A →L[ℂ] ℂ)‖ : ℂ) := by
    rw [← hnorm, ← PositiveContinuousLinearMap.ofReal_opNorm_eq_map_one]
  ext x
  calc ψ x
      = ψ (x.fst • 1 + (x.snd : Unitization ℂ A)) := by
        rw [Unitization.fst_smul_one_add_inr_snd]
    _ = x.fst • ψ 1 + ψ (x.snd : Unitization ℂ A) := by rw [map_add, map_smul]
    _ = ω.extendUnitization x := by
        rw [smul_eq_mul, h1, hinr, extendUnitization_apply]

end PositiveContinuousLinearMap

end
