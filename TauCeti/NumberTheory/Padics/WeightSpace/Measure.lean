/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import TauCeti.NumberTheory.Padics.Measure.CharacterIntegral
public import TauCeti.NumberTheory.Padics.Measure.MahlerDuality
public import TauCeti.NumberTheory.Padics.Measure.Weight
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic

/-!
# Amice expansions of measure functions on weight discs

Twist a measure on the p-adic units by a finite character and push it to `ℤ_p` along the
principal-unit coordinate. Its Amice coefficients give the expansion of the character integral
on the disc indexed by that finite character. This construction uses the same unit decomposition
at odd primes and at two.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Remark 3.47.
-/

public noncomputable section

open ContinuousMonoidHom Filter TauCeti TauCeti.WeightSpace
open scoped AbstractMeasure ENNReal Topology

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime] {K : Type*}

section Ring

variable [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

private def principalCoordinate (p : ℕ) [Fact p.Prime] : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun u ↦ (padicIntUnitsEquivZModUnitsProd p u).2.toAdd,
    continuous_toAdd.comp (padicIntUnitsEquivZModUnitsProd p).continuous.snd⟩

private def finiteCharacterTest (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) :
    C(ℤ_[p]ˣ, K) :=
  ⟨fun u ↦ η (padicIntUnitsEquivZModUnitsProd p u).1,
    Units.continuous_val.comp <|
      continuous_of_discreteTopology.comp (padicIntUnitsEquivZModUnitsProd p).continuous.fst⟩

/-- The linear map that twists a measure by the finite character `η` and pushes it to `ℤ_p`
along the principal-unit coordinate. The resulting Amice transform expands the character
integral on the weight disc with finite character `η`. -/
def weightDiscMeasure (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) :
    D(ℤ_[p]ˣ, K) →ₗ[K] D(ℤ_[p], K) :=
  (map (principalCoordinate p)).comp (weight (finiteCharacterTest η))

/-- Integrate a principal-coordinate test function against the original measure after multiplying
by the finite character. -/
theorem weightDiscMeasure_apply (μ : D(ℤ_[p]ˣ, K))
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) (f : C(ℤ_[p], K)) :
    weightDiscMeasure η μ f = μ ⟨
      fun u ↦ (η (padicIntUnitsEquivZModUnitsProd p u).1 : K) *
        f (padicIntUnitsEquivZModUnitsProd p u).2.toAdd,
      by
        exact (finiteCharacterTest η).continuous.mul
          (f.continuous.comp (principalCoordinate p).continuous)⟩ := by
  rw [weightDiscMeasure, LinearMap.comp_apply, map_apply, weight_apply]
  apply congrArg μ
  ext u
  simp [finiteCharacterTest, principalCoordinate]

/-- A Dirac measure moves to the principal coordinate and acquires its finite-character value
as coefficient. -/
@[simp]
theorem weightDiscMeasure_dirac (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) (u : ℤ_[p]ˣ) :
    weightDiscMeasure η (dirac K u) =
      (η (padicIntUnitsEquivZModUnitsProd p u).1 : K) •
        dirac K (padicIntUnitsEquivZModUnitsProd p u).2.toAdd := by
  ext f
  simp [weightDiscMeasure_apply, smul_eq_mul]

end Ring

section Amice

variable [NormedCommRing K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- The character integral at coordinate `t` is the sum of the Amice series of the twisted
principal-coordinate measure at `t`. -/
theorem hasSum_weightDiscMeasure_amiceTransform (μ : D(ℤ_[p]ˣ, K))
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) {t : K}
    (ht : Tendsto (t ^ ·) atTop (𝓝 0)) :
    HasSum (fun n ↦ (weightDiscMeasure η μ).amiceTransform.coeff n * t ^ n)
      ((ofCoord η t ht).weightTest.characterIntegralAlgHom μ) := by
  let ν := weightDiscMeasure η μ
  have heval : ν (PadicInt.mahlerSeries (t ^ ·)) =
      (ofCoord η t ht).weightTest.characterIntegralAlgHom μ := by
    rw [weightDiscMeasure_apply, characterIntegralAlgHom_apply]
    apply congrArg μ
    ext u
    simp [PadicInt.coe_addChar_of_value_at_one]
  simpa only [PadicInt.mahlerEquiv_apply, PadicInt.fwdDiff_mahlerSeries ht, mul_comm, heval, ν]
    using ν.hasSum_mahlerEquiv_mul_coeff_amiceTransform (PadicInt.mahlerSeries (t ^ ·))

end Amice

variable [NontriviallyNormedField K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- The character integral on a fixed finite-character disc has an analytic extension defined on
the open unit ball. -/
theorem exists_analyticOnNhd_weightDisc (μ : D(ℤ_[p]ˣ, K))
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) :
    ∃ f : K → K, AnalyticOnNhd K f (Metric.ball 0 1) ∧
      ∀ (t : K) (ht : ‖t‖ < 1),
        f t = characterIntegralAlgHom
          (ofCoord η t (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)).weightTest μ := by
  let ν := weightDiscMeasure η μ
  let c := fun n ↦ ν.amiceTransform.coeff n
  let P := FormalMultilinearSeries.ofScalars K c
  refine ⟨P.sum, P.analyticOnNhd.mono ?_, fun t ht ↦ ?_⟩
  · have hP : 1 ≤ P.radius := by
      simpa using P.le_radius_of_bound ‖toCLMEquiv ν‖ (r := 1) (fun n ↦ by
        simpa only [NNReal.coe_one, one_pow, mul_one, P,
          FormalMultilinearSeries.ofScalars_norm] using
          ν.norm_coeff_amiceTransform_le (fun g ↦ by
            simpa only [coe_toCLMEquiv] using (toCLMEquiv ν).le_opNorm g) n)
    have hball : Metric.eball (0 : K) 1 = Metric.ball 0 1 := by
      simpa only [ENNReal.ofReal_one] using Metric.eball_ofReal (x := (0 : K)) (ε := 1)
    rw [← hball]
    exact Metric.eball_subset_eball hP
  · simp only [P, FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul]
    exact
      (μ.hasSum_weightDiscMeasure_amiceTransform η
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht)).tsum_eq

end AbstractMeasure
