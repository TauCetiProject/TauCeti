/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.Topology.Amice
public import TauCeti.NumberTheory.Padics.Measure.Units.WeightIntegral
public import TauCeti.NumberTheory.Padics.WeightSpace.Specialization
import TauCeti.Analysis.Normed.Field.Basic

/-!
# Integral measures on `ℤ_pˣ`, principal-unit Amice coordinates, and specialisation of `ℤ_p[[ℤ_pˣ]]`

This file connects integral measures on principal units `D(1 + qℤ_p, ℤ_p)` with the procyclic
power-series coordinate via the multiplicative Amice transform on `D(Multiplicative ℤ_p, ℤ_p)`
(`TauCeti.toCompletedGroupAlgebra_unitsPrincipal`), and connects `D(ℤ_pˣ, ℤ_p)` and `ℤ_p[[ℤ_pˣ]]`
with evaluation at `K`-valued weights: over any complete ultrametric normed field `K` over `ℚ_p`,
`κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ`
(`TauCeti.WeightSpace.specializeRingHom_toCompletedGroupAlgebra`), so `completedMeasureFun K` embeds
`ℤ_p[[ℤ_pˣ]]` injectively (`TauCeti.completedMeasureFun_injective`) into functions on
`WeightSpace p K` bounded in norm by `1` (`TauCeti.WeightSpace.norm_specializeRingHom_le_one`), with
group elements attaining norm `1` (`TauCeti.WeightSpace.norm_specializeRingHom_of`).

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.5–3.6 and §4.
* L. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §7.1.
-/

public section

open Filter Topology AbstractMeasure ContinuousMonoidHom
open scoped AbstractMeasure PowerSeries.WithPiTopology

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- **Principal-units compatibility.** Under `unitsPrincipalLogEquiv p : 1 + qℤ_p ≃ₜ*
Multiplicative ℤ_p`, `toCompletedGroupAlgebra` on `D(1 + qℤ_p, ℤ_p)` agrees with pushing forward,
taking `amiceTransformₐ`, and applying `powerSeriesCoordinate`. -/
theorem toCompletedGroupAlgebra_unitsPrincipal
    (μ : D(unitsPrincipal p (padicUnitsDepth p), ℤ_[p])) :
    toCompletedGroupAlgebra μ =
      completedGroupAlgebra.domCongr ℤ_[p] (unitsPrincipalLogEquiv p).symm
        (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
          (topologicallyGenerates_ofAdd_one_padicInt p)
          (amiceTransformₐ
            ((unitsPrincipalLogEquiv p :
              unitsPrincipal p (padicUnitsDepth p) →ₜ* Multiplicative ℤ_[p]).mapAlgHom μ))) := by
  rw [powerSeriesCoordinate_amiceTransformₐ, toCompletedGroupAlgebra_continuousMulEquiv,
    ← completedGroupAlgebra.domCongr_symm, AlgEquiv.symm_apply_apply]

section MeasureFunComparison

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Compatibility of `specializeRingHom` with `measureFun`.** -/
@[simp] theorem WeightSpace.specializeRingHom_toCompletedGroupAlgebra (ν : D(ℤ_[p]ˣ, ℤ_[p]))
    (κ : WeightSpace p K) : κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ := by
  let : NontriviallyNormedField K :=
    { ‹NormedField K› with non_trivial := exists_one_lt_norm_of_normedAlgebra ℚ_[p] K }
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  let Φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K :=
    (Pi.evalRingHom (fun _ : WeightSpace p K ↦ K) κ).comp
      ((measureFun K).comp (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm.toRingHom)
  have hΦ_cont : Continuous Φ := ((continuous_extendCoefficients_apply_weak
    (norm_padicIntAlgebraMap_le_one norm_one.le)
    (continuous_padicIntAlgebraMap (continuous_algebraMap ℚ_[p] K)) κ.weightTest).comp
      (continuous_completedGroupAlgebraEquiv_symm_weak (Γ := ℤ_[p]ˣ))).congr fun z ↦ by
        simp [Φ, measureFun_apply]
  have heq := κ.eq_specializeRingHom_of_continuous hΦ_cont fun x ↦ by simp [Φ]
  rw [← completedGroupAlgebraEquiv_apply]
  simpa [Φ, -completedGroupAlgebraEquiv_apply] using
    (RingHom.congr_fun heq (completedGroupAlgebraEquiv ν)).symm

/-- Every field-valued weight specialisation takes values in the closed unit ball of `K`. -/
theorem WeightSpace.norm_specializeRingHom_le_one (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)
    (κ : WeightSpace p K) : ‖κ.specializeRingHom x‖ ≤ 1 := by
  let : NontriviallyNormedField K :=
    { ‹NormedField K› with non_trivial := exists_one_lt_norm_of_normedAlgebra ℚ_[p] K }
  rw [← toCompletedGroupAlgebra_completedGroupAlgebraEquiv_symm x,
    WeightSpace.specializeRingHom_toCompletedGroupAlgebra]
  exact norm_measureFun_le_one _ κ

/-- Group elements in `ℤ_p[[ℤ_pˣ]]` attain norm `1` under every field-valued specialisation. -/
theorem WeightSpace.norm_specializeRingHom_of (g : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    ‖κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ g)‖ = 1 := by
  rw [← toCompletedGroupAlgebra_dirac, WeightSpace.specializeRingHom_toCompletedGroupAlgebra]
  exact norm_measureFun_dirac g κ

variable (K) in
/-- **The completed-group-algebra evaluation map into functions on `WeightSpace p K`.** -/
noncomputable def completedMeasureFun :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* (WeightSpace p K → K) :=
  RingHom.pi fun κ ↦ κ.specializeRingHom

@[simp] theorem completedMeasureFun_apply (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)
    (κ : WeightSpace p K) : completedMeasureFun K x κ = κ.specializeRingHom x := (rfl)
@[simp] theorem completedMeasureFun_toCompletedGroupAlgebra (ν : D(ℤ_[p]ˣ, ℤ_[p])) :
    completedMeasureFun K (toCompletedGroupAlgebra ν) = measureFun K ν :=
  funext <| WeightSpace.specializeRingHom_toCompletedGroupAlgebra ν
theorem completedMeasureFun_comp_toCompletedGroupAlgebra :
    (completedMeasureFun K).comp (toCompletedGroupAlgebra :
      D(ℤ_[p]ˣ, ℤ_[p]) →ₐ[ℤ_[p]] completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ).toRingHom = measureFun K :=
  RingHom.ext completedMeasureFun_toCompletedGroupAlgebra

variable (K) in
/-- **`K`-valued weights separate elements of `ℤ_p[[ℤ_pˣ]]`.** -/
theorem completedMeasureFun_injective :
    Function.Injective (completedMeasureFun (p := p) K) := fun x y hxy ↦
  (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm.injective <|
    measureFun_injective K <| by
      simpa [← completedMeasureFun_toCompletedGroupAlgebra,
        ← completedGroupAlgebraEquiv_apply] using hxy

end MeasureFunComparison

end TauCeti
