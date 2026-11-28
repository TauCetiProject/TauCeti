/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra.Amice
public import TauCeti.NumberTheory.Padics.Measure.Units.WeightIntegral
public import TauCeti.NumberTheory.Padics.WeightSpace.PadicComplex
public import TauCeti.NumberTheory.Padics.WeightSpace.Specialization
import TauCeti.Analysis.Normed.Field.Basic

/-!
# Integral measures on `ℤ_pˣ`, principal-unit Amice coordinates, and specialisation of `ℤ_p[[ℤ_pˣ]]`

This file connects integral measures on principal units `D(1 + qℤ_p, ℤ_p)` with the procyclic
power-series coordinate via the multiplicative Amice transform on `D(Multiplicative ℤ_p, ℤ_p)`
(`TauCeti.toCompletedGroupAlgebra_unitsPrincipal`), and connects `D(ℤ_pˣ, ℤ_p)` and `ℤ_p[[ℤ_pˣ]]`
with evaluation at `K`-valued weights:
* Over any complete ultrametric normed field `K` over `ℚ_p`,
  `κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ`
  (`TauCeti.WeightSpace.specializeRingHom_toCompletedGroupAlgebra`), so `completedMeasureFun K`
  embeds `ℤ_p[[ℤ_pˣ]]` injectively (`TauCeti.completedMeasureFun_injective`) into functions on
  `WeightSpace p K` bounded in norm by `1` (`TauCeti.WeightSpace.norm_specializeRingHom_le_one`),
  with group elements attaining norm `1` (`TauCeti.WeightSpace.norm_specializeRingHom_of`).
* Over `ℂ_p`, every weight `κ : WeightSpace p ℂ_p` restricts to `𝓞_ℂ_p`
  (`TauCeti.WeightSpace.toPadicComplexInt`), and by adic uniqueness its continuous
  `ℤ_p`-algebra specialisation `κ.toPadicComplexInt.adicSpecialize : ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] 𝓞_ℂ_p`
  coincides with the unit-ball factorisation of `κ.specializeRingHom`
  (`TauCeti.WeightSpace.toRingHom_adicSpecialize_toPadicComplexInt`), recovering `measureFun ℂ_p`
  after inclusion into `ℂ_p`
  (`TauCeti.WeightSpace.coe_adicSpecialize_toPadicComplexInt_toCompletedGroupAlgebra`).
* On arbitrary bounded measures `D(ℤ_pˣ, K)` valued in a separably closed Hausdorff topological
  field `K` of characteristic zero (such as `ℂ_p`), integration against weights defines
  `TauCeti.measurePairing K : D(ℤ_pˣ, K) →ₐ[K] (WeightSpace p K → K)`, which is injective
  (`TauCeti.measurePairing_injective`); finite-order weights already separate measures
  (`TauCeti.eq_of_forall_isOfFinOrder_characterIntegralAlgHom_weightTest_eq`).

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
  rw [TauCeti.powerSeriesCoordinate_amiceTransformₐ, toCompletedGroupAlgebra_continuousMulEquiv,
    ← completedGroupAlgebra.domCongr_symm, AlgEquiv.symm_apply_apply]

section MeasureFunComparison

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Compatibility of `specializeRingHom` with `measureFun`.** -/
@[simp] theorem WeightSpace.specializeRingHom_toCompletedGroupAlgebra (ν : D(ℤ_[p]ˣ, ℤ_[p]))
    (κ : WeightSpace p K) : κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ := by
  let : NontriviallyNormedField K := NormedAlgebra.nontriviallyNormedField ℚ_[p] K
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
  have hval := RingHom.congr_fun heq (toCompletedGroupAlgebra ν)
  dsimp only [Φ] at hval
  rw [RingHom.comp_apply, Pi.evalRingHom_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    completedGroupAlgebraEquiv_symm_toCompletedGroupAlgebra] at hval
  exact hval.symm

/-- Every field-valued weight specialisation takes values in the closed unit ball of `K`. -/
theorem WeightSpace.norm_specializeRingHom_le_one (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)
    (κ : WeightSpace p K) : ‖κ.specializeRingHom x‖ ≤ 1 := by
  let : NontriviallyNormedField K := NormedAlgebra.nontriviallyNormedField ℚ_[p] K
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
    Function.Injective (completedMeasureFun (p := p) K) := by
  intro x y hxy
  refine (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm.injective
    (measureFun_injective K ?_)
  rw [← completedMeasureFun_toCompletedGroupAlgebra,
    ← completedMeasureFun_toCompletedGroupAlgebra,
    toCompletedGroupAlgebra_completedGroupAlgebraEquiv_symm,
    toCompletedGroupAlgebra_completedGroupAlgebraEquiv_symm]
  exact hxy

end MeasureFunComparison

section AdicPadicComplex

/-- Every `ℂ_p`-valued weight specialisation takes values in `𝓞_ℂ_p`. -/
theorem WeightSpace.specializeRingHom_mem_padicComplexInt (κ : WeightSpace p ℂ_[p])
    (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) : κ.specializeRingHom x ∈ 𝓞_ℂ_[p] :=
  PadicComplexInt.mem_iff_norm_le_one.mpr (κ.norm_specializeRingHom_le_one x)

/-- Under `PadicComplex.padicIntAlgebra p`, the adic specialisation of `κ.toPadicComplexInt` into
`𝓞_ℂ_p` agrees with the unit-ball factorisation of `κ.specializeRingHom`. -/
theorem WeightSpace.toRingHom_adicSpecialize_toPadicComplexInt (κ : WeightSpace p ℂ_[p]) :
    letI := PadicComplex.padicIntAlgebra p
    haveI := PadicComplex.continuousSMul_padicIntAlgebra p
    κ.toPadicComplexInt.adicSpecialize.toRingHom =
      κ.specializeRingHom.codRestrict 𝓞_ℂ_[p] κ.specializeRingHom_mem_padicComplexInt := by
  let := PadicComplex.padicIntAlgebra p
  have := PadicComplex.continuousSMul_padicIntAlgebra p
  let Φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →ₐ[ℤ_[p]] 𝓞_ℂ_[p] :=
    { κ.specializeRingHom.codRestrict 𝓞_ℂ_[p] κ.specializeRingHom_mem_padicComplexInt with
      commutes' a := Subtype.ext <| by
        simp [PadicComplex.algebraMap_padicIntAlgebra_apply, padicIntAlgebraMap_apply] }
  have hΦ : Continuous Φ := κ.continuous_specializeRingHom.subtype_mk _
  exact congrArg AlgHom.toRingHom
    (WeightSpace.eq_adicSpecialize_of_continuous hΦ κ.toPadicComplexInt fun x ↦
      Subtype.ext <| by simp [Φ]).symm

/-- Applying the adic specialisation `κ.toPadicComplexInt.adicSpecialize : ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p]
𝓞_ℂ_p` and including into `ℂ_p` recovers `κ.specializeRingHom`. -/
theorem WeightSpace.coe_adicSpecialize_toPadicComplexInt (κ : WeightSpace p ℂ_[p])
    (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ) :
    letI := PadicComplex.padicIntAlgebra p
    haveI := PadicComplex.continuousSMul_padicIntAlgebra p
    ((κ.toPadicComplexInt.adicSpecialize x : 𝓞_ℂ_[p]) : ℂ_[p]) = κ.specializeRingHom x := by
  let := PadicComplex.padicIntAlgebra p
  have := PadicComplex.continuousSMul_padicIntAlgebra p
  exact congrArg Subtype.val <|
    RingHom.congr_fun κ.toRingHom_adicSpecialize_toPadicComplexInt x

/-- **Adic specialisation compatibility with `measureFun`.** For an integral measure
`ν ∈ D(ℤ_pˣ, ℤ_p)` and a `ℂ_p`-valued weight `κ`, evaluating the unique continuous `ℤ_p`-algebra
homomorphism `κ.toPadicComplexInt.adicSpecialize : ℤ_p[[ℤ_pˣ]] →ₐ[ℤ_p] 𝓞_ℂ_p` at
`toCompletedGroupAlgebra ν` and including into `ℂ_p` gives `measureFun ℂ_p ν κ`. -/
theorem WeightSpace.coe_adicSpecialize_toPadicComplexInt_toCompletedGroupAlgebra
    (ν : D(ℤ_[p]ˣ, ℤ_[p])) (κ : WeightSpace p ℂ_[p]) :
    letI := PadicComplex.padicIntAlgebra p
    haveI := PadicComplex.continuousSMul_padicIntAlgebra p
    ((κ.toPadicComplexInt.adicSpecialize (toCompletedGroupAlgebra ν) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      measureFun ℂ_[p] ν κ := by
  let := PadicComplex.padicIntAlgebra p
  have := PadicComplex.continuousSMul_padicIntAlgebra p
  rw [κ.coe_adicSpecialize_toPadicComplexInt, WeightSpace.specializeRingHom_toCompletedGroupAlgebra]

end AdicPadicComplex

section MeasurePairing

variable (K : Type*) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

/-- **The weight character pairing** sending a bounded measure `μ ∈ D(ℤ_pˣ, K)` to the function
`κ ↦ μ(κ)` on `K`-valued weights, as a `K`-algebra homomorphism. -/
noncomputable def measurePairing : D(ℤ_[p]ˣ, K) →ₐ[K] (WeightSpace p K → K) :=
  AlgHom.pi fun κ ↦ κ.weightTest.characterIntegralAlgHom

@[simp]
theorem measurePairing_apply (μ : D(ℤ_[p]ˣ, K)) (κ : WeightSpace p K) :
    measurePairing K μ κ = κ.weightTest.characterIntegralAlgHom μ :=
  (rfl)

/-- On coefficient-extended integral measures, `measurePairing` recovers `measureFun`. -/
theorem measurePairing_extendCoefficients {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K]
    [IsUltrametricDist K] [CompleteSpace K] (ν : D(ℤ_[p]ˣ, ℤ_[p])) :
    measurePairing K
        (extendCoefficients (padicIntAlgebraMap p K) (norm_padicIntAlgebraMap_le_one norm_one.le)
          ν) =
      measureFun K ν := by
  ext κ
  simp [measureFun_apply]

/-- Over a separably closed Hausdorff topological field `K` of characteristic zero (such as `ℂ_p`),
finite-order weights separate bounded `K`-valued measures on `ℤ_pˣ`. -/
theorem eq_of_forall_isOfFinOrder_characterIntegralAlgHom_weightTest_eq {K : Type*} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] [CharZero K] [IsSepClosed K]
    {μ ν : D(ℤ_[p]ˣ, K)}
    (h : ∀ κ : WeightSpace p K, IsOfFinOrder κ →
      κ.weightTest.characterIntegralAlgHom μ = κ.weightTest.characterIntegralAlgHom ν) :
    μ = ν :=
  eq_of_forall_isOfFinOrder_characterIntegralAlgHom_eq_of_isSepClosed
    fun (κ : WeightSpace p K) hκ ↦ by
      have htest :
          (ContinuousMonoidHom.comp ⟨Units.coeHom K, Units.continuous_val⟩ κ : C(ℤ_[p]ˣ, K)) =
            (κ.weightTest : C(ℤ_[p]ˣ, K)) :=
        ContinuousMap.ext fun x ↦ (κ.weightTest_apply x).symm
      simpa only [characterIntegralAlgHom_apply, htest] using h κ hκ

/-- **`K`-valued weights separate bounded `K`-valued measures on `ℤ_pˣ`** for every separably
closed Hausdorff topological field `K` of characteristic zero (in particular `K = ℂ_p`). -/
theorem measurePairing_injective (K : Type*) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] [CharZero K] [IsSepClosed K] :
    Function.Injective (measurePairing (p := p) K) := fun _ _ hμν ↦
  eq_of_forall_isOfFinOrder_characterIntegralAlgHom_weightTest_eq fun κ _ ↦
    congrFun hμν κ

example :
    Function.Injective fun (μ : D(ℤ_[p]ˣ, ℂ_[p])) (κ : WeightSpace p ℂ_[p]) ↦
      κ.weightTest.characterIntegralAlgHom μ :=
  measurePairing_injective ℂ_[p]

end MeasurePairing

end TauCeti
