/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra
public import TauCeti.NumberTheory.Padics.Measure.Units.WeightIntegral
public import TauCeti.NumberTheory.Padics.WeightSpace.Specialization
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Integral measures on `ℤ_pˣ`, the Amice transform, and specialisation of `ℤ_p[[ℤ_pˣ]]`

This file bridges the integral-measure algebra `D(ℤ_pˣ, ℤ_p)` with the completed group algebra
`ℤ_p[[ℤ_pˣ]]`, its procyclic power-series coordinate, and evaluation at `K`-valued weights:

1. **Amice transform and procyclic power-series coordinate.** On the additive `p`-adic integers
   viewed multiplicatively (`Multiplicative ℤ_p`), Mathlib's algebra Amice transform
   `AbstractMeasure.amiceTransformₐ : D(Multiplicative ℤ_p, ℤ_p) →ₐ[ℤ_p] ℤ_p⟦X⟧` sends `δ_x` to
   `PowerSeries.binomialSeries ℤ_p x.toAdd` and is continuous from `AbstractMeasure.WeakTopology`
   to `PowerSeries.WithPiTopology`. Composing it with the procyclic completed-group-algebra
   coordinate `completedGroupAlgebra.powerSeriesCoordinate` at `ofAdd 1` recovers the canonical
   measure-to-completed-group-algebra comparison `AbstractMeasure.toCompletedGroupAlgebra`
   (`TauCeti.powerSeriesCoordinate_amiceTransformₐ`). Transporting along the logarithm isomorphism
   `TauCeti.unitsPrincipalLogEquiv p : 1 + qℤ_p ≃ₜ* Multiplicative ℤ_p` gives the corresponding
   compatibility on principal `p`-adic units (`TauCeti.toCompletedGroupAlgebra_unitsPrincipal`).

2. **Weight specialisation and bounded measure functions.** Over any complete ultrametric normed
   field `K` over `ℚ_p`, specialising `toCompletedGroupAlgebra ν` (`ν ∈ D(ℤ_pˣ, ℤ_p)`) at a weight
   `κ : WeightSpace p K` via `TauCeti.WeightSpace.specializeRingHom` agrees with integrating `κ`
   against `ν` via `TauCeti.measureFun`
   (`TauCeti.WeightSpace.specializeRingHom_toCompletedGroupAlgebra`). Consequently, assembling all
   `K`-valued specialisations into
   `TauCeti.completedMeasureFun K : ℤ_p[[ℤ_pˣ]] →+* (WeightSpace p K → K)` embeds `ℤ_p[[ℤ_pˣ]]`
   injectively into functions on `WeightSpace p K` bounded in norm by `1`, with every group element
   `[x]` attaining norm `1`.

## Main definitions

* `TauCeti.completedMeasureFun K`: the ring homomorphism
  `ℤ_p[[ℤ_pˣ]] →+* (WeightSpace p K → K)` sending `x` to `κ ↦ κ.specializeRingHom x`.

## Main results

* `AbstractMeasure.continuous_amiceTransformₐ_weak`: `amiceTransformₐ` is continuous from the weak
  topology on `D(Multiplicative ℤ_p, ℤ_p)` to the coefficientwise `p`-adic topology on `ℤ_p⟦X⟧`.
* `AbstractMeasure.amiceTransformₐ_dirac`: `amiceTransformₐ (dirac ℤ_p x)` is the binomial series
  `(1 + X) ^ x.toAdd`.
* `TauCeti.powerSeriesCoordinate_amiceTransformₐ`: the procyclic power-series coordinate on
  `ℤ_p[[Multiplicative ℤ_p]]` composed with `amiceTransformₐ` equals `toCompletedGroupAlgebra`.
* `TauCeti.toCompletedGroupAlgebra_unitsPrincipal`: compatibility of `toCompletedGroupAlgebra` on
  `D(1 + qℤ_p, ℤ_p)` with `amiceTransformₐ` along `unitsPrincipalLogEquiv p`.
* `TauCeti.WeightSpace.specializeRingHom_toCompletedGroupAlgebra`:
  `κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ`.
* `TauCeti.WeightSpace.norm_specializeRingHom_le_one`,
  `TauCeti.WeightSpace.norm_specializeRingHom_of`: `‖κ.specializeRingHom x‖ ≤ 1`, attained by group
  elements.
* `TauCeti.completedMeasureFun_injective`: `K`-valued weights jointly separate elements of
  `ℤ_p[[ℤ_pˣ]]`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3.5–3.6 and §4.
* L. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §7.1.
-/

public section

open Filter Topology AbstractMeasure ContinuousMonoidHom
open scoped AbstractMeasure PowerSeries.WithPiTopology

namespace AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

/-- The multiplicative integral Amice transform is continuous from the weak topology on
`D(Multiplicative ℤ_p, ℤ_p)` to the coefficientwise `p`-adic topology on `ℤ_p⟦X⟧`. -/
theorem continuous_amiceTransformₐ_weak :
    @Continuous _ _ (WeakTopology (X := Multiplicative ℤ_[p]) (R := ℤ_[p]) (E := ℤ_[p])) _
      (amiceTransformₐ (p := p) (R := ℤ_[p])) := by
  let : TopologicalSpace D(Multiplicative ℤ_[p], ℤ_[p]) := WeakTopology
  have heval : Continuous (fun μ : D(Multiplicative ℤ_[p], ℤ_[p]) ↦
      fun f : C(Multiplicative ℤ_[p], ℤ_[p]) ↦ μ f) :=
    continuous_induced_dom
  refine continuous_iff_continuousAt.mpr fun μ ↦
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℤ_[p] _ _ _).mpr fun n ↦ ?_
  simpa only [coeff_amiceTransformₐ, ContinuousAt, Function.comp_def] using
    ((continuous_apply (mulMahler n : C(Multiplicative ℤ_[p], ℤ_[p]))).comp heval).continuousAt
      (x := μ)

/-- The multiplicative Amice transform of a Dirac measure is the binomial series
`(1 + X) ^ x.toAdd`. -/
@[simp]
theorem amiceTransformₐ_dirac {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R] (x : Multiplicative ℤ_[p]) :
    amiceTransformₐ (dirac R x) = PowerSeries.binomialSeries R x.toAdd := by
  ext n
  simp [coeff_amiceTransformₐ, mulMahler_apply, mahler_apply]

end AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-! ### Amice transform and the procyclic power-series coordinate -/

section AmiceComparison

private theorem continuous_completedGroupAlgebraEquiv_symm_weak (Γ : Type*) [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] :
    @Continuous _ _ _ (WeakTopology (X := Γ) (R := ℤ_[p]) (E := ℤ_[p]))
      (completedGroupAlgebraEquiv (Γ := Γ) (p := p)).symm := by
  let : TopologicalSpace D(Γ, ℤ_[p]) := WeakTopology
  exact isHomeomorph_toCompletedGroupAlgebra_weak.isInducing.continuous_iff.mpr <|
    continuous_id.congr fun x ↦ by
      simp only [Function.comp_apply, id_eq, ← completedGroupAlgebraEquiv_apply,
        AlgEquiv.apply_symm_apply]

/-- **Compatibility of the Amice transform with `powerSeriesCoordinate`.** On
`D(Multiplicative ℤ_p, ℤ_p)`, applying `AbstractMeasure.amiceTransformₐ` and then the procyclic
power-series isomorphism `completedGroupAlgebra.powerSeriesCoordinate` at the canonical generator
`Multiplicative.ofAdd 1` recovers `AbstractMeasure.toCompletedGroupAlgebra`. -/
theorem powerSeriesCoordinate_amiceTransformₐ (μ : D(Multiplicative ℤ_[p], ℤ_[p])) :
    completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p) (amiceTransformₐ μ) =
      toCompletedGroupAlgebra μ := by
  let : TopologicalSpace D(Multiplicative ℤ_[p], ℤ_[p]) := WeakTopology
  let coord := completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p)
  let Φ : completedGroupAlgebra ℤ_[p] (Multiplicative ℤ_[p]) →ₐ[ℤ_[p]]
      completedGroupAlgebra ℤ_[p] (Multiplicative ℤ_[p]) :=
    (coord.toAlgHom.comp amiceTransformₐ).comp
      (completedGroupAlgebraEquiv (Γ := Multiplicative ℤ_[p]) (p := p)).symm.toAlgHom
  have hΦ_cont : Continuous Φ :=
    (completedGroupAlgebra.continuous_powerSeriesCoordinate (isProP_multiplicative_padicInt p)
      (topologicallyGenerates_ofAdd_one_padicInt p)).comp
      (continuous_amiceTransformₐ_weak.comp
        (continuous_completedGroupAlgebraEquiv_symm_weak (Multiplicative ℤ_[p])))
  have hΦ_of (g : Multiplicative ℤ_[p]) :
      Φ (completedGroupAlgebra.of ℤ_[p] (Multiplicative ℤ_[p]) g) =
        completedGroupAlgebra.of ℤ_[p] (Multiplicative ℤ_[p]) g := by
    have hdirac : (completedGroupAlgebraEquiv (Γ := Multiplicative ℤ_[p]) (p := p)).symm
        (completedGroupAlgebra.of ℤ_[p] (Multiplicative ℤ_[p]) g) = dirac ℤ_[p] g :=
      (completedGroupAlgebraEquiv (Γ := Multiplicative ℤ_[p]) (p := p)).symm_apply_eq.mpr
        (by simp)
    dsimp only [Φ, coord]
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
      hdirac, amiceTransformₐ_dirac,
      completedGroupAlgebra.powerSeriesCoordinate_binomialSeries,
      IsProP.padicPow_ofAdd_one_padicInt, ofAdd_toAdd]
  have hspan : Set.EqOn (⇑Φ) (⇑(AlgHom.id ℤ_[p]
      (completedGroupAlgebra ℤ_[p] (Multiplicative ℤ_[p]))))
      (Submodule.span ℤ_[p]
        (Set.range (completedGroupAlgebra.of ℤ_[p] (Multiplicative ℤ_[p])))) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨g, rfl⟩ := hy
      exact hΦ_of g
    | zero => simp
    | add _ _ _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  have heq : ⇑Φ = _root_.id :=
    Continuous.ext_on (completedGroupAlgebra.dense_span_range_of ℤ_[p] (Multiplicative ℤ_[p]))
      hΦ_cont continuous_id hspan
  have hμ : Φ (completedGroupAlgebraEquiv μ) = completedGroupAlgebraEquiv μ :=
    congrFun heq (completedGroupAlgebraEquiv μ)
  dsimp only [Φ, coord] at hμ
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, completedGroupAlgebraEquiv_apply] at hμ
  exact hμ

/-- Applying the inverse procyclic coordinate to `toCompletedGroupAlgebra μ` recovers the
multiplicative Amice transform `amiceTransformₐ μ`. -/
@[simp]
theorem symm_powerSeriesCoordinate_toCompletedGroupAlgebra
    (μ : D(Multiplicative ℤ_[p], ℤ_[p])) :
    (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p)).symm (toCompletedGroupAlgebra μ) =
      amiceTransformₐ μ :=
  (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p)).symm_apply_eq.mpr
    (powerSeriesCoordinate_amiceTransformₐ μ).symm

/-- **Principal-units compatibility.** Under the logarithm isomorphism
`unitsPrincipalLogEquiv p : 1 + qℤ_p ≃ₜ* Multiplicative ℤ_p`, `toCompletedGroupAlgebra` on
integral measures on `1 + qℤ_p` agrees with pushing forward along `unitsPrincipalLogEquiv p`,
taking the Amice transform, and applying the procyclic power-series coordinate. -/
theorem toCompletedGroupAlgebra_unitsPrincipal
    (μ : D(unitsPrincipal p (padicUnitsDepth p), ℤ_[p])) :
    toCompletedGroupAlgebra μ =
      completedGroupAlgebra.domCongr ℤ_[p] (unitsPrincipalLogEquiv p).symm
        (completedGroupAlgebra.powerSeriesCoordinate (isProP_multiplicative_padicInt p)
          (topologicallyGenerates_ofAdd_one_padicInt p)
          (amiceTransformₐ
            ((⟨(unitsPrincipalLogEquiv p : _ →* Multiplicative ℤ_[p]),
              (unitsPrincipalLogEquiv p).continuous⟩ :
                unitsPrincipal p (padicUnitsDepth p) →ₜ* Multiplicative ℤ_[p]).mapAlgHom μ))) := by
  rw [powerSeriesCoordinate_amiceTransformₐ, toCompletedGroupAlgebra_continuousMulEquiv,
    ← completedGroupAlgebra.domCongr_symm, AlgEquiv.symm_apply_apply]

end AmiceComparison

/-! ### Specialisation of `ℤ_p[[ℤ_pˣ]]` and bounded measure functions -/

section MeasureFunComparison

private theorem exists_one_lt_norm_of_normedAlgebra_padic (p : ℕ) [Fact p.Prime]
    (K : Type*) [SeminormedRing K] [NormedAlgebra ℚ_[p] K] [NormOneClass K] :
    ∃ x : K, 1 < ‖x‖ := by
  refine ⟨algebraMap ℚ_[p] K (p : ℚ_[p])⁻¹, ?_⟩
  rw [norm_algebraMap', norm_inv, Padic.norm_p, inv_inv]
  exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem continuous_extendCoefficients_completedGroupAlgebraEquiv_symm
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
    (f : C(ℤ_[p]ˣ, K)) :
    Continuous fun z : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ ↦
      extendCoefficients (padicIntAlgebraMap p K) norm_padicIntAlgebraMap_le_one
        ((completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm z) f := by
  let : NontriviallyNormedField K :=
    { ‹NormedField K› with non_trivial := exists_one_lt_norm_of_normedAlgebra_padic p K }
  let : TopologicalSpace D(ℤ_[p]ˣ, ℤ_[p]) := WeakTopology
  have hsymm : Continuous (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm :=
    continuous_completedGroupAlgebraEquiv_symm_weak ℤ_[p]ˣ
  have hloc (φ : LocallyConstant ℤ_[p]ˣ K) :
      Continuous fun z : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ ↦
        extendCoefficients (padicIntAlgebraMap p K) norm_padicIntAlgebraMap_le_one
          ((completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm z) φ := by
    classical
    let q : C(ℤ_[p]ˣ, φ.discreteQuotient) := ⟨_, φ.discreteQuotient.proj_continuous⟩
    let := Fintype.ofFinite φ.discreteQuotient
    have hφ : (φ : C(ℤ_[p]ˣ, K)) = (ContinuousMap.equivFnOfDiscrete.symm φ.lift).comp q := by
      ext x
      exact (congrFun φ.lift_comp_proj x).symm
    simp_rw [hφ, extendCoefficients_apply_comp_eq_sum]
    exact continuous_finsetSum _ fun a _ ↦
      continuous_const.mul <| continuous_padicIntAlgebraMap.comp <|
        ((continuous_apply a).comp (continuous_finiteProjection q)).comp hsymm
  refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨φ, hφf⟩ :=
    LocallyConstant.denseRange_toContinuousMap.exists_dist_lt f hε
  refine ⟨_, hloc φ, fun z ↦ hεu ?_⟩
  rw [dist_eq_norm, ← map_sub, ← coe_toCLMEquiv]
  refine (ContinuousLinearMap.le_opNorm _ _).trans_lt ?_
  refine (mul_le_of_le_one_left (norm_nonneg _)
    (norm_toCLMEquiv_extendCoefficients_le _ norm_padicIntAlgebraMap_le_one _)).trans_lt ?_
  rwa [dist_eq_norm] at hφf

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **Compatibility of `specializeRingHom` with `measureFun`.** Specialising the image in
`ℤ_p[[ℤ_pˣ]]` of an integral measure `ν ∈ D(ℤ_pˣ, ℤ_p)` at a weight `κ : WeightSpace p K` agrees
with integrating `κ` against `ν`. -/
@[simp]
theorem WeightSpace.specializeRingHom_toCompletedGroupAlgebra (ν : D(ℤ_[p]ˣ, ℤ_[p]))
    (κ : WeightSpace p K) :
    κ.specializeRingHom (toCompletedGroupAlgebra ν) = measureFun K ν κ := by
  let Φ : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* K :=
    (Pi.evalRingHom (fun _ : WeightSpace p K ↦ K) κ).comp
      ((measureFun K).comp (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm.toRingHom)
  have hΦ_cont : Continuous Φ :=
    (continuous_extendCoefficients_completedGroupAlgebraEquiv_symm κ.weightTest).congr fun z ↦ by
      simp [Φ, measureFun_apply]
  have hΦ_of (x : ℤ_[p]ˣ) :
      Φ (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = κ x := by
    have hdirac : (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm
        (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ x) = dirac ℤ_[p] x :=
      (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm_apply_eq.mpr (by simp)
    simp [Φ, hdirac]
  have heq : Φ = κ.specializeRingHom :=
    κ.eq_specializeRingHom_of_continuous hΦ_cont hΦ_of
  have hν : Φ (completedGroupAlgebraEquiv ν) =
      κ.specializeRingHom (completedGroupAlgebraEquiv ν) :=
    RingHom.congr_fun heq (completedGroupAlgebraEquiv ν)
  have hΦν : Φ (completedGroupAlgebraEquiv ν) = measureFun K ν κ := by
    dsimp only [Φ]
    rw [RingHom.comp_apply, RingHom.comp_apply, Pi.evalRingHom_apply]
    change measureFun K ((completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm
      (completedGroupAlgebraEquiv ν)) κ = _
    rw [AlgEquiv.symm_apply_apply]
  rw [← completedGroupAlgebraEquiv_apply, ← hν, hΦν]

/-- Every field-valued weight specialisation takes values in the closed unit ball of `K`. -/
theorem WeightSpace.norm_specializeRingHom_le_one (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)
    (κ : WeightSpace p K) :
    ‖κ.specializeRingHom x‖ ≤ 1 := by
  let : NontriviallyNormedField K :=
    { ‹NormedField K› with non_trivial := exists_one_lt_norm_of_normedAlgebra_padic p K }
  let ν := (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm x
  have hx : toCompletedGroupAlgebra ν = x := by
    rw [← completedGroupAlgebraEquiv_apply, AlgEquiv.apply_symm_apply]
  rw [← hx, WeightSpace.specializeRingHom_toCompletedGroupAlgebra]
  exact norm_measureFun_le_one ν κ

/-- Group elements in `ℤ_p[[ℤ_pˣ]]` attain norm `1` under every field-valued weight
specialisation. -/
theorem WeightSpace.norm_specializeRingHom_of (g : ℤ_[p]ˣ) (κ : WeightSpace p K) :
    ‖κ.specializeRingHom (completedGroupAlgebra.of ℤ_[p] ℤ_[p]ˣ g)‖ = 1 := by
  rw [← toCompletedGroupAlgebra_dirac, WeightSpace.specializeRingHom_toCompletedGroupAlgebra]
  exact norm_measureFun_dirac g κ

variable (K) in
/-- **The completed-group-algebra evaluation map into functions on `WeightSpace p K`.** Each element
`x ∈ ℤ_p[[ℤ_pˣ]]` goes to the bounded function `κ ↦ κ.specializeRingHom x`. -/
noncomputable def completedMeasureFun :
    completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ →+* (WeightSpace p K → K) :=
  RingHom.pi fun κ ↦ κ.specializeRingHom

@[simp]
theorem completedMeasureFun_apply (x : completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ)
    (κ : WeightSpace p K) :
    completedMeasureFun K x κ = κ.specializeRingHom x :=
  (rfl)

/-- Evaluating `toCompletedGroupAlgebra ν` at all `K`-valued weights recovers `measureFun K ν`. -/
@[simp]
theorem completedMeasureFun_toCompletedGroupAlgebra (ν : D(ℤ_[p]ˣ, ℤ_[p])) :
    completedMeasureFun K (toCompletedGroupAlgebra ν) = measureFun K ν := by
  ext κ
  exact WeightSpace.specializeRingHom_toCompletedGroupAlgebra ν κ

/-- `completedMeasureFun K` composed with `toCompletedGroupAlgebra` is `measureFun K`. -/
theorem completedMeasureFun_comp_toCompletedGroupAlgebra :
    (completedMeasureFun K).comp
        (toCompletedGroupAlgebra : D(ℤ_[p]ˣ, ℤ_[p]) →ₐ[ℤ_[p]]
          completedGroupAlgebra ℤ_[p] ℤ_[p]ˣ).toRingHom =
      measureFun K :=
  RingHom.ext completedMeasureFun_toCompletedGroupAlgebra

variable (K) in
/-- **`K`-valued weights separate elements of `ℤ_p[[ℤ_pˣ]]`.** Because `completedMeasureFun K`
transfers `TauCeti.measureFun K` along the isomorphism `completedGroupAlgebraEquiv`, it is
injective. -/
theorem completedMeasureFun_injective :
    Function.Injective (completedMeasureFun (p := p) K) := by
  intro x y hxy
  apply (completedGroupAlgebraEquiv (Γ := ℤ_[p]ˣ) (p := p)).symm.injective
  apply measureFun_injective K
  rw [← completedMeasureFun_toCompletedGroupAlgebra, ← completedMeasureFun_toCompletedGroupAlgebra,
    ← completedGroupAlgebraEquiv_apply, ← completedGroupAlgebraEquiv_apply,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, hxy]

end MeasureFunComparison

end TauCeti
