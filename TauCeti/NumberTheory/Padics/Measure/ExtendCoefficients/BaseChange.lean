/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import TauCeti.NumberTheory.Padics.Measure.BaseChange.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
import TauCeti.NumberTheory.Padics.Measure.IntegralUnitBall

/-!
# Compatibility of finite projective base change with unit-ball coefficient extension

Let `X` be a profinite space, `R` a topological commutative ring, `O` a topological `R`-algebra
carrying the `R`-module topology (`IsModuleTopology R O`), and `j : O →+* K` a ring homomorphism
into the closed unit ball of a complete ultrametric field `K`. Two operations move measures across
the diagram `R → O → K`:

* when `O` is finitely generated and projective over `R`, `AbstractMeasure.extendScalars O :
  D(X, R) →ₛₗ[algebraMap R O] D(X, O)` and its tensor lift
  `AbstractMeasure.baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`;
* `AbstractMeasure.extendCoefficients j hj : D(X, O) →+ D(X, K)`, extending integral coefficients
  into `K` via locally constant functions and ultrametric completion.

This file proves that these constructions are compatible without assuming continuity of `j`:

* for finite projective `O`, `extendCoefficients j hj (extendScalars O μ)` equals the coefficient
  extension of `μ` along `j.comp (algebraMap R O)`
  (`AbstractMeasure.extendCoefficients_extendScalars`), `extendCoefficients_baseChange_tmul` gives
  the formula on pure tensors, `extendCoefficients_baseChange` lifts this to an equality on all of
  `O ⊗[R] D(X, R)` using the `O`-action through `j`, and for an `R`-algebra map `j : O →ₐ[R] K`
  into the closed unit ball it equals the extension along `algebraMap R K`
  (`AbstractMeasure.extendCoefficients_algHom_extendScalars`);
* in any finite `R`-basis `b` of `O`, the extension of every `ν ∈ D(X, O)` decomposes via the
  coordinate retractions `AbstractMeasure.mapScalars (b.coord i) ν`
  (`AbstractMeasure.extendCoefficients_eq_sum_basis`);
* on `ℤ_p`, `AbstractMeasure.amiceTransform_extendCoefficients_baseChange` identifies the Amice
  transform of `extendCoefficients j hj (baseChangeLinearEquiv O z)` with the tensor lift of
  `PowerSeries.map (algebraMap ℤ_[p] K) ∘ amiceTransform`;
* on a profinite topological monoid `G`, extended character integration
  `ContinuousMonoidHom.extendedCharacterRingHom` decomposes correspondingly in any finite `R`-basis
  `b` of `O` (`ContinuousMonoidHom.extendedCharacterRingHom_eq_sum_basis`).

Combined with `@[simp]` lemmas `AbstractMeasure.baseChangeLinearEquiv_tmul`,
`AbstractMeasure.coe_baseChangeAlgEquiv`, `AbstractMeasure.extendCoefficients_smul`,
`AbstractMeasure.amiceTransform_extendScalars`, and
`AbstractMeasure.amiceTransform_extendCoefficients_algebraMap`, `simp` automatically simplifies
coefficient extensions, character evaluations, and Amice transforms on base-changed pure tensors.

## References

* J. Rodrigues Jacinto and C. Williams,
  [*An introduction to p-adic L-functions*](https://doi.org/10.2140/ent.2025.4.101),
  Essential Number Theory **4** (2025), no. 1, 101–216, Proposition 3.16 and Remark 3.28.
-/

public noncomputable section

open ContinuousMap
open scoped PowerSeries TensorProduct

namespace AbstractMeasure

section ProfiniteSpace

variable {X R O K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Extending scalars from `R` to `O` and then extending coefficients along `j : O →+* K` into the
closed unit ball agrees with extending coefficients directly along `j.comp (algebraMap R O)`,
without assuming continuity of `j`. -/
@[simp]
theorem extendCoefficients_extendScalars (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(X, R)) :
    extendCoefficients j hj (extendScalars O μ) =
      extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ :=
  finiteProjection_ext _ _ fun q ↦ by
    ext a
    simp

/-- Extending coefficients of a base-changed pure tensor `a ⊗ₜ μ` scales the coefficient extension
of `μ` by `j a`. -/
theorem extendCoefficients_baseChange_tmul (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O)
    (μ : D(X, R)) :
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  rw [baseChangeLinearEquiv_tmul, extendCoefficients_smul, extendCoefficients_extendScalars]

/-- Extending coefficients of an arbitrary base-changed measure `baseChangeLinearEquiv O z`
equals the `O`-linear tensor lift of coefficient extension along `j.comp (algebraMap R O)`, with
`O` acting on `D(X, K)` through `j`. -/
theorem extendCoefficients_baseChange (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (z : O ⊗[R] D(X, R)) :
    letI : Module O D(X, K) := Module.compHom D(X, K) j
    letI : Module R D(X, K) := Module.restrictScalars R O D(X, K)
    letI : IsScalarTower R O D(X, K) := IsScalarTower.restrictScalars R O D(X, K)
    extendCoefficients j hj (baseChangeLinearEquiv O z) =
      LinearMap.liftBaseChange O
        { toFun := extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r))
          map_add' := map_add _
          map_smul' := fun r μ ↦ by
            rw [RingHom.id_apply, extendCoefficients_smul]
            rfl } z := by
  let : Module O D(X, K) := Module.compHom D(X, K) j
  let : Module R D(X, K) := Module.restrictScalars R O D(X, K)
  let : IsScalarTower R O D(X, K) := IsScalarTower.restrictScalars R O D(X, K)
  induction z using TensorProduct.inductionOn with
  | tmul a μ =>
    rw [LinearMap.liftBaseChange_tmul]
    exact extendCoefficients_baseChange_tmul j hj a μ
  | add z₁ z₂ hz₁ hz₂ =>
    simp only [map_add, hz₁, hz₂]

/-- When `K` is an `R`-algebra and `j : O →ₐ[R] K` is an `R`-algebra homomorphism into the closed
unit ball, extending `extendScalars O μ` along `j` agrees with extending `μ` along
`algebraMap R K`. -/
@[simp]
theorem extendCoefficients_algHom_extendScalars [Algebra R K] (j : O →ₐ[R] K)
    (hj : ∀ a, ‖j a‖ ≤ 1) (μ : D(X, R)) :
    extendCoefficients (j : O →+* K) hj (extendScalars O μ) =
      extendCoefficients (algebraMap R K)
        (fun r ↦ by simpa only [AlgHom.commutes] using hj (algebraMap R O r)) μ :=
  (extendCoefficients_extendScalars (j : O →+* K) hj μ).trans <| by
    simp only [j.comp_algebraMap]

omit [Module.Projective R O] [Module.Finite R O] in
/-- In any finite `R`-basis `b` of `O`, the coefficient extension of an arbitrary `O`-valued
measure `ν ∈ D(X, O)` decomposes as a `K`-linear combination of the extensions of its `R`-valued
coordinate retractions `mapScalars (b.coord i) ν`. -/
theorem extendCoefficients_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(X, O)) :
    extendCoefficients j hj ν =
      ∑ i : ι, j (b i) •
        extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r))
          (mapScalars (b.coord i) ν) := by
  have : Module.Projective R O := Module.Projective.of_basis b
  have : Module.Finite R O := Module.Finite.of_basis b
  have hν : ν = baseChangeLinearEquiv O (∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν) := by
    rw [← baseChangeLinearEquiv_symm_apply b ν, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hν]
  simp [map_sum]

end ProfiniteSpace

section Amice

variable {p : ℕ} [Fact p.Prime]
  {O : Type*} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra ℤ_[p] O] [IsModuleTopology ℤ_[p] O] [Module.Projective ℤ_[p] O] [Module.Finite ℤ_[p] O]
  {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [Algebra ℤ_[p] K] [ContinuousSMul ℤ_[p] K]

/-- On an arbitrary base-changed measure `baseChangeLinearEquiv O z` over `ℤ_p`, taking the Amice
transform after extending coefficients along a `ℤ_p`-algebra homomorphism `j : O →ₐ[ℤ_[p]] K` into
the closed unit ball agrees with the `O`-linear tensor lift of `PowerSeries.map (algebraMap ℤ_[p] K)
∘ amiceTransform`, with `O` acting on `K⟦X⟧` through `j`. -/
theorem amiceTransform_extendCoefficients_baseChange (j : O →ₐ[ℤ_[p]] K)
    (hj : ∀ a, ‖j a‖ ≤ 1) (z : O ⊗[ℤ_[p]] D(ℤ_[p], ℤ_[p])) :
    letI : Module O K⟦X⟧ := Module.compHom K⟦X⟧ (j : O →+* K)
    letI : IsScalarTower ℤ_[p] O K⟦X⟧ := ⟨fun r a F ↦ by
      have h : j (r • a) • F = r • (j a • F) := by
        rw [Algebra.smul_def r a, map_mul, j.commutes, mul_smul, algebraMap_smul]
      exact h⟩
    (extendCoefficients (j : O →+* K) hj (baseChangeLinearEquiv O z)).amiceTransform =
      LinearMap.liftBaseChange O
        ((PowerSeries.mapAlgHom (Algebra.ofId ℤ_[p] K)).toLinearMap ∘ₗ
          (amiceTransform : D(ℤ_[p], ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]⟦X⟧)) z := by
  let : Module O D(ℤ_[p], K) := Module.compHom D(ℤ_[p], K) (j : O →+* K)
  let : Module ℤ_[p] D(ℤ_[p], K) := Module.restrictScalars ℤ_[p] O D(ℤ_[p], K)
  let : IsScalarTower ℤ_[p] O D(ℤ_[p], K) := IsScalarTower.restrictScalars ℤ_[p] O D(ℤ_[p], K)
  let : Module O K⟦X⟧ := Module.compHom K⟦X⟧ (j : O →+* K)
  let : IsScalarTower ℤ_[p] O K⟦X⟧ := ⟨fun r a F ↦ by
    have h : j (r • a) • F = r • (j a • F) := by
      rw [Algebra.smul_def r a, map_mul, j.commutes, mul_smul, algebraMap_smul]
    exact h⟩
  rw [extendCoefficients_baseChange (j : O →+* K) hj]
  let amiceO : D(ℤ_[p], K) →ₗ[O] K⟦X⟧ :=
    { (amiceTransform : D(ℤ_[p], K) →ₗ[K] K⟦X⟧).toAddHom with
      map_smul' := fun a ν ↦ by
        exact (amiceTransform : D(ℤ_[p], K) →ₗ[K] K⟦X⟧).map_smul (j a) ν }
  have hamiceO (ν : D(ℤ_[p], K)) : ν.amiceTransform = amiceO ν := (rfl)
  rw [hamiceO, ← LinearMap.comp_apply, LinearMap.comp_liftBaseChange]
  refine congrArg (fun l ↦ LinearMap.liftBaseChange O l z) ?_
  ext μ n
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk, AlgHom.toLinearMap_apply, amiceO]
  have h1 := amiceTransform_extendCoefficients (Algebra.ofId ℤ_[p] K)
    (continuous_algebraMap ℤ_[p] K) (fun r ↦ by simpa using hj (algebraMap ℤ_[p] O r)) μ
  have h2 : extendCoefficients ((j : O →+* K).comp (algebraMap ℤ_[p] O))
      (fun r ↦ hj (algebraMap ℤ_[p] O r)) μ =
      extendCoefficients (Algebra.ofId ℤ_[p] K : ℤ_[p] →+* K)
        (fun r ↦ by simpa using hj (algebraMap ℤ_[p] O r)) μ := by
    simp only [j.comp_algebraMap, Algebra.toRingHom_ofId]
  have h3 : (((extendCoefficients ((j : O →+* K).comp (algebraMap ℤ_[p] O))
      (fun r ↦ hj (algebraMap ℤ_[p] O r)) μ).amiceTransform)).coeff n =
      ((PowerSeries.mapAlgHom (Algebra.ofId ℤ_[p] K)) μ.amiceTransform).coeff n := by
    rw [h2, h1]
    rfl
  exact h3

end Amice

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable {G R O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
  [Algebra R O] [IsModuleTopology R O] [Module.Projective R O] [Module.Finite R O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [Module.Projective R O] [Module.Finite R O] in
/-- In any finite `R`-basis `b` of `O`, extended character integration of an arbitrary `O`-valued
measure `ν ∈ D(G, O)` decomposes as a `K`-linear combination of the extended character integrals
of its `R`-valued coordinate retractions `mapScalars (b.coord i) ν`. -/
theorem extendedCharacterRingHom_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(G, O)) :
    χ.extendedCharacterRingHom j hj ν =
      ∑ i : ι, j (b i) *
        χ.extendedCharacterRingHom (j.comp (algebraMap R O))
          (fun r ↦ hj (algebraMap R O r)) (mapScalars (b.coord i) ν) := by
  have : Module.Projective R O := Module.Projective.of_basis b
  have : Module.Finite R O := Module.Finite.of_basis b
  have hν : ν = baseChangeAlgEquiv O (∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν) := by
    rw [← baseChangeLinearEquiv_symm_apply b ν, ← coe_symm_baseChangeAlgEquiv,
      AlgEquiv.apply_symm_apply]
  conv_lhs => rw [hν]
  simp [map_sum]

end ContinuousMonoidHom

namespace TauCeti

open AbstractMeasure _root_.ContinuousMonoidHom

section Examples

variable {p : ℕ} [Fact p.Prime] {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O]
  [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
  {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! Sanity checks on Dirac tensors, character evaluations, and Amice transforms. -/

example (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (x : ℤ_[p]) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a • dirac K x := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  simp

example {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (x : G) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    χ.extendedCharacterRingHom j hj (baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a * χ x := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  simp

example [Algebra ℤ_[p] K] [ContinuousSMul ℤ_[p] K] (j : O →ₐ[ℤ_[p]] K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
    (extendCoefficients (j : O →+* K) hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] μ))).amiceTransform =
      j a • PowerSeries.map (algebraMap ℤ_[p] K) μ.amiceTransform := by
  let := TauCeti.isModuleTopology_of_finite_of_compactSpace (R := ℤ_[p]) (M := O)
  ext n
  simp

end Examples

end TauCeti
