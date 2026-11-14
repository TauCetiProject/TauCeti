/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import TauCeti.NumberTheory.Padics.Measure.BaseChange
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
import TauCeti.NumberTheory.Padics.Measure.IntegralUnitBall

/-!
# Compatibility of finite free base change with unit-ball coefficient extension

Let `X` be a profinite space, `R` a compact topological commutative ring, `O` a finite free
Hausdorff topological `R`-algebra with continuous `R`-action, and `j : O →+* K` a ring
homomorphism into the closed unit ball of a complete ultrametric field `K`. Two operations move
measures across the diagram `R → O → K`:

* `AbstractMeasure.extendScalars O : D(X, R) →ₛₗ[algebraMap R O] D(X, O)` and its tensor lift
  `AbstractMeasure.baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`;
* `AbstractMeasure.extendCoefficients j hj : D(X, O) →+ D(X, K)`, extending integral coefficients
  into `K` via locally constant functions and ultrametric completion.

This file proves that the two constructions commute without requiring continuity of `j`:

* `extendCoefficients j hj (extendScalars O μ)` equals the coefficient extension of `μ` along
  `j.comp (algebraMap R O)` (`AbstractMeasure.extendCoefficients_extendScalars`);
* on a pure tensor `a ⊗ₜ μ`, `extendCoefficients j hj` produces `j a` times the extension of `μ`
  along `R → K` (`AbstractMeasure.extendCoefficients_baseChangeLinearEquiv_tmul`,
  `AbstractMeasure.extendCoefficients_baseChangeAlgEquiv_tmul`), and hence decomposes the
  extension of every `ν ∈ D(X, O)` in any finite `R`-basis of `O`
  (`AbstractMeasure.extendCoefficients_eq_sum_basis`);
* on a profinite topological monoid `G`, extended character integration
  `ContinuousMonoidHom.extendedCharacterRingHom` transforms accordingly on `extendScalars O` and
  on `baseChangeAlgEquiv O`;
* on `ℤ_p`, `extendScalars O` applies `algebraMap ℤ_[p] O` coefficientwise to the Amice transform
  (`AbstractMeasure.amiceTransform_extendScalars`), and combining with `extendCoefficients` along
  an `O →ₐ[ℤ_[p]] K` into the unit ball recovers `j a • PowerSeries.map (algebraMap ℤ_[p] K) A(μ)`
  (`AbstractMeasure.amiceTransform_extendCoefficients_baseChangeLinearEquiv_tmul`).

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
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]
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

/-- Extending coefficients of a pure tensor `a ⊗ₜ μ` under `baseChangeLinearEquiv O` scales the
coefficient extension of `μ` along `R → K` by `j a`. -/
theorem extendCoefficients_baseChangeLinearEquiv_tmul (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(X, R)) :
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  simp

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

/-- When `j : O →ₐ[R] K` is an `R`-algebra homomorphism into the closed unit ball, extending
`baseChangeLinearEquiv O (a ⊗ₜ μ)` along `j` gives `j a` times the extension of `μ` along
`algebraMap R K`. -/
theorem extendCoefficients_algHom_baseChangeLinearEquiv_tmul [Algebra R K] (j : O →ₐ[R] K)
    (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (μ : D(X, R)) :
    extendCoefficients (j : O →+* K) hj (baseChangeLinearEquiv O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (algebraMap R K)
        (fun r ↦ by simpa only [AlgHom.commutes] using hj (algebraMap R O r)) μ := by
  rw [baseChangeLinearEquiv_tmul]
  exact (extendCoefficients_smul (j : O →+* K) (extendScalars O μ) hj a).trans
    (congrArg (j a • ·) (extendCoefficients_algHom_extendScalars j hj μ))

/-- In any finite `R`-basis `b` of `O`, the coefficient extension of an arbitrary `O`-valued
measure `ν ∈ D(X, O)` decomposes as a `K`-linear combination of `R`-valued coordinate extensions. -/
theorem extendCoefficients_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(X, O)) :
    ∃ c : ι → D(X, R),
      extendCoefficients j hj ν =
        ∑ i : ι, j (b i) •
          extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) (c i) ∧
        ∀ i (g : C(X, R)), c i g = b.coord i (ν ((algebraMapCLM R O : C(R, O)).comp g)) := by
  obtain ⟨c, hc, hcg⟩ := baseChangeLinearEquiv_symm_apply_comp_algebraMap b ν
  refine ⟨c, ?_, hcg⟩
  have hν : ν = baseChangeLinearEquiv O (∑ i : ι, b i ⊗ₜ[R] c i) := by
    rw [← hc, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hν]
  simp [map_sum]

end ProfiniteSpace

section ProfiniteMonoid

variable {G R O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Extending coefficients of a pure tensor `a ⊗ₜ μ` under `baseChangeAlgEquiv O` scales the
coefficient extension of `μ` along `R → K` by `j a`. -/
theorem extendCoefficients_baseChangeAlgEquiv_tmul (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(G, R)) :
    extendCoefficients j hj (baseChangeAlgEquiv O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r)) μ := by
  simp

/-- Extending coefficients of `baseChangeAlgEquiv O (a ⊗ₜ μ)` along an `R`-algebra homomorphism
`j : O →ₐ[R] K` into the closed unit ball gives `j a` times the extension of `μ` along
`algebraMap R K`. -/
theorem extendCoefficients_algHom_baseChangeAlgEquiv_tmul [Algebra R K] (j : O →ₐ[R] K)
    (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (μ : D(G, R)) :
    extendCoefficients (j : O →+* K) hj (baseChangeAlgEquiv O (a ⊗ₜ[R] μ)) =
      j a • extendCoefficients (algebraMap R K)
        (fun r ↦ by simpa only [AlgHom.commutes] using hj (algebraMap R O r)) μ := by
  rw [baseChangeAlgEquiv_tmul]
  exact (extendCoefficients_smul (j : O →+* K) (extendScalars O μ) hj a).trans
    (congrArg (j a • ·) (extendCoefficients_algHom_extendScalars j hj μ))

end ProfiniteMonoid

section Amice

variable {p : ℕ} [Fact p.Prime] {O K : Type*}
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra ℤ_[p] O] [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- Extending scalars from `ℤ_p` to `O` applies `algebraMap ℤ_[p] O` to the coefficients of the
Amice transform. -/
@[simp]
theorem amiceTransform_extendScalars (μ : D(ℤ_[p], ℤ_[p])) :
    (extendScalars O μ).amiceTransform = PowerSeries.map (algebraMap ℤ_[p] O) μ.amiceTransform := by
  ext n
  simp only [coeff_amiceTransform, PowerSeries.coeff_map]
  rw [← extendScalars_apply_comp_algebraMap]
  congr 1
  ext x
  simp [Algebra.algebraMap_eq_smul_one]

/-- On `ℤ_p`, the Amice transform of `baseChangeLinearEquiv O (a ⊗ₜ μ)` is `a` times the mapped
Amice transform of `μ`. -/
theorem amiceTransform_baseChangeLinearEquiv_tmul (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] μ)).amiceTransform =
      a • PowerSeries.map (algebraMap ℤ_[p] O) μ.amiceTransform := by
  simp

/-- Extending `baseChangeLinearEquiv O (a ⊗ₜ μ)` along a `ℤ_p`-algebra homomorphism
`j : O →ₐ[ℤ_[p]] K` into the closed unit ball of a complete ultrametric `ℤ_p`-field `K` maps its
Amice transform to `j a • PowerSeries.map (algebraMap ℤ_[p] K) μ.amiceTransform`, without assuming
continuity of `j`. -/
theorem amiceTransform_extendCoefficients_baseChangeLinearEquiv_tmul
    [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [Algebra ℤ_[p] K] [ContinuousSMul ℤ_[p] K]
    (j : O →ₐ[ℤ_[p]] K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (extendCoefficients (j : O →+* K) hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] μ))).amiceTransform =
      j a • PowerSeries.map (algebraMap ℤ_[p] K) μ.amiceTransform := by
  rw [extendCoefficients_algHom_baseChangeLinearEquiv_tmul, map_smul]
  have hcont : Continuous (Algebra.ofId ℤ_[p] K) := by
    rw [← RingHom.coe_coe, Algebra.toRingHom_ofId]
    exact continuous_algebraMap ℤ_[p] K
  simpa only [Algebra.toRingHom_ofId] using congrArg (j a • ·)
    (amiceTransform_extendCoefficients (Algebra.ofId ℤ_[p] K) hcont
      (fun r ↦ by simpa only [Algebra.ofId_apply, AlgHom.commutes] using hj (algebraMap ℤ_[p] O r))
      μ)

end Amice

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable {G R O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Extended character integration of `extendScalars O μ` agrees with extended character
integration of `μ` along `j.comp (algebraMap R O)`. -/
theorem extendedCharacterRingHom_extendScalars (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (μ : D(G, R)) :
    χ.extendedCharacterRingHom j hj (extendScalars O μ) =
      χ.extendedCharacterRingHom (j.comp (algebraMap R O))
        (fun r ↦ hj (algebraMap R O r)) μ := by
  simp

/-- Extended character integration sends `baseChangeAlgEquiv O (a ⊗ₜ μ)` to `j a` times the
extended character integral of `μ`. -/
theorem extendedCharacterRingHom_baseChangeAlgEquiv_tmul (χ : G →ₜ* K) (j : O →+* K)
    (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (μ : D(G, R)) :
    χ.extendedCharacterRingHom j hj (baseChangeAlgEquiv O (a ⊗ₜ[R] μ)) =
      j a * χ.extendedCharacterRingHom (j.comp (algebraMap R O))
        (fun r ↦ hj (algebraMap R O r)) μ := by
  simp

end ContinuousMonoidHom

namespace TauCeti

open AbstractMeasure _root_.ContinuousMonoidHom

section Examples

variable {p : ℕ} [Fact p.Prime] {O : Type*} [NormedCommRing O] [Algebra ℤ_[p] O]
  [ContinuousSMul ℤ_[p] O] [Module.Free ℤ_[p] O] [Module.Finite ℤ_[p] O]
  {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! Sanity checks on Dirac tensors and character evaluations. -/

example (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (x : ℤ_[p]) :
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a • dirac K x := by
  simp

example {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (x : G) :
    χ.extendedCharacterRingHom j hj (baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a * χ x := by
  simp

end Examples

end TauCeti
