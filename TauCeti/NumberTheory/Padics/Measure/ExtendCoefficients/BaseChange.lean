/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.BaseChange.Basic
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Algebra
import TauCeti.NumberTheory.Padics.Measure.IntegralUnitBall

/-!
# Compatibility of finite free base change with unit-ball coefficient extension

Let `X` be a profinite space, `R` a compact topological commutative ring, `O` a Hausdorff
topological `R`-algebra with continuous `R`-action, and `j : O →+* K` a ring homomorphism into the
closed unit ball of a complete ultrametric field `K`. Two operations move measures across the
diagram `R → O → K`:

* when `O` is finite and free over `R`, `AbstractMeasure.extendScalars O :
  D(X, R) →ₛₗ[algebraMap R O] D(X, O)` and its tensor lift
  `AbstractMeasure.baseChangeLinearEquiv O : O ⊗[R] D(X, R) ≃ₗ[O] D(X, O)`;
* `AbstractMeasure.extendCoefficients j hj : D(X, O) →+ D(X, K)`, extending integral coefficients
  into `K` via locally constant functions and ultrametric completion.

This file proves that these constructions are compatible without assuming continuity of `j`:

* for finite free `O`, `extendCoefficients j hj (extendScalars O μ)` equals the coefficient
  extension of `μ` along `j.comp (algebraMap R O)`
  (`AbstractMeasure.extendCoefficients_extendScalars`), and for an `R`-algebra map `j : O →ₐ[R] K`
  into the closed unit ball it equals the extension along `algebraMap R K`
  (`AbstractMeasure.extendCoefficients_algHom_extendScalars`);
* in any finite `R`-basis `b` of `O`, the extension of every `ν ∈ D(X, O)` decomposes via the
  coordinate retractions `AbstractMeasure.mapScalars (b.coord i) ν`
  (`AbstractMeasure.extendCoefficients_eq_sum_basis`);
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

omit [Module.Free R O] in
/-- In any finite `R`-basis `b` of `O`, the coefficient extension of an arbitrary `O`-valued
measure `ν ∈ D(X, O)` decomposes as a `K`-linear combination of the extensions of its `R`-valued
coordinate retractions `mapScalars (b.coord i) ν`. -/
theorem extendCoefficients_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(X, O)) :
    extendCoefficients j hj ν =
      ∑ i : ι, j (b i) •
        extendCoefficients (j.comp (algebraMap R O)) (fun r ↦ hj (algebraMap R O r))
          (mapScalars (b.coord i) ν) := by
  have : Module.Free R O := Module.Free.of_basis b
  have hν : ν = baseChangeLinearEquiv O (∑ i : ι, b i ⊗ₜ[R] mapScalars (b.coord i) ν) := by
    rw [← baseChangeLinearEquiv_symm_apply b ν, LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hν]
  simp [map_sum]

end ProfiniteSpace

end AbstractMeasure

namespace ContinuousMonoidHom

open AbstractMeasure

variable {G R O K : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T2Space O]
  [Algebra R O] [ContinuousSMul R O] [Module.Free R O] [Module.Finite R O]
  [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [Module.Free R O] in
/-- In any finite `R`-basis `b` of `O`, extended character integration of an arbitrary `O`-valued
measure `ν ∈ D(G, O)` decomposes as a `K`-linear combination of the extended character integrals
of its `R`-valued coordinate retractions `mapScalars (b.coord i) ν`. -/
theorem extendedCharacterRingHom_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (ν : D(G, O)) :
    χ.extendedCharacterRingHom j hj ν =
      ∑ i : ι, j (b i) *
        χ.extendedCharacterRingHom (j.comp (algebraMap R O))
          (fun r ↦ hj (algebraMap R O r)) (mapScalars (b.coord i) ν) := by
  have : Module.Free R O := Module.Free.of_basis b
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
    extendCoefficients j hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a • dirac K x := by
  simp

example {G : Type*} [TopologicalSpace G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] [Monoid G] [ContinuousMul G]
    (χ : G →ₜ* K) (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1) (a : O) (x : G) :
    χ.extendedCharacterRingHom j hj (baseChangeAlgEquiv O (a ⊗ₜ[ℤ_[p]] dirac ℤ_[p] x)) =
      j a * χ x := by
  simp

example [Algebra ℤ_[p] K] [ContinuousSMul ℤ_[p] K] (j : O →ₐ[ℤ_[p]] K) (hj : ∀ a, ‖j a‖ ≤ 1)
    (a : O) (μ : D(ℤ_[p], ℤ_[p])) :
    (extendCoefficients (j : O →+* K) hj (baseChangeLinearEquiv O (a ⊗ₜ[ℤ_[p]] μ))).amiceTransform =
      j a • PowerSeries.map (algebraMap ℤ_[p] K) μ.amiceTransform := by
  ext n
  simp

end Examples

end TauCeti
