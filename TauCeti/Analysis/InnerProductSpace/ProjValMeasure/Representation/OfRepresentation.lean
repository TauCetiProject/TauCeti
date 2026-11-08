/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.MatrixElement
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.BorelOperator

/-!
# The projection-valued measure of a representation of `C(K, ℂ)`

Let `π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)` be a unital star representation on a complex Hilbert space,
with `K` compact Hausdorff. Its Borel extension `T = StarAlgHom.representationBorelOperator π` is a
unital star algebra homomorphism on the bounded Borel symbols of `K`. Applied to the indicator of a
Borel set `B` it gives an orthogonal projection `P(B) = T(𝟙_B)`, and multiplicativity of `T` gives
`P(B ∩ C) = P(B) P(C)`. With the diagonal Riesz measures `μ_ξ` of `π`, for which
`⟪ξ, P(B) ξ⟫ = μ_ξ(B)`, these projections form the projection-valued measure
`ProjValMeasure.ofRepresentation π`.

Integration against this measure recovers the Borel extension, and in particular `π` itself on
continuous symbols. Its diagonal measures are regular, and it is the only projection-valued
measure on `K` with regular diagonal measures that recovers `π`: the diagonal measures of such a
measure are regular measures with the same continuous integrals as those of `π`, hence equal to
them by the uniqueness in the Riesz–Markov–Kakutani theorem. The measure also has the same
commutant as `π`.

## Main declarations

* `TauCeti.ProjValMeasure.ofRepresentation π`: the projection-valued measure of `π`.
* `TauCeti.ProjValMeasure.polarizedComplexMeasure_ofRepresentation`: its polarized measures are
  those of `π`.
* `TauCeti.ProjValMeasure.integral_ofRepresentation`: integration against it is the Borel
  extension of `π`.
* `TauCeti.ProjValMeasure.integral_ofRepresentation_ofContinuousMap`: it recovers `π` on
  continuous symbols.
* `TauCeti.ProjValMeasure.eq_ofRepresentation_iff`: among projection-valued measures with regular
  diagonal measures, it is the only one recovering `π`.
* `TauCeti.ProjValMeasure.forall_commute_proj_ofRepresentation_iff`: an operator commutes with
  every projection of the measure iff it commutes with `π`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.1.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.22.
-/

public section

noncomputable section

open MeasureTheory MeasureTheory.VectorMeasure
open scoped InnerProductSpace

namespace TauCeti.ProjValMeasure

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [BorelSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- The matrix element of the Borel extension at an indicator is the polarized measure of the
set. -/
private theorem inner_representationBorelOperator_indicator (ψ ξ : H) {B : Set K}
    (hB : MeasurableSet B) :
    ⟪ψ, π.representationBorelOperator (BoundedBorelFunction.indicator B hB 1) ξ⟫_ℂ =
      π.representationPolarizedMeasure ψ ξ B := by
  rw [StarAlgHom.inner_representationBorelOperator, BoundedBorelFunction.coe_indicator,
    BoundedBorelFunction.coe_one, Pi.one_def, VectorMeasure.integral_indicator_const _ hB,
    ContinuousLinearMap.mul_apply', one_mul]

/-- The **projection-valued measure of a representation** `π` of `C(K, ℂ)`: the projection of a
Borel set `B` is the Borel extension of `π` applied to the indicator of `B`, and the diagonal
measures are the Riesz measures `μ_ξ` of `π`. -/
def ofRepresentation : ProjValMeasure K H where
  proj B hB := π.representationBorelOperator (BoundedBorelFunction.indicator B hB 1)
  diag := π.representationDiagMeasure
  diag_finite _ := inferInstance
  inner_proj B hB ξ := by
    rw [inner_representationBorelOperator_indicator,
      π.representationPolarizedMeasure_self_apply ξ hB, measureReal_def]
  proj_univ := by
    rw [BoundedBorelFunction.indicator_univ, map_one, ContinuousLinearMap.one_def]
  proj_inter B₁ B₂ hB₁ hB₂ := by
    rw [← map_mul, BoundedBorelFunction.indicator_mul_indicator, one_mul]

/-- The projection of a Borel set `B` is the Borel extension of `π` at the indicator of `B`. -/
@[simp]
theorem ofRepresentation_proj {B : Set K} (hB : MeasurableSet B) :
    (ofRepresentation π).proj B hB =
      π.representationBorelOperator (BoundedBorelFunction.indicator B hB 1) :=
  (rfl)

/-- The diagonal measures are the Riesz measures of `π`. -/
@[simp]
theorem ofRepresentation_diag (ξ : H) :
    (ofRepresentation π).diag ξ = π.representationDiagMeasure ξ :=
  (rfl)

/-- The diagonal measures of the projection-valued measure of a representation are regular. -/
instance regular_diag_ofRepresentation (ξ : H) : ((ofRepresentation π).diag ξ).Regular := by
  rw [ofRepresentation_diag]
  infer_instance

/-- The polarized complex measures of the projection-valued measure of `π` are the polarized
measures `μ_(ψ,ξ)` of `π`. -/
@[simp]
theorem polarizedComplexMeasure_ofRepresentation (ψ ξ : H) :
    (ofRepresentation π).polarizedComplexMeasure ψ ξ = π.representationPolarizedMeasure ψ ξ :=
  VectorMeasure.ext fun B hB => by
    rw [polarizedComplexMeasure_apply _ _ _ B hB, ofRepresentation_proj,
      inner_representationBorelOperator_indicator]

/-- Integration against the projection-valued measure of `π` is the Borel extension of `π`. -/
@[simp]
theorem integral_ofRepresentation :
    (ofRepresentation π).integral = π.representationBorelOperator :=
  StarAlgHom.ext fun f => ContinuousLinearMap.ext fun ξ => ext_inner_left ℂ fun ψ => by
    rw [← integral_polarizedComplexMeasure_eq_inner_integral,
      polarizedComplexMeasure_ofRepresentation, StarAlgHom.inner_representationBorelOperator]

/-- **Recovery of the representation.** Integrating a continuous function against the
projection-valued measure of `π` gives its image under `π`. -/
theorem integral_ofRepresentation_ofContinuousMap (f : C(K, ℂ)) :
    (ofRepresentation π).integral (BoundedBorelFunction.ofContinuousMap f) = π f := by
  simp

/-- **Uniqueness of the projection-valued measure of a representation.** A projection-valued
measure on `K` whose diagonal measures are regular is the projection-valued measure of `π` iff
integrating every continuous function against it gives its image under `π`. -/
theorem eq_ofRepresentation_iff (P : ProjValMeasure K H) (hP : ∀ ξ, (P.diag ξ).Regular) :
    P = ofRepresentation π ↔
      ∀ f : C(K, ℂ), P.integral (BoundedBorelFunction.ofContinuousMap f) = π f := by
  refine ⟨fun h => h ▸ integral_ofRepresentation_ofContinuousMap π, fun h => ?_⟩
  refine ext_of_diag fun ξ => ?_
  have := hP ξ
  refine (π.eq_representationDiagMeasure_iff ξ (P.diag ξ)).2 fun f => ?_
  simpa [h] using P.integral_diag_eq_inner_integral (BoundedBorelFunction.ofContinuousMap f) ξ

/-- **Commutant of the projection-valued measure of a representation.** An operator commutes with
every projection of the projection-valued measure of `π` iff it commutes with `π f` for every
continuous `f`; by `forall_commute_integral_iff`, equivalently with every integral against it. -/
theorem forall_commute_proj_ofRepresentation_iff (A : H →L[ℂ] H) :
    (∀ B hB, Commute A ((ofRepresentation π).proj B hB)) ↔ ∀ f : C(K, ℂ), Commute A (π f) := by
  rw [← forall_commute_integral_iff, integral_ofRepresentation]
  exact ⟨fun h f => by simpa using h (BoundedBorelFunction.ofContinuousMap f),
    fun h => π.commute_representationBorelOperator h⟩

end TauCeti.ProjValMeasure
