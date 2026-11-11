/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Representation.OfRepresentation

/-!
# Unitary transport of representation projection-valued measures

For a representation `π` of `C(K, ℂ)` and a Hilbert space isometry equivalence `U`, conjugating
`π` by `U` conjugates its projection-valued measure and its bounded Borel integrals by the same
map. The source and target Hilbert spaces may differ.

The comparison uses the uniqueness of the regular diagonal and polarized measures on
continuous test functions. Their matrix-element equations then identify the existing Borel
extension after conjugation; no new extension or projection-valued measure is constructed.

These comparisons transport the spectral data when identifying reducing summands with their
multiplication models.

## Main declarations

* `StarAlgHom.representationDiagMeasure_conj`: transport of diagonal measures.
* `StarAlgHom.representationPolarizedMeasure_conj`: transport of polarized measures.
* `StarAlgHom.representationBorelOperator_conj`: conjugation of the Borel extension.
* `StarAlgHom.ofRepresentation_proj_conj`: conjugation of spectral projections.
* `StarAlgHom.integral_ofRepresentation_conj`: conjugation of Borel integrals.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.1.
* W. Rudin, *Functional Analysis*, 2nd ed., McGraw–Hill (1991), Theorem 12.22.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

namespace StarAlgHom

/-- Conjugating a representation by a unitary transports its polarized measure by the inverse
unitary in both vector arguments. -/
@[simp]
theorem representationPolarizedMeasure_conj
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] H') (ψ ξ : H') :
    (U.conjStarAlgEquiv.toStarAlgHom.comp π).representationPolarizedMeasure ψ ξ =
      π.representationPolarizedMeasure (U.symm ψ) (U.symm ξ) := by
  symm
  apply ((U.conjStarAlgEquiv.toStarAlgHom.comp π).eq_representationPolarizedMeasure_iff
    ψ ξ _).2
  intro f
  rw [π.integral_representationPolarizedMeasure]
  simpa only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.apply_symm_apply] using
    (U.inner_map_map (U.symm ψ) (π f (U.symm ξ))).symm

/-- Conjugating a representation by a unitary transports its diagonal measure by the inverse
unitary in the vector argument. -/
@[simp]
theorem representationDiagMeasure_conj
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] H') (ξ : H') :
    (U.conjStarAlgEquiv.toStarAlgHom.comp π).representationDiagMeasure ξ =
      π.representationDiagMeasure (U.symm ξ) := by
  symm
  apply ((U.conjStarAlgEquiv.toStarAlgHom.comp π).eq_representationDiagMeasure_iff ξ _).2
  intro f
  rw [π.integral_representationDiagMeasure]
  simpa only [StarAlgHom.comp_apply, StarAlgEquiv.toStarAlgHom_apply,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.apply_symm_apply] using
    (U.inner_map_map (U.symm ξ) (π f (U.symm ξ))).symm

/-- The bounded Borel extension of a unitarily conjugated representation is the conjugate of
the original bounded Borel extension. -/
@[simp]
theorem representationBorelOperator_conj
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] H')
    (f : TauCeti.BoundedBorelFunction K) :
    (U.conjStarAlgEquiv.toStarAlgHom.comp π).representationBorelOperator f =
      U.conjStarAlgEquiv (π.representationBorelOperator f) := by
  ext ξ
  apply ext_inner_left ℂ
  intro ψ
  rw [inner_representationBorelOperator, representationPolarizedMeasure_conj,
    ← inner_representationBorelOperator]
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.apply_symm_apply] using
    (U.inner_map_map (U.symm ψ) (π.representationBorelOperator f (U.symm ξ))).symm

/-- The projection-valued measure of a unitarily conjugated representation has the conjugate
projection field, including when the Hilbert space changes. -/
theorem ofRepresentation_proj_conj
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] H')
    {B : Set K} (hB : MeasurableSet B) :
    (TauCeti.ProjValMeasure.ofRepresentation
      (U.conjStarAlgEquiv.toStarAlgHom.comp π)).proj B hB =
      U.conjStarAlgEquiv ((TauCeti.ProjValMeasure.ofRepresentation π).proj B hB) := by
  simp only [TauCeti.ProjValMeasure.ofRepresentation_proj,
    representationBorelOperator_conj]

/-- Integration against the projection-valued measure of a unitarily conjugated representation
conjugates every bounded Borel integral by the same unitary. -/
theorem integral_ofRepresentation_conj
    (π : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (U : H ≃ₗᵢ[ℂ] H')
    (f : TauCeti.BoundedBorelFunction K) :
    (TauCeti.ProjValMeasure.ofRepresentation
      (U.conjStarAlgEquiv.toStarAlgHom.comp π)).integral f =
      U.conjStarAlgEquiv ((TauCeti.ProjValMeasure.ofRepresentation π).integral f) := by
  simp only [TauCeti.ProjValMeasure.integral_ofRepresentation,
    representationBorelOperator_conj]

end StarAlgHom
