/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Euclidean coordinates on a finite-dimensional space

A finite-dimensional real normed space `E` carries no preferred inner product, but the coordinates
in the basis `Module.finBasis ℝ E` identify it with the Euclidean space of the same dimension
(`TauCeti.finBasisEuclideanEquiv`). This identification sends the vectors of the basis to the
standard basis, and carries the Haar measure of the basis to Lebesgue measure.

This is how a function on the model space of a manifold, such as a function read in a chart, is
handed to the analysis on Euclidean domains, which is stated on `EuclideanSpace ℝ ι`.

## Main declarations

* `TauCeti.finBasisEuclideanEquiv`: the coordinates in `Module.finBasis ℝ E`, as a continuous
  linear equivalence with `EuclideanSpace ℝ (Fin (finrank ℝ E))`.
* `TauCeti.measurePreserving_finBasisEuclideanEquiv_symm`: its inverse carries Lebesgue measure to
  the Haar measure of the basis.
-/

public section

open Module MeasureTheory

noncomputable section

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coordinates of a finite-dimensional space `E` in the basis `Module.finBasis ℝ E`, as a
continuous linear equivalence with the Euclidean space of the same dimension. -/
def finBasisEuclideanEquiv : E ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E)) :=
  (Module.finBasis ℝ E).equivFunL.trans (EuclideanSpace.equiv _ ℝ).symm

variable {E}

/-- The Euclidean coordinates send the vectors of `Module.finBasis ℝ E` to the standard basis. -/
@[simp]
theorem finBasisEuclideanEquiv_symm_single (i : Fin (finrank ℝ E)) :
    (finBasisEuclideanEquiv E).symm (EuclideanSpace.single i 1) = Module.finBasis ℝ E i := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  ext j
  simp [finBasisEuclideanEquiv, Finsupp.single_apply, eq_comm]

/-- The derivative of a function read in Euclidean coordinates, along the `i`-th standard basis
vector, is the derivative of the function along the `i`-th vector of `Module.finBasis ℝ E`. -/
theorem fderiv_comp_finBasisEuclideanEquiv_symm_single {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (z : EuclideanSpace ℝ (Fin (finrank ℝ E)))
    (i : Fin (finrank ℝ E)) :
    fderiv ℝ (f ∘ (finBasisEuclideanEquiv E).symm) z (EuclideanSpace.single i 1) =
      fderiv ℝ f ((finBasisEuclideanEquiv E).symm z) (Module.finBasis ℝ E i) := by
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, finBasisEuclideanEquiv_symm_single]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Euclidean coordinates carry the Haar measure of `Module.finBasis ℝ E` to Lebesgue
measure. -/
theorem map_finBasisEuclideanEquiv_addHaar :
    (Module.finBasis ℝ E).addHaar.map (finBasisEuclideanEquiv E) = volume := by
  rw [Module.Basis.map_addHaar]
  have hb : (Module.finBasis ℝ E).map (finBasisEuclideanEquiv E).toLinearEquiv =
      (EuclideanSpace.basisFun _ ℝ).toBasis := by
    ext i
    rw [Module.Basis.map_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv, ← finBasisEuclideanEquiv_symm_single,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hb, OrthonormalBasis.addHaar_eq_volume]

/-- The inverse of the Euclidean coordinates carries Lebesgue measure to the Haar measure of
`Module.finBasis ℝ E`. -/
theorem measurePreserving_finBasisEuclideanEquiv_symm :
    MeasurePreserving (finBasisEuclideanEquiv E).symm volume (Module.finBasis ℝ E).addHaar := by
  refine ⟨(finBasisEuclideanEquiv E).symm.continuous.measurable, ?_⟩
  rw [← map_finBasisEuclideanEquiv_addHaar, Measure.map_map
    (finBasisEuclideanEquiv E).symm.continuous.measurable
    (finBasisEuclideanEquiv E).continuous.measurable]
  simp

end TauCeti
