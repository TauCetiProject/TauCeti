/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Matrix
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Additive Haar measure under linear automorphisms

`LinearEquiv.map_addHaar_eq_smul` computes the pushforward of additive Haar measure under
a linear automorphism of a finite-dimensional vector space over a locally compact second
countable field: the scaling factor is the Haar character of the inverse determinant.
The reduction via `Module.Basis.toGL_smul_equivFun` follows the real-case precedent
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` in Mathlib. The proof uses
 `MeasureTheory.distribHaarChar_eq_distribHaarChar_det` and
`MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul` in a basis.
`LinearEquiv.measurePreserving_addHaar_of_det_sq_eq_one` deduces invariance when the
determinant squares to one, and `LinearMap.BilinForm.measurePreserving_isometryGroup`
applies this to left-separating forms using `TauCeti.BilinForm.IsIsometry.det_sq_eq_one`.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2.
-/

public section

open Matrix MeasureTheory

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V] [MeasurableSpace V] [BorelSpace V]

namespace LinearEquiv

/-- The pushforward of additive Haar measure under a linear automorphism of a finite-dimensional
vector space over a locally compact second countable field scales by the Haar character of its
inverse determinant. See Weil,
*Basic Number Theory*, Chapter I, §2. -/
theorem map_addHaar_eq_smul (e : V ≃ₗ[K] V) (μ : Measure V) [μ.IsAddHaarMeasure] :
    μ.map e = distribHaarChar K e.det⁻¹ • μ := by
  classical
  let b := Module.finBasis K V
  let g := b.toGL e
  let c := b.equivFun.toContinuousLinearEquivOfIsModuleTopology
  borelize (Fin (Module.finrank K V) → K)
  let μc := μ.map c
  have := IsModuleTopology.isTopologicalAddGroup K V
  have : μc.IsAddHaarMeasure := c.isAddHaarMeasure_map μ
  have hg : μc.map (g • ·) = distribHaarChar K e.det⁻¹ • μc := by
    rw [μc.map_smul_eq_inv_distribHaarChar_smul g, distribHaarChar_eq_distribHaarChar_det,
      Module.Basis.det_toGL b e, map_inv]
  have hcoord : c ∘ e = (g • ·) ∘ c := by
    funext v
    simp only [Function.comp_apply, c, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
      g]
    exact (b.toGL_smul_equivFun e v).symm
  have hmeas : Measurable e :=
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap).measurable
  -- Compare the two measures after pushing both to the same basis coordinates.
  apply MeasurableEquiv.map_measurableEquiv_injective c.toHomeomorph.toMeasurableEquiv
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [Measure.map_smul _ c.continuous.measurable.aemeasurable,
    Measure.map_map c.continuous.measurable hmeas, hcoord,
    ← Measure.map_map (measurable_const_smul g) c.continuous.measurable]
  exact hg

/-- A linear automorphism whose determinant squares to one preserves additive Haar measure
on a finite-dimensional vector space over a locally compact second countable field. -/
theorem measurePreserving_addHaar_of_det_sq_eq_one (e : V ≃ₗ[K] V) (μ : Measure V)
    [μ.IsAddHaarMeasure] (hdet : e.det ^ 2 = 1) : MeasurePreserving e μ μ := by
  have hchar : distribHaarChar K e.det = 1 := by
    apply (pow_eq_one_iff_of_nonneg (by positivity : 0 ≤ distribHaarChar K e.det) two_ne_zero).mp
    rw [← map_pow, hdet, map_one]
  have := IsModuleTopology.isTopologicalAddGroup K V
  refine ⟨(IsModuleTopology.continuous_of_linearMap e.toLinearMap).measurable, ?_⟩
  simp only [e.map_addHaar_eq_smul μ, map_inv, hchar, inv_one, one_smul]

end LinearEquiv

namespace LinearMap.BilinForm

/-- Every linear isometry of a left-separating bilinear form on a finite-dimensional vector
space over a locally compact second countable field preserves additive Haar measure. -/
theorem measurePreserving_isometryGroup (B : LinearMap.BilinForm K V)
    (g : LinearMap.isometryGroup B) (hB : B.SeparatingLeft) (ν : Measure V) [ν.IsAddHaarMeasure] :
    MeasurePreserving (g : V ≃ₗ[K] V) ν ν := by
  apply LinearEquiv.measurePreserving_addHaar_of_det_sq_eq_one
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one, LinearEquiv.coe_det]
  exact TauCeti.BilinForm.IsIsometry.det_sq_eq_one (Module.finBasis K V)
    (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
    (mem_isometryGroup.mp g.property)

end LinearMap.BilinForm
