/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar
import TauCeti.MeasureTheory.Measure.Haar.DistribChar.Matrix
import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Additive Haar measure under linear automorphisms

`LinearEquiv.map_addHaar_eq_smul` computes the pushforward of additive Haar measure under
a linear automorphism of a finite-dimensional vector space over a locally compact field.
It uses `MeasureTheory.distribHaarChar_eq_distribHaarChar_det` and
`MeasureTheory.Measure.map_smul_eq_inv_distribHaarChar_smul` in a basis.

## References

* A. Weil, *Basic Number Theory*, Chapter I, §2.
-/

public section

open Matrix MeasureTheory

namespace LinearEquiv

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [TopologicalSpace V]
  [IsModuleTopology K V] [MeasurableSpace V] [BorelSpace V]

/-- The pushforward of additive Haar measure under a linear automorphism over a locally compact
second countable field scales by the Haar character of its inverse determinant. See Weil,
*Basic Number Theory*, Chapter I, §2. -/
theorem map_addHaar_eq_smul (e : V ≃ₗ[K] V) (μ : Measure V) [μ.IsAddHaarMeasure] :
    μ.map e = distribHaarChar K e.det⁻¹ • μ := by
  classical
  let b := Module.finBasis K V
  let A := LinearMap.toMatrix b b (e : V →ₗ[K] V)
  have hdet : A.det = e.det := by rw [LinearEquiv.coe_det, LinearMap.det_toMatrix]
  let g := GeneralLinearGroup.mkOfDetNeZero A (hdet.symm ▸ e.det.ne_zero)
  have hgA : (g : Matrix _ _ K) = A := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hgdet : g.det = e.det := Units.ext (by rw [GeneralLinearGroup.val_det_apply, hgA, hdet])
  let c := b.equivFun.toContinuousLinearEquivOfIsModuleTopology
  borelize (Fin (Module.finrank K V) → K)
  let μc := μ.map c
  have := IsModuleTopology.isTopologicalAddGroup K V
  have : μc.IsAddHaarMeasure := c.isAddHaarMeasure_map μ
  have hg : μc.map (g • ·) = distribHaarChar K e.det⁻¹ • μc := by
    rw [μc.map_smul_eq_inv_distribHaarChar_smul g, distribHaarChar_eq_distribHaarChar_det,
      hgdet, map_inv]
  have hc_repr (v : V) : c v = b.repr v := by
    simp only [c, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
      Module.Basis.equivFun_apply]
  have hcoord : c ∘ e = (g • ·) ∘ c := by
    funext v
    simp only [Function.comp_apply, hc_repr, Units.smul_def, smul_eq_mulVec, hgA]
    exact (LinearMap.toMatrix_mulVec_repr b b (e : V →ₗ[K] V) v).symm
  have hmeas : Measurable e :=
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap).measurable
  -- Compare the two measures after pushing both to the same basis coordinates.
  apply MeasurableEquiv.map_measurableEquiv_injective c.toHomeomorph.toMeasurableEquiv
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [Measure.map_smul _ c.continuous.measurable.aemeasurable,
    Measure.map_map c.continuous.measurable hmeas, hcoord,
    ← Measure.map_map (measurable_const_smul g) c.continuous.measurable]
  exact hg

end LinearEquiv
