/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Bilinear
public import TauCeti.MeasureTheory.GroupExtension.FactorSet
import TauCeti.MeasureTheory.Measure.Haar.DistribChar.LinearEquiv

/-!
# Symplectic invariance of Heisenberg Haar measure

`LinearMap.BilinForm.measurePreserving_isometryGroupToMulAut` shows that the isometry
action on the bilinear Heisenberg extension preserves the product of a central measure
and an additive Haar measure on the vector space. The action fixes the first coordinate
and preserves Haar measure on the second by `LinearEquiv.map_addHaar_eq_smul`
and `TauCeti.BilinForm.IsIsometry.det_sq_eq_one`. This includes the symplectic action
for a nondegenerate alternating form.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), I, §§2–4.
-/

public section

open MeasureTheory Multiplicative TauCeti
open LinearMap (BilinForm)

attribute [local instance] trivialMulDistribMulAction

namespace LinearMap.BilinForm

variable {K W : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [LocallyCompactSpace K] [SecondCountableTopology K] [MeasurableSpace K]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W] [TopologicalSpace W]
  [IsModuleTopology K W] [MeasurableSpace W] [BorelSpace W]

/-- For a left-separating bilinear form, the isometry action preserves the transported
product of any central measure and an additive Haar measure on the underlying vector space.
In particular this holds for symplectic automorphisms and self-dual Haar measures.
See Weil, *Sur certains groupes d'opérateurs unitaires*, I, §§2–4. -/
theorem measurePreserving_isometryGroupToMulAut (B : BilinForm K W)
    (g : LinearMap.isometryGroup B) (hB : B.SeparatingLeft)
    (μ : Measure (Multiplicative K)) (ν : Measure W) [ν.IsAddHaarMeasure] :
    MeasurePreserving (B.isometryGroupToMulAut g)
      (B.bilinearFactorSet.prodMeasure μ (ν.map ofAdd))
      (B.bilinearFactorSet.prodMeasure μ (ν.map ofAdd)) := by
  classical
  let e : W ≃ₗ[K] W := g
  have hdet : e.det ^ 2 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, LinearEquiv.coe_det]
    exact TauCeti.BilinForm.IsIsometry.det_sq_eq_one (Module.finBasis K W)
      (mem_nonZeroDivisors_of_ne_zero ((LinearMap.separatingLeft_iff_det_ne_zero _).mp hB))
      (mem_isometryGroup.mp g.property)
  have hchar : distribHaarChar K e.det = 1 := by
    apply (pow_eq_one_iff_of_nonneg (by positivity : 0 ≤ distribHaarChar K e.det) two_ne_zero).mp
    rw [← map_pow, hdet, map_one]
  have hvector : MeasurePreserving e ν ν := by
    have := IsModuleTopology.isTopologicalAddGroup K W
    refine ⟨(IsModuleTopology.continuous_of_linearMap e.toLinearMap).measurable, ?_⟩
    simp only [e.map_addHaar_eq_smul ν, map_inv, hchar, inv_one, one_smul]
  have hmul : MeasurePreserving (fun w : Multiplicative W ↦ ofAdd (e w.toAdd))
      (ν.map ofAdd) (ν.map ofAdd) := by
    let tag := MeasurableEquiv.multiplicative (α := W)
    have htag : MeasurePreserving tag ν (ν.map ofAdd) := ⟨tag.measurable, rfl⟩
    exact htag.comp (hvector.comp (htag.symm tag))
  have hprod : MeasurePreserving
      (Prod.map _root_.id fun w : Multiplicative W ↦ ofAdd (e w.toAdd))
      (μ.prod (ν.map ofAdd)) (μ.prod (ν.map ofAdd)) := by
    refine ⟨measurable_id.prodMap hmul.measurable, ?_⟩
    by_cases hν : SFinite (ν.map ofAdd)
    · rw [← Measure.map_prod_map _ _ measurable_id hmul.measurable, Measure.map_id, hmul.map_eq]
    · rw [Measure.prod_eq_zero_of_not_sfinite hν, Measure.map_zero]
  have hcoord := B.bilinearFactorSet.measurePreserving_measurableEquivProd μ (ν.map ofAdd)
  have h := (hcoord.symm _).comp (hprod.comp hcoord)
  convert h using 1
  funext p
  simp only [Function.comp_apply, FactorSet.Extension.measurableEquivProd_apply,
    Prod.map_apply, id_eq, FactorSet.Extension.measurableEquivProd_symm_apply,
    isometryGroupToMulAut_apply, e]

end LinearMap.BilinForm
