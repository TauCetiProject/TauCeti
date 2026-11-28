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
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Symplectic invariance of Heisenberg Haar measure

`LinearMap.BilinForm.measurePreserving_isometryGroupToMulAut` shows that the isometry
action on the Heisenberg extension of a left-separating bilinear form on a finite-dimensional
vector space over a locally compact second countable field preserves the product of a central
measure and an additive Haar measure on the vector space. The action fixes the first coordinate
and preserves Haar measure on the second by `LinearMap.BilinForm.measurePreserving_isometryGroup`.
The product argument uses
`MeasureTheory.MeasurePreserving.prodMap_right_self` and
`TauCeti.FactorSet.measurePreserving_prodMeasure`. This includes the symplectic action
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

/-- For a left-separating bilinear form on a finite-dimensional vector space over a locally
compact second countable field, the isometry action preserves the transported product of any
central measure and an additive Haar measure on the vector space.
In particular this holds for symplectic automorphisms and self-dual Haar measures.
See Weil, *Sur certains groupes d'opérateurs unitaires*, I, §§2–4. -/
theorem measurePreserving_isometryGroupToMulAut (B : BilinForm K W)
    (g : LinearMap.isometryGroup B) (hB : B.SeparatingLeft)
    (μ : Measure (Multiplicative K)) (ν : Measure W) [ν.IsAddHaarMeasure] :
    MeasurePreserving (B.isometryGroupToMulAut g)
      (B.bilinearFactorSet.prodMeasure μ (ν.map ofAdd))
      (B.bilinearFactorSet.prodMeasure μ (ν.map ofAdd)) := by
  let e : W ≃ₗ[K] W := g
  have htag : MeasurePreserving ofAdd ν (ν.map ofAdd) :=
    measurable_ofAdd.measurePreserving ν
  have huntag : MeasurePreserving toAdd (ν.map ofAdd) ν :=
    MeasurableEquiv.multiplicative.measurePreserving_symm ν
  have hvector : MeasurePreserving e ν ν := B.measurePreserving_isometryGroup g hB ν
  have hmul : MeasurePreserving (ofAdd ∘ (e : W → W) ∘ toAdd) (ν.map ofAdd) (ν.map ofAdd) :=
    htag.comp (hvector.comp huntag)
  apply B.bilinearFactorSet.measurePreserving_prodMeasure
    ((MeasurePreserving.id μ).prodMap_right_self hmul)
  intro p
  simp only [FactorSet.Extension.measurableEquivProd_apply, Prod.map_apply, id_eq,
    Function.comp_apply, isometryGroupToMulAut_apply, e]

end LinearMap.BilinForm
