/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.MeasureTheory.Group.Prod

/-!
# Product Haar measure on factor-set extensions

`TauCeti.FactorSet.prodMeasure` transports the product of the coefficient and
quotient measures across `TauCeti.FactorSet.Extension.homeomorphProd`. For a measurable
factor set, `TauCeti.FactorSet.isHaarMeasure_prodMeasure` gives left Haar measure when the
quotient acts by measure-preserving maps on the coefficients.
`TauCeti.FactorSet.isMulRightInvariant_prodMeasure` gives right invariance for right invariant
factor measures and measurable orbit maps. Both apply to bilinear Heisenberg extensions with
additive Haar measures. `TauCeti.FactorSet.measurePreserving_prodMeasure` transfers
measure preservation from product coordinates to a map between extensions via Mathlib's
`MeasureTheory.MeasurePreserving.comp_left_iff`. The translation proofs use Mathlib's
`MeasureTheory.MeasurePreserving.skew_product` and `TauCeti.measurePreserving_skew_mul_right`.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), I, §§2–4.
-/

public section

open MeasureTheory
open scoped ENNReal
open Set

namespace TauCeti.FactorSet

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [MeasurableSpace G] [MeasurableSpace M]

namespace Extension

variable (α : FactorSet G M)

/-- The measurable structure transported from the product of the coefficient and quotient. -/
instance instMeasurableSpace : MeasurableSpace α.Extension :=
  MeasurableSpace.comap (equivProd α) inferInstance

/-- Factor-set coordinates as a measurable equivalence. -/
def measurableEquivProd : α.Extension ≃ᵐ M × G where
  toEquiv := equivProd α
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_comap_iff.mpr (by simpa only [Equiv.self_comp_symm] using
    (measurable_id : Measurable (id : M × G → M × G)))

/-- The measurable coordinate map reads the coefficient and quotient. -/
@[simp]
theorem measurableEquivProd_apply (x : α.Extension) :
    measurableEquivProd α x = (x.left, x.right) :=
  equivProd_apply x

/-- The inverse measurable coordinate map assembles the coefficient and quotient. -/
@[simp]
theorem measurableEquivProd_symm_apply (p : M × G) :
    (measurableEquivProd α).symm p = ⟨p.1, p.2⟩ :=
  equivProd_symm_apply p

/-- The measurable structure in factor-set coordinates is Borel when the product structure is. -/
instance instBorelSpace [TopologicalSpace G] [TopologicalSpace M] [BorelSpace (M × G)] :
    BorelSpace α.Extension := by
  have hcoe : (measurableEquivProd α : α.Extension → M × G) = homeomorphProd α :=
    funext fun x ↦ (measurableEquivProd_apply α x).trans (homeomorphProd_apply x).symm
  exact (measurableEquivProd α).measurableEmbedding.borelSpace
    (hcoe.symm ▸ (homeomorphProd α).isInducing)

end Extension

open Extension

/-- The product of the coefficient and quotient measures, in factor-set coordinates. -/
noncomputable def prodMeasure (α : FactorSet G M) (μ : Measure M) (ν : Measure G) :
    Measure α.Extension :=
  (μ.prod ν).map (measurableEquivProd α).symm

/-- The transported product is the pushforward by the inverse coordinate equivalence. -/
theorem prodMeasure_def (α : FactorSet G M) (μ : Measure M) (ν : Measure G) :
    prodMeasure α μ ν = (μ.prod ν).map (measurableEquivProd α).symm :=
  (rfl)

/-- The coordinate equivalence sends the transported measure to the original product. -/
theorem measurePreserving_measurableEquivProd (α : FactorSet G M) (μ : Measure M) (ν : Measure G) :
    MeasurePreserving (measurableEquivProd α) (prodMeasure α μ ν) (μ.prod ν) :=
  (measurableEquivProd α).symm.measurePreserving_symm (μ.prod ν)

/-- A coordinate rectangle has measure equal to the product of the measures of its sides. -/
@[simp]
theorem prodMeasure_preimage_prod (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    [SFinite ν] (s : Set M) (t : Set G) :
    α.prodMeasure μ ν ((measurableEquivProd α) ⁻¹' (s ×ˢ t)) = μ s * ν t := by
  rw [(α.measurePreserving_measurableEquivProd μ ν).measure_preimage_equiv, Measure.prod_prod]

/-- Rescaling the coefficient measure rescales the transported product. -/
theorem prodMeasure_smul_left (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    (c : ℝ≥0∞) :
    prodMeasure α (c • μ) ν = c • prodMeasure α μ ν := by
  by_cases hν : SFinite ν
  swap
  · simp only [prodMeasure_def, Measure.prod_eq_zero_of_not_sfinite hν, Measure.map_zero, smul_zero]
  rw [prodMeasure_def, prodMeasure_def, Measure.prod_smul_left, Measure.map_smul _
    (measurableEquivProd α).symm.measurable.aemeasurable]

/-- Rescaling the quotient measure rescales the transported product. -/
theorem prodMeasure_smul_right (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    (c : ℝ≥0∞) [SFinite ν] :
    prodMeasure α μ (c • ν) = c • prodMeasure α μ ν := by
  rw [prodMeasure_def, prodMeasure_def, Measure.prod_smul_right, Measure.map_smul _
    (measurableEquivProd α).symm.measurable.aemeasurable]

section Transport

variable {H N : Type*} [Group H] [CommGroup N] [MulDistribMulAction H N]
  [MeasurableSpace H] [MeasurableSpace N]
  {μ : Measure M} {ν : Measure G} {μ' : Measure N} {ν' : Measure H}

/-- A map between extensions preserves their transported product measures if its coordinate
expression preserves the product of the factor measures. -/
theorem measurePreserving_prodMeasure (α : FactorSet G M) {β : FactorSet H N}
    {f : α.Extension → β.Extension} {g : M × G → N × H}
    (hg : MeasurePreserving g (μ.prod ν) (μ'.prod ν'))
    (hf : ∀ x, g (measurableEquivProd α x) = measurableEquivProd β (f x)) :
    MeasurePreserving f (α.prodMeasure μ ν) (β.prodMeasure μ' ν') := by
  apply (β.measurePreserving_measurableEquivProd μ' ν').comp_left_iff.mp
  have hcomp : g ∘ measurableEquivProd α = measurableEquivProd β ∘ f := funext hf
  rw [← hcomp]
  exact hg.comp (α.measurePreserving_measurableEquivProd μ ν)

/-- For s-finite factor measures, a map between extensions preserves their transported
product measures if its expression in swapped coordinates preserves the swapped products. -/
theorem measurePreserving_prodMeasure_of_swap (α : FactorSet G M) {β : FactorSet H N}
    [SFinite μ] [SFinite ν] [SFinite μ'] [SFinite ν'] {f : α.Extension → β.Extension}
    {g : G × M → H × N} (hg : MeasurePreserving g (ν.prod μ) (ν'.prod μ'))
    (hf : ∀ x, g (x.right, x.left) = ((f x).right, (f x).left)) :
    MeasurePreserving f (α.prodMeasure μ ν) (β.prodMeasure μ' ν') :=
  α.measurePreserving_prodMeasure
    (Measure.measurePreserving_swap.comp (hg.comp Measure.measurePreserving_swap))
    (fun x ↦ by simp only [Function.comp_apply, measurableEquivProd_apply, Prod.swap, hf])

end Transport

variable [MeasurableMul G] [MeasurableMul₂ M]

/-- The product measure is left invariant when both factors are left invariant and the
quotient action preserves the coefficient measure. -/
theorem isMulLeftInvariant_prodMeasure (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    [SFinite μ] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hα : Measurable ⇑α) (hsmul : ∀ g : G, MeasurePreserving (g • ·) μ μ) :
    (prodMeasure α μ ν).IsMulLeftInvariant := by
  by_cases hν : SFinite ν
  swap
  · simp only [prodMeasure_def, Measure.prod_eq_zero_of_not_sfinite hν, Measure.map_zero]
    exact ⟨fun _ ↦ Measure.map_zero _⟩
  constructor
  intro x
  have hfactor : Measurable fun g : G ↦ α (x.right, g) :=
    hα.comp (measurable_const.prodMk measurable_id)
  have hskew := (measurePreserving_mul_left ν x.right).skew_product
    (g := fun g m ↦ x.left * (x.right • m) * α (x.right, g))
    ((hsmul x.right).measurable.comp measurable_snd |>.const_mul x.left |>.mul
      (hfactor.comp measurable_fst))
    (Filter.Eventually.of_forall fun g ↦ by
      simpa only [mul_comm (α (x.right, g))] using
        (((hsmul x.right).mul_left μ x.left).mul_left μ (α (x.right, g))).map_eq)
  exact (α.measurePreserving_prodMeasure_of_swap hskew (by
    intro y
    simp only [mul_left, mul_right])).map_eq

/-- The product measure is right invariant when both factors are right invariant and the
orbit maps of the coefficient action are measurable. -/
theorem isMulRightInvariant_prodMeasure (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    [SFinite μ] [μ.IsMulRightInvariant] [ν.IsMulRightInvariant]
    (hα : Measurable ⇑α) (hsmul : ∀ m : M, Measurable (· • m : G → M)) :
    (prodMeasure α μ ν).IsMulRightInvariant := by
  by_cases hν : SFinite ν
  swap
  · simp only [prodMeasure_def, Measure.prod_eq_zero_of_not_sfinite hν, Measure.map_zero]
    exact ⟨fun _ ↦ Measure.map_zero _⟩
  constructor
  intro x
  have hshift : Measurable fun g : G ↦ (g • x.left) * α (g, x.right) :=
    (hsmul x.left).mul (hα.comp (measurable_id.prodMk measurable_const))
  have hskew := measurePreserving_skew_mul_right ν μ x.right hshift
  exact (α.measurePreserving_prodMeasure_of_swap hskew (by
    intro y
    simp only [mul_left, mul_right, mul_assoc])).map_eq

/-- For a measurable factor set, the transported product of Haar measures is Haar if the
coordinate product is Borel and the quotient action preserves the coefficient Haar measure. -/
theorem isHaarMeasure_prodMeasure (α : FactorSet G M) (μ : Measure M) (ν : Measure G)
    [TopologicalSpace G] [TopologicalSpace M] [BorelSpace (M × G)]
    [μ.IsHaarMeasure] [ν.IsHaarMeasure] [SFinite μ] [SFinite ν]
    (hα : Measurable ⇑α) (hsmul : ∀ g : G, MeasurePreserving (g • ·) μ μ) :
    (prodMeasure α μ ν).IsHaarMeasure := by
  have hmap : prodMeasure α μ ν = (μ.prod ν).map (homeomorphProd α).symm := by
    rw [prodMeasure_def]
    congr 1
    funext p
    rw [measurableEquivProd_symm_apply, homeomorphProd_symm_apply]
  rw [hmap]
  exact {
    toIsMulLeftInvariant := hmap ▸ isMulLeftInvariant_prodMeasure α μ ν hα hsmul
    toIsFiniteMeasureOnCompacts :=
      Measure.IsFiniteMeasureOnCompacts.map (μ.prod ν) (homeomorphProd α).symm
    toIsOpenPosMeasure := (homeomorphProd α).symm.continuous.isOpenPosMeasure_map
      (homeomorphProd α).symm.surjective }

end TauCeti.FactorSet
