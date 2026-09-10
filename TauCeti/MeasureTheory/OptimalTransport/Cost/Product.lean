/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Transport costs of a product problem

Two transport problems, one from `μ₁` to `ν₁` with cost `c₁` and one from `μ₂` to `ν₂` with cost
`c₂`, assemble into a single problem from `μ₁ ⊗ μ₂` to `ν₁ ⊗ ν₂` whose cost is the *additively
separable* function

`c ((x₁, x₂), (y₁, y₂)) = c₁ (x₁, y₁) + c₂ (x₂, y₂)`.

This file proves that the assembled problem decouples exactly: its value is the sum of the two
values, and rearranging a pair of optimal plans produces an optimal plan of the product problem.

The decoupling is an identity in `ℝ≥0∞`: no value is assumed finite, and both sides are `∞` as
soon as one of the two coordinate values is.

The four marginals are probability measures. That normalisation is what makes the coordinate
pushforwards of a plan of `μ₁ ⊗ μ₂` and `ν₁ ⊗ ν₂` land on `μᵢ` and `νᵢ` rather than on a rescaling
of them; the rearrangement lemma below carries no such hypothesis.

## Main statements

* `TauCeti.IsCoupling.prodProdProdComm` — rearranging the product of two plans gives a plan of the
  product problem, and `TauCeti.lintegral_map_prodProdProdComm` computes its separable cost;
* `TauCeti.transportCost_prod_add` — the value of an additively separable cost on a product of two
  transport problems is the sum of the two values;
* `TauCeti.IsOptimalCoupling.prod` — rearranging the product of two optimal plans gives an optimal
  plan for the separable cost.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6, where
  the tensorization of the Wasserstein distance is the special case `cᵢ = dᵢ ^ p` of the identity
  proved here.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

universe u v w

variable {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type*}
  [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
  {c₁ : X₁ × Y₁ → ℝ≥0∞} {c₂ : X₂ × Y₂ → ℝ≥0∞}
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν₁ : Measure Y₁} {ν₂ : Measure Y₂}
  {π₁ : Measure (X₁ × Y₁)} {π₂ : Measure (X₂ × Y₂)}

/-- **Rearranging a product of plans.** Exchanging the two middle coordinates of the product of a
plan of `μ₁, ν₁` and a plan of `μ₂, ν₂` gives a plan of `μ₁ ⊗ μ₂` and `ν₁ ⊗ ν₂`. -/
protected theorem IsCoupling.prodProdProdComm [SFinite π₁] [SFinite π₂]
    (h₁ : IsCoupling π₁ μ₁ ν₁) (h₂ : IsCoupling π₂ μ₂ ν₂) :
    IsCoupling ((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2)))
      (μ₁.prod μ₂) (ν₁.prod ν₂) := by
  have hX : Measurable (Prod.map Prod.fst Prod.fst : (X₁ × Y₁) × X₂ × Y₂ → X₁ × X₂) :=
    measurable_fst.prodMap measurable_fst
  have hY : Measurable (Prod.map Prod.snd Prod.snd : (X₁ × Y₁) × X₂ × Y₂ → Y₁ × Y₂) :=
    measurable_snd.prodMap measurable_snd
  constructor
  · have h : ((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2))).fst
        = (π₁.prod π₂).map (Prod.map Prod.fst Prod.fst) :=
      Measure.fst_map_prodMk hX hY
    rw [h, ← Measure.map_prod_map π₁ π₂ measurable_fst measurable_fst]
    exact congrArg₂ Measure.prod h₁.fst_eq h₂.fst_eq
  · have h : ((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2))).snd
        = (π₁.prod π₂).map (Prod.map Prod.snd Prod.snd) :=
      Measure.snd_map_prodMk hX hY
    rw [h, ← Measure.map_prod_map π₁ π₂ measurable_snd measurable_snd]
    exact congrArg₂ Measure.prod h₁.snd_eq h₂.snd_eq

/-- The cost of a rearranged product of plans is the sum of the two coordinate costs. -/
theorem lintegral_map_prodProdProdComm [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) :
    ∫⁻ z : (X₁ × X₂) × Y₁ × Y₂, (c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2))
        ∂((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2)))
      = ∫⁻ u, c₁ u ∂π₁ + ∫⁻ v, c₂ v ∂π₂ := by
  have hm : Measurable fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2) :=
    (hc₁.comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).add
      (hc₂.comp ((measurable_snd.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_snd)))
  have hg : Measurable fun w : (X₁ × Y₁) × X₂ × Y₂ ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2)) :=
    (((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  rw [lintegral_map (f := fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2))
    (g := fun w : (X₁ × Y₁) × X₂ × Y₂ ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2))) hm hg]
  simpa using (isCoupling_prod π₁ π₂).lintegral_add_split hc₁ hc₂ 0

section Separable

variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]

/-- **The transport cost of a product problem splits.** For an additively separable cost on a
product of two transport problems between probability measures, the value of the assembled problem
is the sum of the two coordinate values.

No coordinate value is assumed finite: both sides are `∞` as soon as one of them is. -/
theorem transportCost_prod_add (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) :
    transportCost (fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2))
        (μ₁.prod μ₂) (ν₁.prod ν₂)
      = transportCost c₁ μ₁ ν₁ + transportCost c₂ μ₂ ν₂ := by
  have hm₁ : Measurable fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) :=
    hc₁.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
  refine le_antisymm ?_ (le_transportCost fun π hπ ↦ ?_)
  · rw [transportCost_def (c := c₁) (μ := μ₁) (ν := ν₁),
      transportCost_def (c := c₂) (μ := μ₂) (ν := ν₂)]
    refine ENNReal.le_iInf₂_add_iInf₂ fun σ₁ hσ₁ σ₂ hσ₂ ↦ ?_
    have : IsProbabilityMeasure σ₁ := hσ₁.isProbabilityMeasure
    have : IsProbabilityMeasure σ₂ := hσ₂.isProbabilityMeasure
    exact (transportCost_le_lintegral (hσ₁.prodProdProdComm hσ₂) _).trans_eq
      (lintegral_map_prodProdProdComm hc₁ hc₂)
  · have eμ₁ : Measure.map Prod.fst (μ₁.prod μ₂) = μ₁ := Measure.fst_prod
    have eν₁ : Measure.map Prod.fst (ν₁.prod ν₂) = ν₁ := Measure.fst_prod
    have eμ₂ : Measure.map Prod.snd (μ₁.prod μ₂) = μ₂ := Measure.snd_prod
    have eν₂ : Measure.map Prod.snd (ν₁.prod ν₂) = ν₂ := Measure.snd_prod
    have hπ₁ : IsCoupling (π.map (Prod.map Prod.fst Prod.fst)) μ₁ ν₁ := by
      simpa only [eμ₁, eν₁] using hπ.map measurable_fst measurable_fst
    have hπ₂ : IsCoupling (π.map (Prod.map Prod.snd Prod.snd)) μ₂ ν₂ := by
      simpa only [eμ₂, eν₂] using hπ.map measurable_snd measurable_snd
    calc transportCost c₁ μ₁ ν₁ + transportCost c₂ μ₂ ν₂
        ≤ (∫⁻ u, c₁ u ∂π.map (Prod.map Prod.fst Prod.fst))
            + ∫⁻ v, c₂ v ∂π.map (Prod.map Prod.snd Prod.snd) :=
          add_le_add (transportCost_le_lintegral hπ₁ c₁) (transportCost_le_lintegral hπ₂ c₂)
      _ = ∫⁻ z, (c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2)) ∂π := by
          rw [lintegral_map hc₁ (measurable_fst.prodMap measurable_fst),
            lintegral_map hc₂ (measurable_snd.prodMap measurable_snd)]
          exact (lintegral_add_left hm₁ _).symm

/-- Rearranging the product of two optimal plans gives an optimal plan for the additively
separable cost on the product problem. -/
protected theorem IsOptimalCoupling.prod (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (h₁ : IsOptimalCoupling c₁ π₁ μ₁ ν₁) (h₂ : IsOptimalCoupling c₂ π₂ μ₂ ν₂) :
    IsOptimalCoupling (fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2))
      ((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2))) (μ₁.prod μ₂) (ν₁.prod ν₂) := by
  have : IsProbabilityMeasure π₁ := h₁.toIsCoupling.isProbabilityMeasure
  have : IsProbabilityMeasure π₂ := h₂.toIsCoupling.isProbabilityMeasure
  refine ⟨h₁.toIsCoupling.prodProdProdComm h₂.toIsCoupling, ?_⟩
  rw [lintegral_map_prodProdProdComm hc₁ hc₂, h₁.lintegral_eq, h₂.lintegral_eq,
    transportCost_prod_add hc₁ hc₂]

end Separable

end TauCeti
