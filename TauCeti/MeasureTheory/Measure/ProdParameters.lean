/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Parameterized product measure-preserving maps

A measure-preserving map `φ : X₁ × X₂ → Z₁ × Z₂` between product measures remains measure
preserving when one or two auxiliary parameter spaces are carried along and reassociated across
the product factors.

## Main results

* `MeasureTheory.MeasurePreserving.prod_param`: carrying a single parameter measure `m` through a
  measure-preserving map `φ : X₁ × X₂ → Z₁ × Z₂` yields a measure-preserving map
  `((x₁, y), x₂) ↦ ((y, (φ (x₁, x₂)).fst), (φ (x₁, x₂)).snd)`.
* `MeasureTheory.MeasurePreserving.prod_two_params`: carrying two parameter measures `m₁`, `m₂`
  through `φ` yields a measure-preserving map
  `(((x₁, y₁), y₂), x₂) ↦ ((y₁, y₂, (φ (x₁, x₂)).fst), (φ (x₁, x₂)).snd)`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/SiegelWeil/Tower/FiniteTateIntegral.lean` (`measurePreserving_prod_parameters`).
-/

@[expose] public section

namespace MeasureTheory

/-- A measure-preserving map `φ : X₁ × X₂ → Z₁ × Z₂` remains measure preserving when an auxiliary
parameter `y` with measure `m` is carried along. -/
theorem MeasurePreserving.prod_param {X₁ X₂ Y Z₁ Z₂ : Type*}
    [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    [MeasurableSpace Z₁] [MeasurableSpace Z₂]
    {ξ₁ : Measure X₁} {ξ₂ : Measure X₂} {ζ₁ : Measure Z₁} {ζ₂ : Measure Z₂}
    [SFinite ξ₁] [SFinite ξ₂] [SFinite ζ₁] [SFinite ζ₂]
    {φ : X₁ × X₂ → Z₁ × Z₂}
    (hφ : MeasurePreserving φ (ξ₁.prod ξ₂) (ζ₁.prod ζ₂))
    (m : Measure Y) [SFinite m] :
    MeasurePreserving
      (fun (((x₁, y), x₂) : (X₁ × Y) × X₂) ↦
        ((y, (φ (x₁, x₂)).fst), (φ (x₁, x₂)).snd))
      ((ξ₁.prod m).prod ξ₂) ((m.prod ζ₁).prod ζ₂) := by
  have h_src : MeasurePreserving (fun (((x₁, y), x₂) : (X₁ × Y) × X₂) ↦ (y, x₁, x₂))
      ((ξ₁.prod m).prod ξ₂) (m.prod (ξ₁.prod ξ₂)) :=
    (measurePreserving_prodAssoc m ξ₁ ξ₂).comp
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id ξ₂))
  have h_tgt : MeasurePreserving (fun ((y, z₁, z₂) : Y × Z₁ × Z₂) ↦ ((y, z₁), z₂))
      (m.prod (ζ₁.prod ζ₂)) ((m.prod ζ₁).prod ζ₂) :=
    (measurePreserving_prodAssoc m ζ₁ ζ₂).symm
  exact h_tgt.comp (((MeasurePreserving.id m).prod hφ).comp h_src)

/-- A measure-preserving map `φ : X₁ × X₂ → Z₁ × Z₂` remains measure preserving when two auxiliary
parameters `y₁` and `y₂` with measures `m₁` and `m₂` are carried along. -/
theorem MeasurePreserving.prod_two_params {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Type*}
    [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    [MeasurableSpace Z₁] [MeasurableSpace Z₂]
    {ξ₁ : Measure X₁} {ξ₂ : Measure X₂} {ζ₁ : Measure Z₁} {ζ₂ : Measure Z₂}
    [SFinite ξ₁] [SFinite ξ₂] [SFinite ζ₁] [SFinite ζ₂]
    {φ : X₁ × X₂ → Z₁ × Z₂}
    (hφ : MeasurePreserving φ (ξ₁.prod ξ₂) (ζ₁.prod ζ₂))
    (m₁ : Measure Y₁) (m₂ : Measure Y₂) [SFinite m₁] [SFinite m₂] :
    MeasurePreserving
      (fun ((((x₁, y₁), y₂), x₂) : ((X₁ × Y₁) × Y₂) × X₂) ↦
        ((y₁, y₂, (φ (x₁, x₂)).fst), (φ (x₁, x₂)).snd))
      (((ξ₁.prod m₁).prod m₂).prod ξ₂) ((m₁.prod (m₂.prod ζ₁)).prod ζ₂) := by
  have h_src : MeasurePreserving
      (fun ((((x₁, y₁), y₂), x₂) : ((X₁ × Y₁) × Y₂) × X₂) ↦ ((x₁, (y₁, y₂)), x₂))
      (((ξ₁.prod m₁).prod m₂).prod ξ₂) ((ξ₁.prod (m₁.prod m₂)).prod ξ₂) :=
    (measurePreserving_prodAssoc ξ₁ m₁ m₂).prod (MeasurePreserving.id ξ₂)
  have h_tgt : MeasurePreserving
      (fun ((((y₁, y₂), z₁), z₂) : ((Y₁ × Y₂) × Z₁) × Z₂) ↦ ((y₁, y₂, z₁), z₂))
      (((m₁.prod m₂).prod ζ₁).prod ζ₂) ((m₁.prod (m₂.prod ζ₁)).prod ζ₂) :=
    (measurePreserving_prodAssoc m₁ m₂ ζ₁).prod (MeasurePreserving.id ζ₂)
  exact h_tgt.comp ((hφ.prod_param (m₁.prod m₂)).comp h_src)

end MeasureTheory
