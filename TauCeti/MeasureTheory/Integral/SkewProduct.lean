/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.RCLike.Basic

/-!
# Skew-product Fubini and group-convolution pairing

This file provides Fubini identities along measure-preserving maps from a product space and along
skew-product transformations (k, g) ↦ (k, T k g) whose fibres preserve the second measure, together
with the resulting group-convolution pairing identity for a left-invariant measure on a group.

## Main results

* TauCeti.integral_integral_comp_of_measurePreserving: Fubini's theorem along a
  measure-preserving map T : W × Z → Y carrying ν.prod μ to ρ.
* TauCeti.integrable_integral_skew_product: integrability of g ↦ ∫ k, f (k, T k g) ∂ν when each
  T k preserves μ.
* TauCeti.integral_integral_skew_product:
  ∫ g, ∫ k, f (k, T k g) ∂ν ∂μ = ∫ k, ∫ g, f (k, g) ∂μ ∂ν.
* TauCeti.integral_smul_integral_eq_integral_conv_smul: for a left-invariant measure μ on a
  group Z, ∫ x, k x • ∫ g, α g • F (j x * g) ∂μ ∂ν = ∫ g, (∫ x, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ.

## Provenance

Generalized from MeasureTheory.MeasurePreserving.integral_integral_comp,
New.integral_skew_product, New.integral_integral_skew_product, and
New.integral_smul_integral_eq_integral_conv_smul in src/Lib/General/Measure/IdempotentKernel.lean
of [grh-lean](https://github.com/lsernau/grh-lean) at commit
72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open MeasureTheory

namespace TauCeti

section SkewProduct

variable {W Z X : Type*} [MeasurableSpace W] [MeasurableSpace Z]
  {ν : Measure W} {μ : Measure Z} [SFinite ν] [SFinite μ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Fubini's theorem along a measure-preserving map T : W × Z → Y carrying ν.prod μ to ρ:
for any ρ-integrable , ∫ k, ∫ g, f (T (k, g)) ∂μ ∂ν = ∫ y, f y ∂ρ. -/
theorem integral_integral_comp_of_measurePreserving {Y : Type*} [MeasurableSpace Y]
    {ρ : Measure Y} {T : W × Z → Y} {f : Y → X}
    (hT : MeasurePreserving T (ν.prod μ) ρ) (hf : Integrable f ρ) :
    ∫ k : W, ∫ g : Z, f (T (k, g)) ∂μ ∂ν = ∫ y : Y, f y ∂ρ :=
  calc ∫ k : W, ∫ g : Z, f (T (k, g)) ∂μ ∂ν
      = ∫ z : W × Z, f (T z) ∂(ν.prod μ) :=
        (integral_prod (f ∘ T) (hT.integrable_comp_of_integrable hf)).symm
    _ = ∫ y : Y, f y ∂ρ := by
      rw [← hT.map_eq, integral_map hT.measurable.aemeasurable]
      simpa only [hT.map_eq] using hf.aestronglyMeasurable

/-- If T : W → Z → Z is jointly measurable, each T k preserves μ, and  is
(ν.prod μ)-integrable, then g ↦ ∫ k, f (k, T k g) ∂ν is μ-integrable. -/
theorem integrable_integral_skew_product {T : W → Z → Z}
    (hT_map : ∀ k : W, μ.map (T k) = μ) {f : W × Z → X} (hf : Integrable f (ν.prod μ))
    (hT : Measurable T.uncurry := by fun_prop) :
    Integrable (fun g : Z ↦ ∫ k : W, f (k, T k g) ∂ν) μ :=
  have h_pres : MeasurePreserving (fun p : W × Z ↦ (p.fst, T p.fst p.snd))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hT (.of_forall hT_map)
  (h_pres.integrable_comp_of_integrable hf).integral_prod_right

/-- Skew-product Fubini's theorem: if T : W → Z → Z is jointly measurable, each T k preserves
μ, and  is (ν.prod μ)-integrable, then
∫ g, ∫ k, f (k, T k g) ∂ν ∂μ = ∫ k, ∫ g, f (k, g) ∂μ ∂ν. -/
theorem integral_integral_skew_product {T : W → Z → Z}
    (hT_map : ∀ k : W, μ.map (T k) = μ) {f : W × Z → X} (hf : Integrable f (ν.prod μ))
    (hT : Measurable T.uncurry := by fun_prop) :
    ∫ g : Z, ∫ k : W, f (k, T k g) ∂ν ∂μ = ∫ k : W, ∫ g : Z, f (k, g) ∂μ ∂ν := by
  have h_pres : MeasurePreserving (fun p : W × Z ↦ (p.fst, T p.fst p.snd))
      (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hT (.of_forall hT_map)
  have h_int : Integrable (fun p : W × Z ↦ f (p.fst, T p.fst p.snd)) (ν.prod μ) :=
    h_pres.integrable_comp_of_integrable hf
  calc ∫ g : Z, ∫ k : W, f (k, T k g) ∂ν ∂μ
      = ∫ k : W, ∫ g : Z, f (k, T k g) ∂μ ∂ν := integral_integral_swap h_int.swap
    _ = ∫ p : W × Z, f p ∂(ν.prod μ) := integral_integral_comp_of_measurePreserving h_pres hf
    _ = ∫ k : W, ∫ g : Z, f (k, g) ∂μ ∂ν := integral_prod f hf

/-- Let μ be a left-invariant measure on a group Z, j : W → Z measurable, k and α
integrable, and F strongly measurable and uniformly bounded. Then
∫ x, k x • ∫ g, α g • F (j x * g) ∂μ ∂ν = ∫ g, (∫ x, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ. -/
theorem integral_smul_integral_eq_integral_conv_smul {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 X] [CompleteSpace X]
    [Group Z] [MeasurableMul₂ Z] [MeasurableInv Z] [μ.IsMulLeftInvariant]
    (j : W → Z) {k : W → 𝕜} {α : Z → 𝕜} {F : Z → X} (hk : Integrable k ν) (hα : Integrable α μ)
    (hF_meas : StronglyMeasurable F) (hF_bdd : ∃ C : ℝ, ∀ g : Z, ‖F g‖ ≤ C)
    (hj : Measurable j := by fun_prop) :
    ∫ x : W, k x • ∫ g : Z, α g • F (j x * g) ∂μ ∂ν =
      ∫ g : Z, (∫ x : W, k x * α ((j x)⁻¹ * g) ∂ν) • F g ∂μ := by
  obtain ⟨C, hC⟩ := hF_bdd
  have h_mul : Measurable fun p : W × Z ↦ j p.fst * p.snd := by fun_prop
  have h_top : MemLp (fun p : W × Z ↦ F (j p.fst * p.snd)) ⊤ (ν.prod μ) :=
    memLp_top_of_bound (hF_meas.comp_measurable h_mul).aestronglyMeasurable C
      (.of_forall fun _ ↦ hC _)
  have h_int : Integrable (fun p : W × Z ↦ (k p.fst * α p.snd) • F (j p.fst * p.snd))
      (ν.prod μ) :=
    (hk.mul_prod hα).smul_of_top_left h_top
  have h_skew := integral_integral_skew_product (fun x : W ↦ map_mul_left_eq_self μ (j x)⁻¹) h_int
  simpa [← integral_smul, ← integral_smul_const, smul_smul] using h_skew.symm

end SkewProduct

end TauCeti
