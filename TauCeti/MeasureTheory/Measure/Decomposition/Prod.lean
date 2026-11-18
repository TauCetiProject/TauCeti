/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Densities against a product of marginals

Let `μ` and `ν` be σ-finite measures on `α` and `β`, and let `m` be an s-finite measure on
`α × β`, absolutely continuous with respect to the product `μ.prod ν`. Integrating the density
`dm/d(μ ⊗ ν)` in the second variable against `ν` gives, `μ`-almost everywhere, the density of the
first marginal of `m` against `μ`; symmetrically, integrating it in the first variable against `μ`
gives, `ν`-almost everywhere, the density of the second marginal of `m` against `ν`.

In particular, if the first marginal of `m` is `μ` (which forces `m` to be σ-finite), then for
`μ`-almost every `x` the density `dm/d(μ ⊗ ν)` integrates to `1` in the second variable against
`ν`: the section `y ↦ dm/d(μ ⊗ ν) (x, y)` is a probability density with respect to `ν`, the
density of the conditional law of the second coordinate given the first. Symmetrically for the
second marginal.

These identities are used for the block approximation of a coupling in entropic optimal
transport: if `π` couples `μ` and `ν` and `p`, `q` are measurable maps on the two factors, then
reweighting `μ ⊗ ν` by the density of `π.map (Prod.map p q)` against `(μ.map p).prod (ν.map q)`,
pulled back along `Prod.map p q`, gives a measure that still has marginals `μ` and `ν`.

We also show that mutual singularity on either factor passes to product measures
(`MeasureTheory.Measure.MutuallySingular.prod_left` and
`MeasureTheory.Measure.MutuallySingular.prod_right`) and deduce that the Radon–Nikodym derivative
of a product of s-finite measures against a product of σ-finite measures factors almost everywhere
as the product of the factor Radon–Nikodym derivatives (`MeasureTheory.Measure.rnDeriv_prod`).
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {m : Measure (α × β)} [SigmaFinite μ] [SigmaFinite ν]

/-- If `m` is s-finite and `m ≪ μ ⊗ ν`, then integrating the density of `m` against `μ ⊗ ν` in the
second variable gives, `μ`-almost everywhere, the density of the first marginal of `m` against
`μ`. -/
theorem lintegral_rnDeriv_prod_right_ae_eq_rnDeriv_fst [SFinite m] (hac : m ≪ μ.prod ν) :
    (fun x ↦ ∫⁻ y, m.rnDeriv (μ.prod ν) (x, y) ∂ν) =ᵐ[μ] m.fst.rnDeriv μ := by
  have hfst : m.fst ≪ μ :=
    (hac.map measurable_fst).trans (by rw [map_fst_prod]; exact smul_absolutelyContinuous)
  have hd := measurable_rnDeriv m (μ.prod ν)
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hd.lintegral_prod_right'
    (measurable_rnDeriv _ _) fun s hs _ ↦ ?_
  calc ∫⁻ x in s, ∫⁻ y, m.rnDeriv (μ.prod ν) (x, y) ∂ν ∂μ
      = ∫⁻ z in s ×ˢ univ, m.rnDeriv (μ.prod ν) z ∂μ.prod ν := by
        rw [setLIntegral_prod _ hd.aemeasurable, restrict_univ]
    _ = ∫⁻ x in s, m.fst.rnDeriv μ x ∂μ := by
        rw [setLIntegral_rnDeriv hac, setLIntegral_rnDeriv hfst, fst_apply hs, prod_univ]

/-- If `m` is s-finite and `m ≪ μ ⊗ ν`, then integrating the density of `m` against `μ ⊗ ν` in the
first variable gives, `ν`-almost everywhere, the density of the second marginal of `m` against
`ν`. -/
theorem lintegral_rnDeriv_prod_left_ae_eq_rnDeriv_snd [SFinite m] (hac : m ≪ μ.prod ν) :
    (fun y ↦ ∫⁻ x, m.rnDeriv (μ.prod ν) (x, y) ∂μ) =ᵐ[ν] m.snd.rnDeriv ν := by
  have hsnd : m.snd ≪ ν :=
    (hac.map measurable_snd).trans (by rw [map_snd_prod]; exact smul_absolutelyContinuous)
  have hd := measurable_rnDeriv m (μ.prod ν)
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hd.lintegral_prod_left'
    (measurable_rnDeriv _ _) fun t ht _ ↦ ?_
  calc ∫⁻ y in t, ∫⁻ x, m.rnDeriv (μ.prod ν) (x, y) ∂μ ∂ν
      = ∫⁻ z in univ ×ˢ t, m.rnDeriv (μ.prod ν) z ∂μ.prod ν := by
        rw [← prod_restrict, restrict_univ, lintegral_prod_symm _ hd.aemeasurable]
    _ = ∫⁻ y in t, m.snd.rnDeriv ν y ∂ν := by
        rw [setLIntegral_rnDeriv hac, setLIntegral_rnDeriv hsnd, snd_apply ht, univ_prod]

/-- If `m ≪ μ ⊗ ν` has first marginal `μ`, then for `μ`-almost every `x` the density of `m` against
`μ ⊗ ν` integrates to `1` in the second variable. -/
theorem ae_lintegral_rnDeriv_prod_right_eq_one (hm : m.fst = μ) (hac : m ≪ μ.prod ν) :
    ∀ᵐ x ∂μ, ∫⁻ y, m.rnDeriv (μ.prod ν) (x, y) ∂ν = 1 := by
  subst hm
  have : SigmaFinite m := .of_map m measurable_fst.aemeasurable ‹_›
  filter_upwards [lintegral_rnDeriv_prod_right_ae_eq_rnDeriv_fst hac, m.fst.rnDeriv_self]
    with x h h1 using h.trans h1

/-- If `m ≪ μ ⊗ ν` has second marginal `ν`, then for `ν`-almost every `y` the density of `m`
against `μ ⊗ ν` integrates to `1` in the first variable. -/
theorem ae_lintegral_rnDeriv_prod_left_eq_one (hm : m.snd = ν) (hac : m ≪ μ.prod ν) :
    ∀ᵐ y ∂ν, ∫⁻ x, m.rnDeriv (μ.prod ν) (x, y) ∂μ = 1 := by
  subst hm
  have : SigmaFinite m := .of_map m measurable_snd.aemeasurable ‹_›
  filter_upwards [lintegral_rnDeriv_prod_left_ae_eq_rnDeriv_snd hac, m.snd.rnDeriv_self]
    with y h h1 using h.trans h1

/-- If `μ₁ ⟂ₘ ν₁`, then `μ₁ ⊗ μ₂ ⟂ₘ ν₁ ⊗ ν₂` for any measures `μ₂` and `ν₂`. -/
theorem MutuallySingular.prod_left {μ₁ ν₁ : Measure α} (μ₂ ν₂ : Measure β) (h : μ₁ ⟂ₘ ν₁) :
    μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂ := by
  by_cases hμ₂ : SFinite μ₂
  · by_cases hν₂ : SFinite ν₂
    · refine ⟨h.nullSet ×ˢ univ, h.measurableSet_nullSet.prod .univ, ?_, ?_⟩
      · rw [prod_prod, h.measure_nullSet, zero_mul]
      · rw [compl_prod_eq_union, compl_univ, prod_empty, union_empty, prod_prod,
          h.measure_compl_nullSet, zero_mul]
    · simp [prod_eq_zero_of_not_sfinite hν₂]
  · simp [prod_eq_zero_of_not_sfinite hμ₂]

/-- If `μ₂ ⟂ₘ ν₂`, then `μ₁ ⊗ μ₂ ⟂ₘ ν₁ ⊗ ν₂` for any measures `μ₁` and `ν₁`. -/
theorem MutuallySingular.prod_right (μ₁ ν₁ : Measure α) {μ₂ ν₂ : Measure β} (h : μ₂ ⟂ₘ ν₂) :
    μ₁.prod μ₂ ⟂ₘ ν₁.prod ν₂ := by
  by_cases hμ₂ : SFinite μ₂
  · by_cases hν₂ : SFinite ν₂
    · refine ⟨univ ×ˢ h.nullSet, MeasurableSet.univ.prod h.measurableSet_nullSet, ?_, ?_⟩
      · rw [prod_prod, h.measure_nullSet, mul_zero]
      · rw [compl_prod_eq_union, compl_univ, empty_prod, empty_union, prod_prod,
          h.measure_compl_nullSet, mul_zero]
    · simp [prod_eq_zero_of_not_sfinite hν₂]
  · simp [prod_eq_zero_of_not_sfinite hμ₂]

/-- For s-finite measures `μ₁`, `μ₂` and σ-finite measures `ν₁`, `ν₂`, the Radon–Nikodym derivative
of `μ₁ ⊗ μ₂` against `ν₁ ⊗ ν₂` factors `ν₁ ⊗ ν₂`-almost everywhere as the product of the factor
Radon–Nikodym derivatives. No absolute continuity hypothesis is needed: singular parts on either
factor yield product terms mutually singular with `ν₁ ⊗ ν₂`. -/
theorem rnDeriv_prod (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [SFinite μ₁] [SigmaFinite ν₁] [SFinite μ₂] [SigmaFinite ν₂] :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) =ᵐ[ν₁.prod ν₂]
      fun z ↦ μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 := by
  have : SFinite (μ₁.singularPart ν₁) :=
    sfinite_of_absolutelyContinuous (absolutelyContinuous_of_le (singularPart_le _ _))
  have : SFinite (μ₂.singularPart ν₂) :=
    sfinite_of_absolutelyContinuous (absolutelyContinuous_of_le (singularPart_le _ _))
  have hsing : (μ₁.singularPart ν₁).prod μ₂ +
      (ν₁.withDensity (μ₁.rnDeriv ν₁)).prod (μ₂.singularPart ν₂) ⟂ₘ ν₁.prod ν₂ :=
    ((mutuallySingular_singularPart μ₁ ν₁).prod_left μ₂ ν₂).add_left
      ((mutuallySingular_singularPart μ₂ ν₂).prod_right _ ν₁)
  refine (eq_rnDeriv (by fun_prop) hsing ?_).symm
  calc μ₁.prod μ₂
      = (μ₁.singularPart ν₁ + ν₁.withDensity (μ₁.rnDeriv ν₁)).prod μ₂ := by
          rw [← μ₁.haveLebesgueDecomposition_add ν₁]
    _ = (μ₁.singularPart ν₁).prod μ₂ + (ν₁.withDensity (μ₁.rnDeriv ν₁)).prod
          (μ₂.singularPart ν₂ + ν₂.withDensity (μ₂.rnDeriv ν₂)) := by
          rw [add_prod, ← μ₂.haveLebesgueDecomposition_add ν₂]
    _ = ((μ₁.singularPart ν₁).prod μ₂ +
          (ν₁.withDensity (μ₁.rnDeriv ν₁)).prod (μ₂.singularPart ν₂)) +
        (ν₁.prod ν₂).withDensity (fun z ↦ μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) := by
          rw [prod_add, prod_withDensity (measurable_rnDeriv _ _) (measurable_rnDeriv _ _),
            add_assoc]

end MeasureTheory.Measure
