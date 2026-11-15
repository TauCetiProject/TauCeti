/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod

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

end MeasureTheory.Measure
