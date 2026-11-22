/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.Prod
public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.Distributions.Bernoulli.Measurability
public import TauCeti.Topology.UnitInterval.NNReal

/-!
# Poisson acceptance regions and monotone coupling

Restrict a Poisson random measure on a product to a measurable acceptance region, then project
onto the first coordinate. For a product intensity `Λ.prod Q` or a composition-product intensity
`Λ ⊗ₘ κ`, the resulting intensity is the ground measure weighted by the masses of the vertical
sections. In particular, selecting a mark from a location-dependent Bernoulli kernel
`Kernel.bernoulli` weights `Λ` by `p` or `unitInterval.symm ∘ p`, while a null mark region
projects to the zero measure almost surely. For Lebesgue marks and a region below a measurable
density, this is precisely the measure with that density. Infinite density values are allowed.

Using the same Poisson measure for two ordered densities gives an ordered pair of random
measures on the original sample space. This is the acceptance-region construction of monotone
Poisson coupling; it does not assert independence of the two outputs or construct the driver.
No simplicity, atomlessness of the ground intensity, or topology on its space is required.

The construction follows G. Last and M. Penrose, *Lectures on the Poisson Process* (2018),
Chapter 5 (restriction, mapping, and thinning).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  {P : Measure Ω} {Λ : Measure X} {Q : Measure E} {κ : Kernel X E} {M : Ω → Measure (X × E)}

/-- Projecting the accepted occurrences of a product-intensity Poisson random measure is
Poisson, with density equal to the mark measure of each acceptance section. Multiplicities
are retained, and the acceptance region need not have finite intensity. -/
theorem IsPoissonRandomMeasure.acceptance [SFinite Q]
    (hM : IsPoissonRandomMeasure P M (Λ.prod Q))
    {A : Set (X × E)} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict A).map Prod.fst)
      (Λ.withDensity fun x ↦ Q (Prod.mk x ⁻¹' A)) := by
  simpa only [Measure.map_fst_restrict_prod_eq_withDensity Λ Q hA] using
    (hM.restrict hA).map measurable_fst

/-- Selecting a measurable mark set from a product-intensity Poisson measure and projecting
onto the ground space multiplies the intensity by the mass of that mark set. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod [SFinite Q]
    (hM : IsPoissonRandomMeasure P M (Λ.prod Q))
    {A : Set E} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ A)).map Prod.fst)
      (Q A • Λ) := by
  simpa only [mk_preimage_prod_right (mem_univ _), withDensity_const] using
    hM.acceptance (MeasurableSet.univ.prod hA)

/-- Restricting a Poisson random measure with composition-product intensity `Λ ⊗ₘ κ` to a
measurable set `A` and projecting onto `X` gives a Poisson random measure whose intensity weights
`Λ` by the section masses `x ↦ κ x (Prod.mk x ⁻¹' A)`. -/
theorem IsPoissonRandomMeasure.map_fst_restrict_compProd [SFinite Λ] [IsSFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {A : Set (X × E)} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict A).map Prod.fst)
      (Λ.withDensity fun x ↦ κ x (Prod.mk x ⁻¹' A)) := by
  simpa only [Measure.map_fst_restrict_compProd_eq_withDensity Λ κ hA] using
    (hM.restrict hA).map measurable_fst

/-- Projecting occurrences whose marks fall in a measurable mark set `B` produces a Poisson random
measure on `X` with intensity `Λ.withDensity (fun x ↦ κ x B)`. -/
theorem IsPoissonRandomMeasure.map_fst_restrict_univ_prod_compProd [SFinite Λ] [IsSFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {B : Set E} (hB : MeasurableSet B) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ B)).map Prod.fst)
      (Λ.withDensity fun x ↦ κ x B) := by
  simpa using hM.map_fst_restrict_compProd (MeasurableSet.univ.prod hB)

/-- Selecting the first atom `a` from a Poisson random measure with Bernoulli kernel intensity
`Λ ⊗ₘ Kernel.bernoulli a b hp` (with `a ≠ b`) weights `Λ` by `p`. -/
theorem IsPoissonRandomMeasure.acceptance_compProd_bernoulli_left [SFinite Λ]
    {a b : E} (ha : MeasurableSet ({a} : Set E)) (hab : a ≠ b)
    {p : X → unitInterval} {hp : Measurable p}
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ Kernel.bernoulli a b hp)) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {a})).map Prod.fst)
      (Λ.withDensity fun x ↦ (unitInterval.toNNReal (p x) : ℝ≥0∞)) := by
  simpa only [Kernel.bernoulli_apply_singleton_left ha hab] using
    hM.map_fst_restrict_univ_prod_compProd ha

/-- Selecting the second atom `b` from a Poisson random measure with Bernoulli kernel intensity
`Λ ⊗ₘ Kernel.bernoulli a b hp` (with `a ≠ b`) weights `Λ` by `unitInterval.symm ∘ p`. -/
theorem IsPoissonRandomMeasure.acceptance_compProd_bernoulli_right [SFinite Λ]
    {a b : E} (hb : MeasurableSet ({b} : Set E)) (hab : a ≠ b)
    {p : X → unitInterval} {hp : Measurable p}
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ Kernel.bernoulli a b hp)) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (Λ.withDensity fun x ↦ (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) := by
  simpa only [Kernel.bernoulli_apply_singleton_right hb hab] using
    hM.map_fst_restrict_univ_prod_compProd hb

/-- Selecting colour `b : Bool` from a Poisson random measure with Boolean Bernoulli kernel
intensity `Λ ⊗ₘ Kernel.bernoulli true false hp` weights `Λ` by `p` (for `true`) or
`unitInterval.symm ∘ p` (for `false`). Endpoint values `0` and `1` are allowed. -/
theorem IsPoissonRandomMeasure.acceptance_compProd_bernoulli [SFinite Λ]
    {M : Ω → Measure (X × Bool)} {p : X → unitInterval} {hp : Measurable p}
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ Kernel.bernoulli true false hp)) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (Λ.withDensity fun x ↦
        (unitInterval.toNNReal (if b then p x else unitInterval.symm (p x)) : ℝ≥0∞)) := by
  simpa only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool,
    ← unitInterval.toNNReal_symm, apply_ite unitInterval.toNNReal] using
    hM.map_fst_restrict_univ_prod_compProd (measurableSet_singleton b)

/-- If a product-space Poisson random measure has zero intensity on `univ ×ˢ B`, then the
ground projection of its restriction to `univ ×ˢ B` vanishes almost surely. No measurability
assumption on `B` is required. -/
theorem IsPoissonRandomMeasure.ae_map_fst_restrict_univ_prod_eq_zero
    {Γ : Measure (X × E)} (hM : IsPoissonRandomMeasure P M Γ) {B : Set E}
    (hzero : Γ (univ ×ˢ B) = 0) :
    ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ B)).map Prod.fst = 0 := by
  filter_upwards [hM.ae_eq_zero hzero] with ω hω
  rw [← Measure.measure_univ_eq_zero, Measure.map_fst_restrict_prod_apply _ _ _ MeasurableSet.univ,
    univ_inter]
  exact hω

/-- Selecting a finite-mass mark set from a scaled product intensity multiplies the ground
scale by the mass of that mark set, including scale zero. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod_smul [SFinite Q] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P M (((r : ℝ≥0∞) • Λ).prod Q))
    {A : Set E} (hA : MeasurableSet A) (hQA : Q A ≠ ∞ := by finiteness) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ A)).map Prod.fst)
      (((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • Λ) := by
  have hscale : Q A • (r : ℝ≥0∞) • Λ =
      ((r * (Q A).toNNReal : ℝ≥0) : ℝ≥0∞) • Λ := by
    rw [smul_smul, ENNReal.coe_mul, ENNReal.coe_toNNReal hQA, mul_comm]
  simpa only [hscale] using h.acceptance_univ_prod hA

/-- Bernoulli mark selection scales an arbitrary ground intensity by `p` or `1-p`,
including both endpoint parameters. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod_singleton_of_bernoulliMeasure
    {M : Ω → Measure (X × Bool)} {p : unitInterval}
    (h : IsPoissonRandomMeasure P M (Λ.prod (bernoulliMeasure true false p))) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (((if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) := by
  simpa only [bernoulliMeasure_apply_singleton_bool] using
    h.acceptance_univ_prod (measurableSet_singleton b)

/-- Bernoulli colour selection splits a scaled ground intensity into scales `r*p` and
`r*(1-p)`, including both endpoint parameters and scale zero. -/
theorem IsPoissonRandomMeasure.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure
    {M : Ω → Measure (X × Bool)} {r : ℝ≥0} {p : unitInterval}
    (h : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • Λ).prod (bernoulliMeasure true false p))) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) := by
  simpa only [smul_smul, ENNReal.coe_mul, mul_comm] using
    h.acceptance_univ_prod_singleton_of_bernoulliMeasure b

/-- Accepting a Lebesgue mark `u` exactly when `u ≤ f x` produces a Poisson random measure
with intensity `Λ.withDensity f`, including at zero and infinite values of `f`. -/
theorem IsPoissonRandomMeasure.acceptance_le
    {M : Ω → Measure (X × ℝ≥0)}
    (hM : IsPoissonRandomMeasure P M (Λ.prod nnvolume))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    IsPoissonRandomMeasure P
      (fun ω ↦ ((M ω).restrict {p | (p.2 : ℝ≥0∞) ≤ f p.1}).map Prod.fst)
      (Λ.withDensity f) := by
  have hA : MeasurableSet {p : X × ℝ≥0 | (p.2 : ℝ≥0∞) ≤ f p.1} :=
    measurableSet_le measurable_snd.coe_nnreal_ennreal (hf.comp measurable_fst)
  simpa only [preimage_ofPred_eq, nnvolume_setOf_coe_le] using hM.acceptance hA

/-- Ordered measurable densities admit an ordered Poisson coupling on the sample space of
the given product-intensity Poisson measure. The domination holds for every sample, not just
almost surely. -/
theorem IsPoissonRandomMeasure.exists_monotone_coupling
    {M : Ω → Measure (X × ℝ≥0)}
    (hM : IsPoissonRandomMeasure P M (Λ.prod nnvolume))
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hfg : f ≤ g) :
    ∃ N₁ N₂ : Ω → Measure X,
      IsPoissonRandomMeasure P N₁ (Λ.withDensity f) ∧
      IsPoissonRandomMeasure P N₂ (Λ.withDensity g) ∧ ∀ ω, N₁ ω ≤ N₂ ω := by
  refine ⟨_, _, hM.acceptance_le hf, hM.acceptance_le hg, fun ω ↦ ?_⟩
  exact Measure.map_mono
    ((M ω).restrict_mono_set fun p hp ↦ hp.trans (hfg p.1)) measurable_fst

end TauCeti.Probability
