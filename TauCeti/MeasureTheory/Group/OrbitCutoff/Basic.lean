/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.IdentDistrib

/-!
# Integration over orbit spaces by cutoffs

Let a group `H` with a measure `ν` act measurably on a measure space `(X, μ)`. An integral over the
orbit space `H \ X` can be taken on `X` itself, against a weight whose integral along every orbit is
one. Such a weight is an *orbit cutoff* (`MeasureTheory.IsOrbitCutoff ν β`): a measurable
`β : X → [0, ∞]` with `∫ β (h • x) dν(h) = 1` for every `x`. For an `H`-invariant function `F`,
`∫_{H\X} F` is `∫_X F β dμ`. No orbit space, section or quotient measure is needed, and the action
need not come from a subgroup acting on its group.

When `ν` is invariant under inversion and `μ` is `H`-invariant, both s-finite, the map
`(x, h) ↦ h • x` carries `(β μ) × ν` to `μ` (`MeasureTheory.IsOrbitCutoff.measurePreserving_smul`).
This is the unfolding identity `∫_X (∫_H f (h • x) dν(h)) β(x) dμ(x) = ∫_X f dμ`, from which the
rest follows by Fubini's theorem. In particular an invariant function has the same distribution
under `β μ` for every cutoff `β` (`MeasureTheory.IsOrbitCutoff.identDistrib_withDensity`), so the
integral over the orbit space does not depend on the cutoff.

`MeasureTheory.Measure.cutoffMeasure ν μ` is `μ` weighted by a cutoff chosen once and for all; it is
the measure that computes integrals over `H \ X` when the action has a cutoff
(`MeasureTheory.HasOrbitCutoff`). For a subgroup `Γ` of a group `G`, acting by left multiplication
with counting measure, `Subgroup.cutoffMeasure Γ μ` computes integrals over `Γ \ G`.

This is a measure-theoretic notion, distinct from the topological cutoff functions
`TauCeti.MulAction.IsCutoff`: real-valued nonnegative functions whose translates sum to one at every
point and whose support meets the translates of each compact set for only finitely many group
elements. For a countable group with counting measure an orbit cutoff is a measurable weight whose
values along every orbit sum to one (`MeasureTheory.isOrbitCutoff_count_iff`).

## Main definitions

* `MeasureTheory.IsOrbitCutoff ν β`: `β` is a measurable weight with integral one on every orbit.
* `MeasureTheory.HasOrbitCutoff ν X`: the action of `H` on `X` has an orbit cutoff for `ν`.
* `MeasureTheory.Measure.cutoffMeasure ν μ`: `μ` weighted by a chosen orbit cutoff.
* `Subgroup.cutoffMeasure Γ μ`: the measure computing integrals over `Γ \ G`.

## Main results

* `MeasureTheory.IsOrbitCutoff.measurePreserving_smul`: unfolding, `(β μ) × ν ↦ μ`.
* `MeasureTheory.IsOrbitCutoff.lintegral_lintegral_smul_mul`,
  `MeasureTheory.IsOrbitCutoff.integral_integral_smul`: unfolding for nonnegative and for integrable
  functions.
* `MeasureTheory.IsOrbitCutoff.identDistrib_withDensity_of_measurePreserving`: an invariant `F`
  under `β μ` has the distribution of `F ∘ T` under any measure `m` unfolding to `μ` along `T`.
* `MeasureTheory.identDistrib_cutoffMeasure_of_measurePreserving`: the same for the measure
  `ν.cutoffMeasure μ` weighted by the chosen cutoff.
* `MeasureTheory.IsOrbitCutoff.identDistrib_withDensity`: independence of the cutoff.
* `MeasureTheory.identDistrib_cutoffMeasure_comp`: change of variables along an equivariant measure
  preserving map.

## References

* O. Kallenberg, *Invariant measures and disintegrations with applications to Palm and related
  kernels*, Probab. Theory Related Fields 139 (2007), 285–310, as cited in D. Gentner and G. Last,
  *Palm pairs and the general mass-transport principle*, Math. Z. 267 (2011), §2.
* N. Bourbaki, *Intégration*, chapitre VII, Hermann, 1963.

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/Basic.lean` (`New.IsCutoff`,
`New.measurePreserving_smul_prod`, `New.IsCutoff.measurePreserving`,
`New.identDistrib_orbitMeasure_of_unfold`, `New.identDistrib_orbitMeasure`,
`New.identDistrib_orbitMeasure_comp`) and `src/Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean`
(`New.IsCutoff.integrable_orbitMeasure_iff`).
-/

public section

open MeasureTheory Measure ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

section Defs

variable [SMul H X]

/-- An **orbit cutoff** for the action of `H` on `X` and the measure `ν` on `H` is a measurable
weight `β : X → [0, ∞]` whose integral along every orbit is one: `∫ β (h • x) dν(h) = 1` for every
`x`. Integrating an `H`-invariant function against `β μ` computes its integral over `H \ X`. -/
structure IsOrbitCutoff (ν : Measure H) (β : X → ℝ≥0∞) : Prop where
  /-- An orbit cutoff is measurable. -/
  measurable : Measurable β
  /-- An orbit cutoff has integral one along every orbit. -/
  lintegral_smul (x : X) : ∫⁻ h, β (h • x) ∂ν = 1

/-- The action of `H` on `X` **has an orbit cutoff** for the measure `ν` on `H`. -/
class HasOrbitCutoff (ν : Measure H) (X : Type*) [MeasurableSpace X] [SMul H X] : Prop where
  /-- Some weight is an orbit cutoff. -/
  exists_isOrbitCutoff : ∃ β : X → ℝ≥0∞, IsOrbitCutoff ν β

variable (ν : Measure H)

/-- A weight on `X` that is an orbit cutoff for `ν` whenever the action has one
(`MeasureTheory.Measure.isOrbitCutoff_orbitCutoff`), chosen once and for all; otherwise it is an
unspecified function. -/
noncomputable def Measure.orbitCutoff : X → ℝ≥0∞ :=
  Classical.epsilon (IsOrbitCutoff ν)

/-- The measure `μ` weighted by the chosen orbit cutoff `ν.orbitCutoff`. When the action has a
cutoff, `ν` is inversion invariant and `μ` is `H`-invariant, both s-finite, integrating an
`H`-invariant function against it computes its integral over `H \ X`, and every cutoff gives the
same result (`MeasureTheory.IsOrbitCutoff.identDistrib_withDensity`). -/
noncomputable def Measure.cutoffMeasure (μ : Measure X) : Measure X :=
  μ.withDensity ν.orbitCutoff

/-- If the action has an orbit cutoff, the chosen weight `ν.orbitCutoff` is an orbit cutoff. -/
theorem Measure.isOrbitCutoff_orbitCutoff [h : HasOrbitCutoff ν X] :
    IsOrbitCutoff ν (ν.orbitCutoff : X → ℝ≥0∞) :=
  Classical.epsilon_spec h.exists_isOrbitCutoff

/-- An orbit cutoff gives the action an orbit cutoff. -/
theorem IsOrbitCutoff.hasOrbitCutoff {ν : Measure H} {β : X → ℝ≥0∞} (hβ : IsOrbitCutoff ν β) :
    HasOrbitCutoff ν X :=
  ⟨β, hβ⟩

/-- The measure `cutoffMeasure ν μ` is `μ` weighted by the chosen cutoff. -/
theorem Measure.cutoffMeasure_def (μ : Measure X) :
    ν.cutoffMeasure μ = μ.withDensity ν.orbitCutoff :=
  (rfl)

/-- The cutoff measure of the zero measure is zero. -/
@[simp]
theorem Measure.cutoffMeasure_zero : ν.cutoffMeasure (0 : Measure X) = 0 := by
  rw [cutoffMeasure_def, withDensity_zero_left]

/-- The cutoff measure is additive in the measure. -/
theorem Measure.cutoffMeasure_add (μ μ' : Measure X) :
    ν.cutoffMeasure (μ + μ') = ν.cutoffMeasure μ + ν.cutoffMeasure μ' := by
  rw [cutoffMeasure_def, cutoffMeasure_def, cutoffMeasure_def, withDensity_add_measure]

/-- The cutoff measure commutes with scaling the measure. -/
theorem Measure.cutoffMeasure_smul (c : ℝ≥0∞) (μ : Measure X) :
    ν.cutoffMeasure (c • μ) = c • ν.cutoffMeasure μ := by
  rw [cutoffMeasure_def, cutoffMeasure_def, withDensity_smul_measure]

end Defs

/-- For counting measure, an orbit cutoff is a measurable weight whose values along every orbit sum
to one. -/
theorem isOrbitCutoff_count_iff [SMul H X] [MeasurableSingletonClass H] {β : X → ℝ≥0∞} :
    IsOrbitCutoff (count : Measure H) β ↔ Measurable β ∧ ∀ x : X, ∑' h : H, β (h • x) = 1 := by
  simp only [← lintegral_count]
  exact ⟨fun h ↦ ⟨h.measurable, h.lintegral_smul⟩, fun ⟨hm, h⟩ ↦ ⟨hm, h⟩⟩

/-! ### Unfolding along a measure that unfolds to `μ` -/

section Unfold

variable [SMul H X] [MeasurableSMul₂ H X] {ν : Measure H} {μ : Measure X} {β : X → ℝ≥0∞}
  {Y : Type*} [MeasurableSpace Y] {F : X → Y}

/-- **The quotient integral does not depend on how `μ` is unfolded.** Let `β` be an orbit cutoff
for `ν`, let `σ` carry an s-finite measure `ρ` to `ν`, and let `(z, l) ↦ σ l • T z` carry `m × ρ`
to `μ`, with `T` measurable. Then a measurable `H`-invariant function `F` has the
same distribution under `β μ` as `F ∘ T` under `m`. -/
theorem IsOrbitCutoff.identDistrib_withDensity_of_measurePreserving (hβ : IsOrbitCutoff ν β)
    {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L] {ρ : Measure L} [SFinite ρ]
    {σ : L → H} (hσ : MeasurePreserving σ ρ ν) {T : Z → X} {m : Measure Z}
    (hT_unfold : MeasurePreserving (fun p : Z × L ↦ σ p.2 • T p.1) (m.prod ρ) μ)
    (hF : Measurable F) (hT : Measurable T) (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F (F ∘ T) (μ.withDensity β) m := by
  -- Test both laws against a measurable `f`; unfolding `μ` along `(z, l) ↦ σ l • T z`, the
  -- integral over `l` is that of `β` along an orbit, which is `1`.
  have hσm : Measurable σ := hσ.measurable
  have hβm : Measurable β := hβ.measurable
  refine ⟨hF.aemeasurable, (hF.comp hT).aemeasurable, ext_of_lintegral _ fun f hf ↦ ?_⟩
  have h_orbit (x : X) : ∫⁻ l, β (σ l • x) ∂ρ = 1 := by
    rw [← hβ.lintegral_smul x, ← hσ.lintegral_comp (by fun_prop)]
  calc ∫⁻ y, f y ∂(μ.withDensity β).map F
      = ∫⁻ x, β x * f (F x) ∂μ := by
        rw [lintegral_map hf hF]
        exact lintegral_withDensity_eq_lintegral_mul _ hβm (hf.comp hF)
    _ = ∫⁻ p, β (σ p.2 • T p.1) * f (F (T p.1)) ∂m.prod ρ := by
        rw [← hT_unfold.lintegral_comp (by fun_prop)]
        simp only [hF_inv]
    _ = ∫⁻ z, ∫⁻ l, β (σ l • T z) * f (F (T z)) ∂ρ ∂m := lintegral_prod _ (by fun_prop)
    _ = ∫⁻ z, f (F (T z)) ∂m := by
        refine lintegral_congr fun z ↦ ?_
        rw [lintegral_mul_const _ (by fun_prop), h_orbit, one_mul]
    _ = ∫⁻ y, f y ∂m.map (F ∘ T) := (lintegral_map hf (hF.comp hT)).symm

/-- **The quotient integral does not depend on how `μ` is unfolded**, for the chosen cutoff. Let `σ`
carry an s-finite measure `ρ` to `ν`, and let `(z, l) ↦ σ l • T z` carry `m × ρ` to `μ`, with `T`
measurable. Then a measurable `H`-invariant function `F` has the same distribution under
`ν.cutoffMeasure μ` as `F ∘ T` under `m`. -/
theorem identDistrib_cutoffMeasure_of_measurePreserving [HasOrbitCutoff ν X] {Z L : Type*}
    [MeasurableSpace Z] [MeasurableSpace L] {ρ : Measure L} [SFinite ρ] {σ : L → H}
    (hσ : MeasurePreserving σ ρ ν) {T : Z → X} {m : Measure Z}
    (hT_unfold : MeasurePreserving (fun p : Z × L ↦ σ p.2 • T p.1) (m.prod ρ) μ)
    (hF : Measurable F) (hT : Measurable T) (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F (F ∘ T) (ν.cutoffMeasure μ) m := by
  rw [cutoffMeasure_def]
  exact (isOrbitCutoff_orbitCutoff ν).identDistrib_withDensity_of_measurePreserving hσ hT_unfold hF
    hT hF_inv

end Unfold

/-! ### Unfolding with a cutoff -/

section Group

variable [Group H] [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X]
  {ν : Measure H} [SFinite ν] {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ]
  {β : X → ℝ≥0∞}

/-- For any measurable weight `β`, the map `(x, h) ↦ h • x` carries `(β μ) × ν` to `μ` weighted by
the integral of `β` along orbits, `x ↦ ∫ β (h • x) dν⁻¹(h)`. -/
theorem measurePreserving_smul_prod_withDensity (hβ : Measurable β) :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((μ.withDensity β).prod ν)
      (μ.withDensity fun x ↦ ∫⁻ h, β (h • x) ∂ν.inv) := by
  have h_smul : Measurable fun p : X × H ↦ p.2 • p.1 := by fun_prop
  refine ⟨h_smul, ext fun s hs ↦ ?_⟩
  -- For fixed `h` substitute `x ↦ h • x`, which preserves `μ`; then swap the integrals.
  have h_slice (h : H) : μ.withDensity β ((h • ·) ⁻¹' s) = ∫⁻ x in s, β (h⁻¹ • x) ∂μ := by
    rw [← (measurePreserving_smul h μ).setLIntegral_comp_preimage hs (by fun_prop),
      withDensity_apply _ (measurable_const_smul h hs)]
    simp
  rw [map_apply h_smul hs, prod_apply_symm (h_smul hs), withDensity_apply _ hs]
  calc _ = ∫⁻ h, ∫⁻ x in s, β (h⁻¹ • x) ∂μ ∂ν := lintegral_congr h_slice
    _ = ∫⁻ x in s, ∫⁻ h, β (h⁻¹ • x) ∂ν ∂μ := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x in s, ∫⁻ h, β (h • x) ∂ν.inv ∂μ := by
        refine setLIntegral_congr_fun hs fun x _ ↦ ?_
        rw [Measure.inv, lintegral_map (f := fun h ↦ β (h • x)) (hβ.comp (measurable_smul_const x))
          measurable_inv]

variable [ν.IsInvInvariant]

/-- **Unfolding.** For an orbit cutoff `β`, an inversion-invariant measure `ν` and an
`H`-invariant measure `μ`, both s-finite, the map `(x, h) ↦ h • x` carries `(β μ) × ν` to `μ`. -/
theorem IsOrbitCutoff.measurePreserving_smul (hβ : IsOrbitCutoff ν β) :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((μ.withDensity β).prod ν) μ := by
  simpa [Measure.inv_eq_self, hβ.lintegral_smul] using
    measurePreserving_smul_prod_withDensity (ν := ν) (μ := μ) hβ.measurable

/-- **Unfolding for nonnegative functions**: for an orbit cutoff `β`,
`∫_X (∫_H f (h • x) dν(h)) β(x) dμ(x) = ∫_X f dμ` for every measurable `f ≥ 0`. -/
theorem IsOrbitCutoff.lintegral_lintegral_smul_mul (hβ : IsOrbitCutoff ν β) {f : X → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (∫⁻ h, f (h • x) ∂ν) * β x ∂μ = ∫⁻ x, f x ∂μ := by
  rw [← hβ.measurePreserving_smul.lintegral_comp hf, lintegral_prod _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hβ.measurable (by fun_prop)]
  simp only [Pi.mul_apply, mul_comm]

/-- **Unfolding for integrable functions**: for an orbit cutoff `β` and a `μ`-integrable `f` with
values in a real Banach space, `x ↦ ∫_H f (h • x) dν(h)` is integrable for `β μ`, and
`∫_X (∫_H f (h • x) dν(h)) β(x) dμ(x) = ∫_X f dμ`. -/
theorem IsOrbitCutoff.integral_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hβ : IsOrbitCutoff ν β) {f : X → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ ∫ h, f (h • x) ∂ν) (μ.withDensity β) ∧
      ∫ x, ∫ h, f (h • x) ∂ν ∂μ.withDensity β = ∫ x, f x ∂μ := by
  have h_int : Integrable (fun p : X × H ↦ f (p.2 • p.1)) ((μ.withDensity β).prod ν) :=
    hβ.measurePreserving_smul.integrable_comp_of_integrable hf
  refine ⟨h_int.integral_prod_left, ?_⟩
  rw [← integral_prod _ h_int]
  exact hβ.measurePreserving_smul.hasLaw.integral_comp hf.aestronglyMeasurable

/-- **Independence of the cutoff.** For two orbit cutoffs `β` and `β'`, a measurable
`H`-invariant function has the same distribution under `β μ` and under `β' μ`. -/
theorem IsOrbitCutoff.identDistrib_withDensity {Y : Type*} [MeasurableSpace Y] {F : X → Y}
    {β' : X → ℝ≥0∞} (hβ : IsOrbitCutoff ν β) (hβ' : IsOrbitCutoff ν β') (hF : Measurable F)
    (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F F (μ.withDensity β) (μ.withDensity β') :=
  hβ.identDistrib_withDensity_of_measurePreserving (.id ν) hβ'.measurePreserving_smul hF
    measurable_id hF_inv

/-- An orbit cutoff is finite almost everywhere. -/
theorem IsOrbitCutoff.ae_lt_top (hβ : IsOrbitCutoff ν β) : ∀ᵐ x ∂μ, β x < ∞ := by
  -- Along each orbit `β` has finite integral, so it is finite almost everywhere there; unfold.
  have h_orbit (x : X) : ∀ᵐ h ∂ν, β (h • x) < ∞ :=
    MeasureTheory.ae_lt_top (hβ.measurable.comp (measurable_smul_const x))
      (by simp [hβ.lintegral_smul])
  have h_set : MeasurableSet {x | β x < ∞} := measurableSet_lt hβ.measurable measurable_const
  have h_prod : ∀ᵐ p ∂(μ.withDensity β).prod ν, β (p.2 • p.1) < ∞ :=
    (ae_prod_iff_ae_ae (h_set.preimage (by fun_prop))).2 (.of_forall h_orbit)
  rw [← (hβ.measurePreserving_smul (μ := μ)).map_eq]
  exact (ae_map_iff (by fun_prop) h_set).2 h_prod

end Group

/-! ### The measure weighted by the chosen cutoff -/

section CutoffMeasure

variable [Group H] [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X]
  {ν : Measure H} [SFinite ν] [ν.IsInvInvariant] {μ : Measure X} [SFinite μ]
  [SMulInvariantMeasure H X μ] {β : X → ℝ≥0∞} {Y : Type*} [MeasurableSpace Y] {F : X → Y}

instance (ν : Measure H) (μ : Measure X) [SFinite μ] : SFinite (ν.cutoffMeasure μ) := by
  rw [cutoffMeasure_def]; infer_instance

/-- **Unfolding** for the chosen cutoff: `(x, h) ↦ h • x` carries `ν.cutoffMeasure μ × ν` to
`μ`. -/
theorem measurePreserving_cutoffMeasure [HasOrbitCutoff ν X] :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((ν.cutoffMeasure μ).prod ν) μ :=
  (isOrbitCutoff_orbitCutoff ν).measurePreserving_smul

/-- **Unfolding for nonnegative functions** over the orbit space:
`∫_{H\X} ∫_H f (h • x) dν(h) = ∫_X f dμ`. -/
theorem lintegral_cutoffMeasure_lintegral [HasOrbitCutoff ν X] {f : X → ℝ≥0∞}
    (hf : Measurable f) : ∫⁻ x, ∫⁻ h, f (h • x) ∂ν ∂ν.cutoffMeasure μ = ∫⁻ x, f x ∂μ := by
  rw [← (measurePreserving_cutoffMeasure (ν := ν) (μ := μ)).lintegral_comp hf]
  exact lintegral_lintegral (by fun_prop)

/-- **Unfolding for integrable functions** over the orbit space: for `f` integrable on `X`,
`x ↦ ∫_H f (h • x) dν(h)` is integrable on `H \ X` and its integral there is `∫_X f dμ`. -/
theorem integral_cutoffMeasure_integral [HasOrbitCutoff ν X] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ ∫ h, f (h • x) ∂ν) (ν.cutoffMeasure μ) ∧
      ∫ x, ∫ h, f (h • x) ∂ν ∂ν.cutoffMeasure μ = ∫ x, f x ∂μ :=
  (isOrbitCutoff_orbitCutoff ν).integral_integral_smul hf

/-- For any orbit cutoff `β`, a measurable `H`-invariant function has the same distribution under
`ν.cutoffMeasure μ` as under `β μ`. -/
theorem IsOrbitCutoff.identDistrib_cutoffMeasure (hβ : IsOrbitCutoff ν β) (hF : Measurable F)
    (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F F (ν.cutoffMeasure μ) (μ.withDensity β) :=
  haveI : HasOrbitCutoff ν X := hβ.hasOrbitCutoff
  (isOrbitCutoff_orbitCutoff ν).identDistrib_withDensity hβ hF hF_inv

/-- For any orbit cutoff `β`, the lower integral of a measurable `H`-invariant function over `H \ X`
is `∫_X F β dμ`. -/
theorem IsOrbitCutoff.lintegral_cutoffMeasure (hβ : IsOrbitCutoff ν β) {F : X → ℝ≥0∞}
    (hF : Measurable F) (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    ∫⁻ x, F x ∂ν.cutoffMeasure μ = ∫⁻ x, β x * F x ∂μ := by
  rw [(hβ.identDistrib_cutoffMeasure hF hF_inv).lintegral_eq,
    lintegral_withDensity_eq_lintegral_mul _ hβ.measurable hF]
  simp only [Pi.mul_apply]

/-- For any orbit cutoff `β`, the integral of a measurable `H`-invariant function over `H \ X` is
`∫_X β F dμ`. -/
theorem IsOrbitCutoff.integral_cutoffMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (hβ : IsOrbitCutoff ν β) {F : X → E} (hF : Measurable F)
    (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    ∫ x, F x ∂ν.cutoffMeasure μ = ∫ x, (β x).toReal • F x ∂μ := by
  rw [(hβ.identDistrib_cutoffMeasure hF hF_inv).integral_eq,
    integral_withDensity_eq_integral_toReal_smul hβ.measurable hβ.ae_lt_top]

/-- For any orbit cutoff `β`, a measurable `H`-invariant function is integrable over `H \ X` if and
only if `β F` is `μ`-integrable. -/
theorem IsOrbitCutoff.integrable_cutoffMeasure_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] (hβ : IsOrbitCutoff ν β) {F : X → E}
    (hF : Measurable F)
    (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    Integrable F (ν.cutoffMeasure μ) ↔ Integrable (fun x ↦ (β x).toReal • F x) μ := by
  rw [(hβ.identDistrib_cutoffMeasure hF hF_inv).integrable_iff,
    integrable_withDensity_iff_integrable_smul' hβ.measurable hβ.ae_lt_top]

/-- **Change of variables on orbit spaces.** Let `σ : H → H'` and `T : X → Y` preserve the measures,
with `T (h • x) = σ h • T x`, and let both actions have orbit cutoffs. For a measurable
`H'`-invariant `F` on `Y`, the function `F ∘ T` on `H \ X` and the function `F` on `H' \ Y` have the
same distribution. -/
theorem identDistrib_cutoffMeasure_comp [HasOrbitCutoff ν X] {H' Z : Type*} [MeasurableSpace H']
    [MeasurableSpace Z] [SMul H' Y] [MeasurableSMul₂ H' Y] {ν' : Measure H'} {μ' : Measure Y}
    [HasOrbitCutoff ν' Y] {σ : H → H'} (hσ : MeasurePreserving σ ν ν') {T : X → Y}
    (hT : MeasurePreserving T μ μ') (hT_equiv : ∀ (h : H) (x : X), T (h • x) = σ h • T x)
    {F : Y → Z} (hF : Measurable F) (hF_inv : ∀ (h : H') (y : Y), F (h • y) = F y) :
    IdentDistrib (F ∘ T) F (ν.cutoffMeasure μ) (ν'.cutoffMeasure μ') := by
  -- `ν.cutoffMeasure μ` unfolds to `μ`, and `T` is equivariant, so along `σ` it unfolds to `μ'`.
  have h_unfold : MeasurePreserving (fun p : X × H ↦ σ p.2 • T p.1)
      ((ν.cutoffMeasure μ).prod ν) μ' := by
    simpa only [Function.comp_def, hT_equiv] using
      hT.comp (measurePreserving_cutoffMeasure (ν := ν) (μ := μ))
  exact ((isOrbitCutoff_orbitCutoff ν').identDistrib_withDensity_of_measurePreserving hσ h_unfold
    hF hT.measurable hF_inv).symm

/-- If `μ` is right invariant on the group `X`, and the action of `H` commutes with right
multiplication, then right translation by `g` does not change the distribution on `H \ X` of a
measurable `H`-invariant function. -/
theorem identDistrib_cutoffMeasure_mul_right [HasOrbitCutoff ν X] [Group X] [MeasurableMul X]
    [IsScalarTower H X X] [μ.IsMulRightInvariant] (g : X) (hF : Measurable F)
    (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib (fun x ↦ F (x * g)) F (ν.cutoffMeasure μ) (ν.cutoffMeasure μ) :=
  identDistrib_cutoffMeasure_comp (.id ν) (measurePreserving_mul_right μ g)
    (fun h x ↦ smul_mul_assoc h x g) hF hF_inv

end CutoffMeasure

end MeasureTheory

/-- For a subgroup `Γ` of a group `G` acting on `G` by left multiplication, with counting measure,
`Γ.cutoffMeasure μ` is `μ` weighted by a chosen orbit cutoff. When `Γ` is discrete in a second
countable locally compact group and `μ` is a left Haar measure, it computes integrals over `Γ \ G`
(`Subgroup.integral_cutoffMeasure_tsum`), and its total mass is the covolume `vol(Γ \ G)`. -/
noncomputable abbrev Subgroup.cutoffMeasure {G : Type*} [Group G] [MeasurableSpace G]
    (Γ : Subgroup G) (μ : Measure G) : Measure G :=
  (count : Measure Γ).cutoffMeasure μ
