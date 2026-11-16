/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection

/-!
# Lowering the integrability exponent of Sobolev sections

Let `C` be chart data for the sections of a vector bundle with model fibre `F`, read on open
subsets of a finite-dimensional real inner product space `E` with Haar measure `μ`, and suppose that
every chart image `C.image i` has finite measure. The scalar inclusions `TauCeti.Wkp.ofExponentLEL`
then apply to every component of an element of the Sobolev sections of exponent `q`. Applied
componentwise they give the continuous linear inclusion `W^{k,q} → W^{k,p}` of Sobolev sections for
`1 ≤ p ≤ q ≤ ∞`. Its chart data are the `Lᵖ` copies of the original chart data, so it keeps the
underlying section, is injective, commutes with forgetting the highest derivative, and sends the
Sobolev section of exponent `q` with given components to the one of exponent `p`.

For a finite bundle atlas `A`, every chart image has compact closure, so it has finite measure
(`TauCeti.FiniteBundleAtlas.isFiniteMeasure_restrict_image`), and the inclusion applies to
`W^{k,q}(V) = TauCeti.SobolevSection A μ q k`. Over a base with boundary, the instances
`TauCeti.FiniteBundleAtlas.isFiniteMeasure_restrict_halfSectionChartData_image` let it apply to
`TauCeti.BorderedSobolevSection A q k` as well.

## Main definitions

* `TauCeti.SectionChartData.ofExponentLEL`: the continuous inclusion `W^{k,q} → W^{k,p}` of Sobolev
  sections.

## Main results

* `TauCeti.SectionChartData.chartValueL_ofExponentLEL`: the chart data are their `Lᵖ` copies.
* `TauCeti.SectionChartData.ofExponentLEL_injective`: the inclusion is injective.
* `TauCeti.SectionChartData.ofExponentLEL_self`,
  `TauCeti.SectionChartData.ofExponentLEL_ofExponentLEL`: the identity at `p = q` and
  transitivity.
* `TauCeti.SectionChartData.lowerOrderL_ofExponentLEL`: compatibility with `lowerOrderL`.
* `TauCeti.SectionChartData.ofExponentLEL_ofComponents`,
  `TauCeti.SobolevSection.ofExponentLEL_ofContMDiffSection`: compatibility with the Sobolev sections
  with given components, in particular those of `Cᵏ` sections.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]
  (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure]
  [∀ i, IsFiniteMeasure (μ.restrict (C.image i : Set E))]
  {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] (k : ℕ)

variable {C μ k} in
/-- Lowering the exponent of every component of a tuple of Sobolev functions replaces its chart data
by their `Lᵖ` copies. -/
theorem chartValueL_mapL_ofExponentLEL (hpq : p ≤ q) (w : C.SobolevData μ q k) (i : Fin C.n) :
    C.chartValueL μ p k i (SobolevData.mapL (fun _ ↦ Wkp.ofExponentLEL hpq k) w) =
      Lp.ofExponentLEL ℝ F hpq (C.chartValueL μ q k i w) :=
  Lp.ext <| by
    rw [Lp.coeFn_ofExponentLEL]
    filter_upwards [C.chartValueL_apply_ae μ p k i
        (SobolevData.mapL (fun _ ↦ Wkp.ofExponentLEL hpq k) w),
      C.chartValueL_apply_ae μ q k i w,
      ae_all_iff.2 fun j ↦ Wkp.value_ofExponentLEL_ae hpq k (w i j)] with y hp hq hj
    rw [hp, hq]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [SobolevData.mapL_apply, hj j]

/-- **Lowering the exponent.** For `p ≤ q`, the continuous inclusion of the Sobolev sections of
exponent `q` into those of exponent `p`, applying `TauCeti.Wkp.ofExponentLEL` to every chartwise
component. -/
def ofExponentLEL (hpq : p ≤ q) : C.sobolevSections μ q k →L[ℝ] C.sobolevSections μ p k :=
  ((SobolevData.mapL fun _ ↦ Wkp.ofExponentLEL hpq k).comp
    (C.sobolevSections μ q k).subtypeL).codRestrict (C.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := C.exists_section μ q k w
      refine (C.mem_sobolevSections_iff μ p k).2 ⟨s, fun i ↦ ?_⟩
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        chartValueL_mapL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
      exact hs i

variable {C μ k}

/-- The underlying tuple of `C.ofExponentLEL μ k hpq w` applies `TauCeti.Wkp.ofExponentLEL` to
every component of `w`. -/
theorem coe_ofExponentLEL (hpq : p ≤ q) (w : C.sobolevSections μ q k) :
    (C.ofExponentLEL μ k hpq w : C.SobolevData μ p k) =
      SobolevData.mapL (fun _ ↦ Wkp.ofExponentLEL hpq k) (w : C.SobolevData μ q k) :=
  (rfl)

/-- The components of `C.ofExponentLEL μ k hpq w` are the components of `w` with lowered
exponent. -/
@[simp]
theorem ofExponentLEL_apply (hpq : p ≤ q) (w : C.sobolevSections μ q k) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    (C.ofExponentLEL μ k hpq w : C.SobolevData μ p k) i j =
      Wkp.ofExponentLEL hpq k ((w : C.SobolevData μ q k) i j) := by
  rw [coe_ofExponentLEL, SobolevData.mapL_apply]

/-- The chart data of `C.ofExponentLEL μ k hpq w` are the `Lᵖ` copies of those of `w`. -/
@[simp]
theorem chartValueL_ofExponentLEL (hpq : p ≤ q) (w : C.sobolevSections μ q k) (i : Fin C.n) :
    C.chartValueL μ p k i (C.ofExponentLEL μ k hpq w) =
      Lp.ofExponentLEL ℝ F hpq (C.chartValueL μ q k i w) := by
  rw [coe_ofExponentLEL, chartValueL_mapL_ofExponentLEL]

/-- Lowering the exponent is injective. -/
theorem ofExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (C.ofExponentLEL μ k hpq) := fun w w' h ↦
  Subtype.ext <| funext fun i ↦ funext fun j ↦
    Wkp.ofExponentLEL_injective hpq k <| by
      rw [← ofExponentLEL_apply, ← ofExponentLEL_apply, h]

/-- Lowering the exponent from `p` to itself is the identity. -/
@[simp]
theorem ofExponentLEL_self (w : C.sobolevSections μ p k) : C.ofExponentLEL μ k le_rfl w = w :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ by rw [ofExponentLEL_apply, Wkp.ofExponentLEL_self]

/-- Exponent inclusions compose transitively. -/
@[simp]
theorem ofExponentLEL_ofExponentLEL (hpq : p ≤ q) (hqr : q ≤ r) (w : C.sobolevSections μ r k) :
    C.ofExponentLEL μ k hpq (C.ofExponentLEL μ k hqr w) = C.ofExponentLEL μ k (hpq.trans hqr) w :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ by
    rw [ofExponentLEL_apply, ofExponentLEL_apply, ofExponentLEL_apply,
      Wkp.ofExponentLEL_ofExponentLEL]

/-- Lowering the exponent commutes with forgetting the highest derivative. -/
theorem lowerOrderL_ofExponentLEL (hpq : p ≤ q) (w : C.sobolevSections μ q (k + 1)) :
    C.lowerOrderL μ p k (C.ofExponentLEL μ (k + 1) hpq w) =
      C.ofExponentLEL μ k hpq (C.lowerOrderL μ q k w) :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ by
    rw [lowerOrderL_apply, ofExponentLEL_apply, ofExponentLEL_apply, lowerOrderL_apply,
      Wkp.lowerOrder_ofExponentLEL]

variable {T : Type*} [AddCommGroup T] [Module ℝ T] (ι : T →ₗ[ℝ] S)

/-- Lowering the exponent sends the Sobolev section of exponent `q` with the components of the
readings of `ι t` to the Sobolev section of exponent `p` with these components. -/
theorem ofExponentLEL_ofComponents
    (hq : ∀ t i j, ∃ w : Wkp μ (C.image i) q k, (Wkp.value k w : E → ℝ)
      =ᵐ[μ.restrict (C.image i)] fun y ↦ (finBasis ℝ F).coord j (C.coord i (ι t) y))
    (hp : ∀ t i j, ∃ w : Wkp μ (C.image i) p k, (Wkp.value k w : E → ℝ)
      =ᵐ[μ.restrict (C.image i)] fun y ↦ (finBasis ℝ F).coord j (C.coord i (ι t) y))
    (hpq : p ≤ q) (t : T) :
    C.ofExponentLEL μ k hpq (C.ofComponents μ q k ι hq t) = C.ofComponents μ p k ι hp t :=
  eq_of_ae_eq_coord
    (fun i ↦ by
      rw [chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
      exact C.chartValueL_ofComponents_ae μ q k ι hq t i)
    (C.chartValueL_ofComponents_ae μ p k ι hp t)

end SectionChartData

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {k : ℕ}
  [IsManifold 𝓘(ℝ, E) k M] [ContMDiffVectorBundle k F V 𝓘(ℝ, E)]

/-- Lowering the exponent sends the Sobolev section of exponent `q` of a `Cᵏ` section to its
Sobolev section of exponent `p`. -/
@[simp]
theorem ofExponentLEL_ofContMDiffSection (hpq : p ≤ q) (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    A.sectionChartData.ofExponentLEL μ k hpq (ofContMDiffSection A μ q k s) =
      ofContMDiffSection A μ p k s :=
  eq_of_ae_eq_coord (s := s)
    (fun i ↦ by
      rw [SectionChartData.chartValueL_ofExponentLEL, Lp.coeFn_ofExponentLEL]
      exact chartValueL_ofContMDiffSection_ae A μ q k s i)
    (fun i ↦ chartValueL_ofContMDiffSection_ae A μ p k s i)

end SobolevSection

end TauCeti
