/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import TauCeti.Analysis.Convex.SubgradientImage
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Aleksandrov Monge–Ampère measure of a convex function

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with `D` the interior of its
effective domain `{x | f x ≠ ⊤}`. The *subgradient image* of a set `s` is
`∂f(s) = ⋃ x ∈ s, ∂f(x)` (`TauCeti.subgradientImage`), the union of the subdifferentials of `f`
for the inner product. The *Aleksandrov Monge–Ampère measure* of `f` is

  `MA_f(s) = μ(∂f(s ∩ D))`

for Borel `s`. It gives the weak (Aleksandrov) sense in which a merely convex function solves
the Monge–Ampère equation `det D²f = ν`. Classically, for a convex function of class `C²` it is
the measure `det (D²f) dx`; that identification is not part of this file. The same formula
defines a measure for every `μ` absolutely continuous with respect to a Haar measure, such as the
weighted measure `s ↦ ∫_{∂f(s ∩ D)} g` for `μ = volume.withDensity g`.

That `s ↦ μ(∂f(s ∩ D))` is a measure rests on two facts.

* A point `y` that is a subgradient at two distinct points `x₁ ≠ x₂` is a point where the
  conjugate `f⋆` has the two subgradients `x₁` and `x₂`, so `f⋆` is not differentiable there.
  By Rademacher's theorem for the convex function `f⋆`, such points form a `μ`-null set
  (`TauCeti.measure_setOf_mem_subdifferential_of_ne_eq_zero`); this needs no convexity of `f`.
  Hence the subgradient images of disjoint sets are almost disjoint.
* The subgradient image of a compact subset of `D` is compact
  (`TauCeti.isCompact_subgradientImage`). Open subsets of `D` are σ-compact, so their
  subgradient images are measurable; complements are handled by the almost-disjointness, so the
  subgradient image of every Borel subset of `D` is null measurable
  (`TauCeti.nullMeasurableSet_subgradientImage`).

A finite convex function `u` on an open convex set `Ω` is covered by extending it by `⊤` off `Ω`;
then `D = Ω` and the subdifferential is the set of `y` with `u x + ⟪x' - x, y⟫ ≤ u x'` for all
`x' ∈ Ω` (`TauCeti.mongeAmpereMeasure_ite_apply`).

## Main definitions

* `TauCeti.mongeAmpereMeasure μ f` — the Aleksandrov Monge–Ampère measure of `f`; it is `0` when
  `f` is not convex or `μ` is not absolutely continuous with respect to a Haar measure.

## Main statements

* `TauCeti.mongeAmpereMeasure_apply` — `MA_f(s) = μ(∂f(s ∩ D))` for measurable `s`;
* `TauCeti.mongeAmpereMeasure_compl_interior` — `MA_f` is concentrated on `D`;
* `TauCeti.mongeAmpereMeasure_lt_top` and `TauCeti.isLocallyFiniteMeasure_comap_mongeAmpereMeasure`
  — when `μ` is finite on compact sets, `MA_f` is finite on compact subsets of `D`, so it is a
  locally finite measure on `D`;
* `TauCeti.mongeAmpereMeasure_ite_apply` — the formula for a finite convex function on an open
  set.

## References

* A. D. Aleksandrov, *Dirichlet's problem for the equation Det ‖z_{ij}‖ = φ(z₁, …, zₙ, z, x₁, …,
  xₙ). I*, Vestnik Leningrad. Univ. Ser. Mat. Meh. Astr. 13 (1958), 5–24.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1, in particular Theorem 1.1.13.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §2.1, in particular Theorem 2.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

section Overlap

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **Almost no point is a subgradient at two distinct points.** For any `f : E → EReal` on a
finite-dimensional real inner product space, the set of `y` lying in the subdifferentials of `f`
at two distinct points is null for every additive Haar measure. -/
theorem measure_setOf_mem_subdifferential_of_ne_eq_zero (f : E → EReal) :
    μ {y | ∃ x₁ x₂, x₁ ≠ x₂ ∧ y ∈ subdifferential (innerₗ E) f x₁ ∧
      y ∈ subdifferential (innerₗ E) f x₂} = 0 := by
  by_cases hdom : ∃ x, f x ≠ ⊤
  · obtain ⟨x₀, hx₀⟩ := hdom
    refine measure_mono_null ?_ (ae_iff.1 (ae_eventually_ne_top_and_differentiableAt_toReal
      (μ := μ) (convex_epigraph_fenchelConjugate (innerₗ E) f)
      (fenchelConjugate_ne_bot (innerₗ E) hx₀)))
    rintro y ⟨x₁, x₂, hne, h₁, h₂⟩ hy
    have h₁' := mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E) h₁
    have h₂' := mem_subdifferential_fenchelConjugate_of_mem_subdifferential (innerₗ E) h₂
    rw [flip_innerₗ] at h₁' h₂'
    obtain ⟨hev, hd⟩ := hy (ne_top_of_mem_subdifferential _ h₁')
    exact hne ((hasGradientAt_toReal_of_mem_subdifferential h₁' hev hd).unique
      (hasGradientAt_toReal_of_mem_subdifferential h₂' hev hd))
  · simp only [not_exists, not_not] at hdom
    refine measure_mono_null ?_ measure_empty
    rintro y ⟨x₁, -, -, h₁, -⟩
    exact ne_top_of_mem_subdifferential _ h₁ (hdom x₁)

/-- The subgradient images of disjoint sets are almost disjoint. -/
private lemma aedisjoint_subgradientImage {s t : Set E} (hst : Disjoint s t) :
    AEDisjoint μ (subgradientImage (innerₗ E) f s) (subgradientImage (innerₗ E) f t) := by
  refine measure_mono_null ?_ (measure_setOf_mem_subdifferential_of_ne_eq_zero μ f)
  rintro y ⟨h₁, h₂⟩
  obtain ⟨x₁, hx₁, h₁⟩ := (mem_subgradientImage_iff _).1 h₁
  obtain ⟨x₂, hx₂, h₂⟩ := (mem_subgradientImage_iff _).1 h₂
  exact ⟨x₁, x₂, hst.ne_of_mem hx₁ hx₂, h₁, h₂⟩

end Overlap

section Convex

variable (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
include hf hbot

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **Subgradient images of Borel subsets of the domain are null measurable.** For a convex
`f : E → EReal` on a finite-dimensional real inner product space, the subgradient image of the
part of a measurable set inside the interior of the effective domain is null measurable for every
additive Haar measure. -/
theorem nullMeasurableSet_subgradientImage {s : Set E} (hs : MeasurableSet s) :
    NullMeasurableSet (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤})) μ := by
  set D := interior {x | f x ≠ ⊤}
  -- On open sets: an open subset of `D` is a countable union of compact sets.
  have hopen : ∀ U, IsOpen U → NullMeasurableSet (subgradientImage (innerₗ E) f (U ∩ D)) μ := by
    intro U hU
    have : LocallyCompactSpace (U ∩ D : Set E) := (hU.inter isOpen_interior).locallyCompactSpace
    obtain ⟨K, hK, hKU⟩ := isSigmaCompact_iff_sigmaCompactSpace.2 (inferInstance :
      SigmaCompactSpace (U ∩ D : Set E))
    rw [← hKU, subgradientImage_iUnion]
    refine NullMeasurableSet.iUnion fun n => ?_
    refine (isCompact_subgradientImage hf hbot (hK n) fun x hx => ?_).isClosed
      |>.measurableSet.nullMeasurableSet
    exact (hKU ▸ mem_iUnion_of_mem n hx : x ∈ U ∩ D).2
  refine MeasurableSet.induction_on_open
    (C := fun t _ => NullMeasurableSet (subgradientImage (innerₗ E) f (t ∩ D)) μ) hopen ?_ ?_ s hs
  · -- On complements: the subgradient images of `t` and `tᶜ` are almost disjoint and cover the
    -- subgradient image of `D`.
    intro t _ ht
    refine ((hopen univ isOpen_univ).diff ht).congr (ae_eq_set.2 ⟨?_, ?_⟩)
    · refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := μ))
      obtain ⟨⟨hyD, hyt⟩, hytc⟩ := hy
      obtain ⟨x, ⟨-, hx⟩, hyx⟩ := (mem_subgradientImage_iff _).1 hyD
      by_cases hxt : x ∈ t
      · exact hyt ((mem_subgradientImage_iff _).2 ⟨x, ⟨hxt, hx⟩, hyx⟩)
      · exact hytc ((mem_subgradientImage_iff _).2 ⟨x, ⟨hxt, hx⟩, hyx⟩)
    · refine measure_mono_null (fun y hy => ?_) (aedisjoint_subgradientImage μ (f := f)
        (disjoint_compl_left.mono inter_subset_left inter_subset_left :
          Disjoint (tᶜ ∩ D) (t ∩ D)))
      obtain ⟨hytc, hy'⟩ := hy
      obtain ⟨x, hx, hyx⟩ := (mem_subgradientImage_iff _).1 hytc
      refine ⟨hytc, ?_⟩
      by_contra hyt
      exact hy' ⟨(mem_subgradientImage_iff _).2 ⟨x, ⟨mem_univ x, hx.2⟩, hyx⟩, hyt⟩
  · -- On countable unions: the subgradient image commutes with unions.
    intro g _ _ hg
    simpa only [iUnion_inter, subgradientImage_iUnion] using NullMeasurableSet.iUnion hg

end Convex

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- The **Aleksandrov Monge–Ampère measure** of `f : E → EReal` with respect to a measure `μ`
that is absolutely continuous with respect to an additive Haar measure. When `f` is convex
(convex real epigraph, never `⊥`), it is the measure with `MA_f(s) = μ(∂f(s ∩ D))` for
measurable `s`, where `D` is the interior of the effective domain and `∂f` the subgradient image
for the inner product (`mongeAmpereMeasure_apply`). For an additive Haar `μ` this is the
Aleksandrov measure; for `μ = ν.withDensity g` it is the weighted measure `∫_{∂f(s ∩ D)} g dν`.
If `f` is not convex, or `μ` is not absolutely continuous with respect to a Haar measure, it is
`0`. -/
def mongeAmpereMeasure (μ : Measure E) (f : E → EReal) : Measure E :=
  if h : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ (∀ x, f x ≠ ⊥) ∧
      ∃ ν : Measure E, ν.IsAddHaarMeasure ∧ μ ≪ ν then
    Measure.ofMeasurable
      (fun s _ => μ (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤})))
      (by simp) fun g hg hd => by
        obtain ⟨hf, hbot, ν, _, hμ⟩ := h
        simp only [iUnion_inter, subgradientImage_iUnion]
        exact measure_iUnion₀
          (fun i j hij => hμ (aedisjoint_subgradientImage ν
            ((hd hij).mono inter_subset_left inter_subset_left)))
          fun i => (nullMeasurableSet_subgradientImage hf hbot ν (hg i)).mono_ac hμ
  else 0

variable (μ : Measure E) {ν : Measure E} [ν.IsAddHaarMeasure]

/-- The Aleksandrov Monge–Ampère measure of a convex function evaluated on a measurable set `s` is
the measure of the subgradient image of the part of `s` in the interior of the effective domain. -/
theorem mongeAmpereMeasure_apply (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) (hμ : μ ≪ ν) {s : Set E} (hs : MeasurableSet s) :
    mongeAmpereMeasure μ f s =
      μ (subgradientImage (innerₗ E) f (s ∩ interior {x | f x ≠ ⊤})) := by
  rw [mongeAmpereMeasure, dite_eq_left ⟨hf, hbot, ν, inferInstance, hμ⟩, ofMeasurable_apply _ hs]

/-- The Aleksandrov Monge–Ampère measure of a function whose real epigraph is not convex is
`0`. -/
theorem mongeAmpereMeasure_eq_zero_of_not_convex (hf : ¬Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) :
    mongeAmpereMeasure μ f = 0 := by
  rw [mongeAmpereMeasure, dite_eq_right fun h => hf h.1]

/-- The Aleksandrov Monge–Ampère measure of a function taking the value `⊥` is `0`. -/
theorem mongeAmpereMeasure_eq_zero_of_eq_bot {x : E} (hx : f x = ⊥) :
    mongeAmpereMeasure μ f = 0 := by
  rw [mongeAmpereMeasure, dite_eq_right fun h => h.2.1 x hx]

/-- The Aleksandrov Monge–Ampère measure with respect to a measure that is not absolutely
continuous with respect to an additive Haar measure is `0`. -/
theorem mongeAmpereMeasure_eq_zero_of_not_absolutelyContinuous (hμ : ¬μ ≪ ν) :
    mongeAmpereMeasure μ f = 0 := by
  rw [mongeAmpereMeasure, dite_eq_right]
  rintro ⟨-, -, ν', _, hμ'⟩
  exact hμ (hμ'.trans (absolutelyContinuous_isAddHaarMeasure ν' ν))

/-- The Aleksandrov Monge–Ampère measure is concentrated on the interior of the effective
domain. -/
@[simp]
theorem mongeAmpereMeasure_compl_interior :
    mongeAmpereMeasure μ f (interior {x | f x ≠ ⊤})ᶜ = 0 := by
  rw [mongeAmpereMeasure]
  split_ifs
  · rw [ofMeasurable_apply _ measurableSet_interior.compl, compl_inter_self]
    simp
  · simp

/-- The Aleksandrov Monge–Ampère measure of a convex function, with respect to a measure that is
finite on compact sets, is finite on every compact subset of the interior of the effective
domain. -/
theorem mongeAmpereMeasure_lt_top [IsFiniteMeasureOnCompacts μ]
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) (hμ : μ ≪ ν) {K : Set E}
    (hK : IsCompact K) (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    mongeAmpereMeasure μ f K < ∞ := by
  rw [mongeAmpereMeasure_apply μ hf hbot hμ hK.measurableSet, inter_eq_left.2 hKD]
  exact (isCompact_subgradientImage hf hbot hK hKD).measure_lt_top

/-- The Aleksandrov Monge–Ampère measure of a convex function, with respect to a measure that is
finite on compact sets, is a locally finite measure on the interior of the effective domain. -/
theorem isLocallyFiniteMeasure_comap_mongeAmpereMeasure [IsFiniteMeasureOnCompacts μ]
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) (hμ : μ ≪ ν) :
    IsLocallyFiniteMeasure
      ((mongeAmpereMeasure μ f).comap ((↑) : interior {x | f x ≠ ⊤} → E)) := by
  have : LocallyCompactSpace (interior {x | f x ≠ ⊤}) := isOpen_interior.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts
      ((mongeAmpereMeasure μ f).comap ((↑) : interior {x | f x ≠ ⊤} → E)) := by
    refine ⟨fun K hK => ?_⟩
    rw [comap_subtype_coe_apply measurableSet_interior]
    exact mongeAmpereMeasure_lt_top μ hf hbot hμ (hK.image continuous_subtype_val)
      (image_subset_iff.2 fun x _ => x.2)
  infer_instance

/-- **The Aleksandrov Monge–Ampère measure of a finite convex function on an open set.** Let `u`
be convex on an open set `Ω`, extended by `⊤` off `Ω`. On a measurable set `s`, its Monge–Ampère
measure is the measure of the set of `y` that are subgradients of `u` relative to `Ω` at some
point of `s ∩ Ω`, i.e. satisfy `u x + ⟪x' - x, y⟫ ≤ u x'` for every `x' ∈ Ω`. -/
theorem mongeAmpereMeasure_ite_apply {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (hμ : μ ≪ ν) {s : Set E} (hs : MeasurableSet s) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) s =
      μ (⋃ x ∈ s ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'}) := by
  have hdom : {x | (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊤} = Ω := by
    ext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hepi : {p : E × ℝ | (if p.1 ∈ Ω then (u p.1 : EReal) else ⊤) ≤ p.2} =
      {p : E × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2} := by
    ext p
    by_cases hp : p.1 ∈ Ω <;> simp [hp]
  have hbot : ∀ x, (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊥ := fun x => by
    by_cases hx : x ∈ Ω <;> simp [hx]
  rw [mongeAmpereMeasure_apply μ (hepi ▸ hu.convex_epigraph) hbot hμ hs, hdom, hΩ.interior_eq]
  congr 1
  ext y
  simp only [mem_subgradientImage_iff, mem_iUnion, exists_prop]
  refine exists_congr fun x => and_congr_right fun hx => ?_
  simp only [mem_subdifferential_iff, hx.2, ite_true, ne_eq, EReal.coe_ne_bot,
    EReal.coe_ne_top, not_false_eq_true, true_and, innerₗ_apply_apply, mem_ofPred_eq]
  refine ⟨fun h x' hx' => by simpa [hx', ← EReal.coe_add] using h x', fun h x' => ?_⟩
  by_cases hx' : x' ∈ Ω
  · simpa [hx', ← EReal.coe_add] using h x' hx'
  · simp [hx']

end TauCeti
