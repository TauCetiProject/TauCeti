/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Differentiability
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# The Aleksandrov Monge–Ampère measure of a convex function

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with `D` the interior of its
effective domain `{x | f x ≠ ⊤}`. The *subgradient image* of a set `s` is
`∂f(s) = ⋃ x ∈ s, ∂f(x)`, the union of the subdifferentials of `f` for the inner product. The
*Aleksandrov Monge–Ampère measure* of `f` is

  `MA_f(s) = μ(∂f(s ∩ D))`

for Borel `s`. It gives the weak (Aleksandrov) sense in which a merely convex function solves
the Monge–Ampère equation `det D²f = ν`. Classically, for a convex function of class `C²` it is
the measure `det (D²f) dx`; that identification is not part of this file.

That `s ↦ μ(∂f(s ∩ D))` is a measure rests on two facts.

* A point `y` that is a subgradient at two distinct points `x₁ ≠ x₂` is a point where the
  conjugate `f⋆` has the two subgradients `x₁` and `x₂`, so `f⋆` is not differentiable there.
  By Rademacher's theorem for the convex function `f⋆`, such points form a `μ`-null set
  (`TauCeti.measure_setOf_mem_subdifferential_of_ne_eq_zero`); this needs no convexity of `f`.
  Hence the subgradient images of disjoint sets are almost disjoint.
* The subgradient image of a compact subset of `D` is compact
  (`TauCeti.isCompact_biUnion_subdifferential`), since `f` is continuous on `D` and its
  subgradients are bounded on compact subsets of `D`. Open subsets of `D` are σ-compact, so their
  subgradient images are measurable; complements are handled by the almost-disjointness, so the
  subgradient image of every Borel subset of `D` is null measurable
  (`TauCeti.nullMeasurableSet_biUnion_subdifferential`).

A finite convex function `u` on an open convex set `Ω` is covered by extending it by `⊤` off `Ω`;
then `D = Ω` and the subdifferential is the set of `y` with `u x + ⟪x' - x, y⟫ ≤ u x'` for all
`x' ∈ Ω` (`TauCeti.mongeAmpereMeasure_ite_apply`).

## Main definitions

* `TauCeti.mongeAmpereMeasure μ f` — the Aleksandrov Monge–Ampère measure of `f`; it is `0` when
  `f` is not convex.

## Main statements

* `TauCeti.mongeAmpereMeasure_apply` — `MA_f(s) = μ(∂f(s ∩ D))` for measurable `s`;
* `TauCeti.mongeAmpereMeasure_compl_interior` — `MA_f` is concentrated on `D`;
* `TauCeti.mongeAmpereMeasure_lt_top` and `TauCeti.isLocallyFiniteMeasure_comap_mongeAmpereMeasure`
  — `MA_f` is finite on compact subsets of `D`, so it is a locally finite measure on `D`;
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

/-- The subgradient inequality between real representatives: if `y ∈ ∂f(x)` and `f x'` is not
`⊤`, then `(f x).toReal + ⟪x' - x, y⟫ ≤ (f x').toReal`. -/
private lemma toReal_add_inner_le_toReal (hbot : ∀ x, f x ≠ ⊥) {x x' y : E}
    (hy : y ∈ subdifferential (innerₗ E) f x) (hx' : f x' ≠ ⊤) :
    (f x).toReal + inner ℝ (x' - x) y ≤ (f x').toReal := by
  have h := add_le_of_mem_subdifferential (innerₗ E) hy x'
  rw [← EReal.coe_toReal (ne_top_of_mem_subdifferential _ hy) (hbot x),
    ← EReal.coe_toReal hx' (hbot x'), innerₗ_apply_apply, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.1 h

section Overlap

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **Almost no point is a subgradient at two distinct points.** For any `f : E → EReal` on a
finite-dimensional real inner product space, the set of `y` lying in the subdifferentials of `f`
at two distinct points is null for every additive Haar measure. Such a `y` is a point where the
convex conjugate `f⋆` has two distinct subgradients, hence is not differentiable, and these
points are null by Rademacher's theorem. -/
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
private lemma aedisjoint_biUnion_subdifferential {s t : Set E} (hst : Disjoint s t) :
    AEDisjoint μ (⋃ x ∈ s, subdifferential (innerₗ E) f x)
      (⋃ x ∈ t, subdifferential (innerₗ E) f x) := by
  refine measure_mono_null ?_ (measure_setOf_mem_subdifferential_of_ne_eq_zero μ f)
  simp only [subset_def, mem_inter_iff, mem_iUnion, exists_prop]
  rintro y ⟨⟨x₁, hx₁, h₁⟩, x₂, hx₂, h₂⟩
  exact ⟨x₁, x₂, fun h => hst.ne_of_mem hx₁ hx₂ h, h₁, h₂⟩

end Overlap

section Convex

variable (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥)
include hf hbot

variable [FiniteDimensional ℝ E]

/-- The subgradients of a convex function are bounded over a compact subset `K` of the interior of
the effective domain: compare `f` at `x ∈ K` and at `x + δ • y / ‖y‖` in a compact thickening of
`K` inside the domain, where `f` is continuous, hence bounded. -/
private lemma exists_norm_le_of_mem_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    ∃ R, ∀ x ∈ K, ∀ y ∈ subdifferential (innerₗ E) f x, ‖y‖ ≤ R := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open isOpen_interior hKD
  obtain ⟨M, hM⟩ := hK.cthickening.exists_bound_of_continuousOn
    ((convexOn_toReal hf hbot).continuousOn_interior.mono hKδ)
  have hM' : ∀ x ∈ cthickening δ K, |(f x).toReal| ≤ M := fun x hx => by
    simpa only [Real.norm_eq_abs] using hM x hx
  refine ⟨2 * M / δ, fun x hx y hy => ?_⟩
  have hxδ : x ∈ cthickening δ K := self_subset_cthickening K hx
  rcases eq_or_ne y 0 with rfl | hy0
  · simpa using div_nonneg (mul_nonneg zero_le_two ((abs_nonneg _).trans (hM' x hxδ))) hδ.le
  have hy0' : 0 < ‖y‖ := norm_pos_iff.2 hy0
  set x' := x + (δ / ‖y‖) • y
  have hx' : x' ∈ cthickening δ K := mem_cthickening_of_dist_le x' x δ K hx <| by
    simp [x', dist_eq_norm, norm_smul, hy0'.ne', abs_of_pos hδ]
  have hle := toReal_add_inner_le_toReal hbot hy (interior_subset (hKδ hx'))
  have hinner : inner ℝ (x' - x) y = δ * ‖y‖ := by
    simp only [x', add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [hinner] at hle
  have h₁ := (abs_le.1 (hM' x' hx')).2
  have h₂ := (abs_le.1 (hM' x hxδ)).1
  rw [le_div_iff₀ hδ]
  linarith

/-- The graph of the subdifferential of a convex function over a compact subset `K` of the
interior of the effective domain is closed: it is cut out of `K × E` by the subgradient
inequalities, which are closed conditions because `f` is continuous there. -/
private lemma isClosed_setOf_mem_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsClosed {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} := by
  set h : E → ℝ := fun x => (f x).toReal
  have hG : {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} =
      (K ×ˢ univ) ∩ ⋂ x' ∈ {x' | f x' ≠ ⊤},
        ((K ×ˢ univ) ∩ (fun z : E × E => h z.1 + inner ℝ (x' - z.1) z.2) ⁻¹' Iic (h x')) := by
    ext ⟨x, y⟩
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, mem_iInter,
      mem_preimage, mem_Iic]
    refine ⟨fun hz => ⟨hz.1, fun x' hx' => ⟨hz.1, toReal_add_inner_le_toReal hbot hz.2 hx'⟩⟩,
      fun hz => ⟨hz.1, ?_⟩⟩
    have hx := interior_subset (hKD hz.1)
    refine (mem_subdifferential_iff _).2 ⟨hbot x, hx, fun x' => ?_⟩
    rcases eq_or_ne (f x') ⊤ with hx' | hx'
    · rw [hx']
      exact le_top
    rw [← EReal.coe_toReal hx (hbot x), ← EReal.coe_toReal hx' (hbot x'), innerₗ_apply_apply,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (hz.2 x' hx').2
  rw [hG]
  refine (hK.isClosed.prod isClosed_univ).inter (isClosed_biInter fun x' _ => ?_)
  refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (hK.isClosed.prod isClosed_univ)
    isClosed_Iic
  refine ContinuousOn.add (((convexOn_toReal hf hbot).continuousOn_interior.mono hKD).comp
    continuousOn_fst fun z hz => hz.1) ?_
  exact ((continuous_const.sub continuous_fst).inner continuous_snd).continuousOn

/-- **Subgradient images of compact sets are compact.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, the union of the subdifferentials of `f` over a
compact subset of the interior of the effective domain is compact. -/
theorem isCompact_biUnion_subdifferential {K : Set E} (hK : IsCompact K)
    (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    IsCompact (⋃ x ∈ K, subdifferential (innerₗ E) f x) := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_mem_subdifferential hf hbot hK hKD
  have hG : IsCompact {z : E × E | z.1 ∈ K ∧ z.2 ∈ subdifferential (innerₗ E) f z.1} :=
    (hK.prod (isCompact_closedBall (0 : E) R)).of_isClosed_subset
      (isClosed_setOf_mem_subdifferential hf hbot hK hKD)
      fun z hz => ⟨hz.1, mem_closedBall_zero_iff.2 (hR z.1 hz.1 z.2 hz.2)⟩
  convert hG.image continuous_snd using 1
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 hy
    exact ⟨(x, y), ⟨hx, hxy⟩, rfl⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hxy⟩, rfl⟩
    exact mem_iUnion₂.2 ⟨x, hx, hxy⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Subgradient images of Borel sets are measurable.** For a convex `f : E → EReal` on a
finite-dimensional real inner product space, the subgradient image of the part of a measurable
set inside the interior of the effective domain is null measurable for every additive Haar
measure. -/
theorem nullMeasurableSet_biUnion_subdifferential {s : Set E} (hs : MeasurableSet s) :
    NullMeasurableSet (⋃ x ∈ s ∩ interior {x | f x ≠ ⊤}, subdifferential (innerₗ E) f x) μ := by
  set D := interior {x | f x ≠ ⊤}
  set S : Set E → Set E := fun t => ⋃ x ∈ t, subdifferential (innerₗ E) f x
  -- On open sets: an open subset of `D` is a countable union of compact sets.
  have hopen : ∀ U, IsOpen U → NullMeasurableSet (S (U ∩ D)) μ := by
    intro U hU
    have : LocallyCompactSpace (U ∩ D : Set E) := (hU.inter isOpen_interior).locallyCompactSpace
    obtain ⟨K, hK, hKU⟩ := isSigmaCompact_iff_sigmaCompactSpace.2 (inferInstance :
      SigmaCompactSpace (U ∩ D : Set E))
    have hS : S (U ∩ D) = ⋃ n, S (K n) := by
      simp only [S, ← hKU, biUnion_iUnion]
    rw [hS]
    refine NullMeasurableSet.iUnion fun n => ?_
    refine (isCompact_biUnion_subdifferential hf hbot (hK n) fun x hx => ?_).isClosed
      |>.measurableSet.nullMeasurableSet
    exact (hKU ▸ mem_iUnion_of_mem n hx : x ∈ U ∩ D).2
  refine MeasurableSet.induction_on_open (C := fun t _ => NullMeasurableSet (S (t ∩ D)) μ)
    hopen ?_ ?_ s hs
  · -- On complements: the subgradient images of `t` and `tᶜ` are almost disjoint and cover the
    -- subgradient image of `D`.
    intro t _ ht
    refine ((hopen univ isOpen_univ).diff ht).congr (ae_eq_set.2 ⟨?_, ?_⟩)
    · refine measure_mono_null (fun y hy => ?_) (measure_empty (μ := μ))
      obtain ⟨⟨hyD, hyt⟩, hytc⟩ := hy
      obtain ⟨x, ⟨-, hx⟩, hyx⟩ := mem_iUnion₂.1 hyD
      by_cases hxt : x ∈ t
      · exact hyt (mem_iUnion₂.2 ⟨x, ⟨hxt, hx⟩, hyx⟩)
      · exact hytc (mem_iUnion₂.2 ⟨x, ⟨hxt, hx⟩, hyx⟩)
    · refine measure_mono_null (fun y hy => ?_) (aedisjoint_biUnion_subdifferential μ (f := f)
        (disjoint_compl_left.mono inter_subset_left inter_subset_left :
          Disjoint (tᶜ ∩ D) (t ∩ D)))
      obtain ⟨hytc, hy'⟩ := hy
      obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hytc
      refine ⟨hytc, ?_⟩
      by_contra hyt
      exact hy' ⟨mem_iUnion₂.2 ⟨x, ⟨mem_univ x, hx.2⟩, hyx⟩, hyt⟩
  · -- On countable unions: the subgradient image commutes with unions.
    intro g _ _ hg
    simpa only [S, iUnion_inter, biUnion_iUnion] using NullMeasurableSet.iUnion hg

end Convex

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open Classical in
/-- The **Aleksandrov Monge–Ampère measure** of `f : E → EReal` with respect to an additive Haar
measure `μ`. When `f` is convex (convex real epigraph, never `⊥`), it is the measure with
`MA_f(s) = μ(⋃ x ∈ s ∩ D, ∂f(x))` for measurable `s`, where `D` is the interior of the effective
domain and `∂f(x)` the subdifferential for the inner product (`mongeAmpereMeasure_apply`).
Otherwise it is `0`. -/
def mongeAmpereMeasure (μ : Measure E) [μ.IsAddHaarMeasure] (f : E → EReal) : Measure E :=
  if h : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ ∀ x, f x ≠ ⊥ then
    Measure.ofMeasurable
      (fun s _ => μ (⋃ x ∈ s ∩ interior {x | f x ≠ ⊤}, subdifferential (innerₗ E) f x))
      (by simp) fun g hg hd => by
        simp only [iUnion_inter, biUnion_iUnion]
        exact measure_iUnion₀
          (fun i j hij => aedisjoint_biUnion_subdifferential μ
            ((hd hij).mono inter_subset_left inter_subset_left))
          fun i => nullMeasurableSet_biUnion_subdifferential h.1 h.2 μ (hg i)
  else 0

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The Aleksandrov Monge–Ampère measure of a convex function evaluated on a measurable set `s` is
the measure of the subgradient image of the part of `s` in the interior of the effective domain. -/
theorem mongeAmpereMeasure_apply (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {s : Set E} (hs : MeasurableSet s) :
    mongeAmpereMeasure μ f s =
      μ (⋃ x ∈ s ∩ interior {x | f x ≠ ⊤}, subdifferential (innerₗ E) f x) := by
  rw [mongeAmpereMeasure, dite_eq_left ⟨hf, hbot⟩, ofMeasurable_apply _ hs]

/-- The Aleksandrov Monge–Ampère measure of a function that is not convex is `0`. -/
theorem mongeAmpereMeasure_of_not
    (h : ¬(Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ ∀ x, f x ≠ ⊥)) :
    mongeAmpereMeasure μ f = 0 := by
  rw [mongeAmpereMeasure, dite_eq_right h]

/-- The Aleksandrov Monge–Ampère measure is concentrated on the interior of the effective
domain. -/
@[simp]
theorem mongeAmpereMeasure_compl_interior :
    mongeAmpereMeasure μ f (interior {x | f x ≠ ⊤})ᶜ = 0 := by
  by_cases h : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2} ∧ ∀ x, f x ≠ ⊥
  · rw [mongeAmpereMeasure_apply μ h.1 h.2 measurableSet_interior.compl, compl_inter_self]
    simp
  · simp [mongeAmpereMeasure_of_not μ h]

/-- The Aleksandrov Monge–Ampère measure of a convex function is finite on every compact subset of
the interior of the effective domain. -/
theorem mongeAmpereMeasure_lt_top (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {K : Set E} (hK : IsCompact K) (hKD : K ⊆ interior {x | f x ≠ ⊤}) :
    mongeAmpereMeasure μ f K < ∞ := by
  rw [mongeAmpereMeasure_apply μ hf hbot hK.measurableSet, inter_eq_left.2 hKD]
  exact (isCompact_biUnion_subdifferential hf hbot hK hKD).measure_lt_top

/-- The Aleksandrov Monge–Ampère measure of a convex function is a locally finite measure on the
interior of the effective domain. -/
theorem isLocallyFiniteMeasure_comap_mongeAmpereMeasure
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) :
    IsLocallyFiniteMeasure
      ((mongeAmpereMeasure μ f).comap ((↑) : interior {x | f x ≠ ⊤} → E)) := by
  have : LocallyCompactSpace (interior {x | f x ≠ ⊤}) := isOpen_interior.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts
      ((mongeAmpereMeasure μ f).comap ((↑) : interior {x | f x ≠ ⊤} → E)) := by
    refine ⟨fun K hK => ?_⟩
    rw [comap_subtype_coe_apply measurableSet_interior]
    exact mongeAmpereMeasure_lt_top μ hf hbot (hK.image continuous_subtype_val)
      (image_subset_iff.2 fun x _ => x.2)
  infer_instance

/-- **The Aleksandrov Monge–Ampère measure of a finite convex function on an open set.** Let `u`
be convex on an open set `Ω`, extended by `⊤` off `Ω`. On a measurable set `s`, its Monge–Ampère
measure is the measure of the set of `y` that are subgradients of `u` relative to `Ω` at some
point of `s ∩ Ω`, i.e. satisfy `u x + ⟪x' - x, y⟫ ≤ u x'` for every `x' ∈ Ω`. -/
theorem mongeAmpereMeasure_ite_apply {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}
    (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) {s : Set E} (hs : MeasurableSet s) :
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
  rw [mongeAmpereMeasure_apply μ (hepi ▸ hu.convex_epigraph) hbot hs, hdom, hΩ.interior_eq]
  congr 1
  refine iUnion₂_congr fun x hx => ?_
  ext y
  simp only [mem_subdifferential_iff, hx.2, ite_true, ne_eq, EReal.coe_ne_bot,
    EReal.coe_ne_top, not_false_eq_true, true_and, innerₗ_apply_apply, mem_ofPred_eq]
  refine ⟨fun h x' hx' => by simpa [hx', ← EReal.coe_add] using h x', fun h x' => ?_⟩
  by_cases hx' : x' ∈ Ω
  · simpa [hx', ← EReal.coe_add] using h x' hx'
  · simp [hx']

end TauCeti
