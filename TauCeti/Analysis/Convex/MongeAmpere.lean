/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Hessian
public import TauCeti.Analysis.Convex.SubgradientImage
public import TauCeti.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The Aleksandrov Monge–Ampère measure of a convex function

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with `D` the interior of its
effective domain `{x | f x ≠ ⊤}`. The *subgradient image* of a set `s` is
`∂f(s) = ⋃ x ∈ s, ∂f(x)` (`TauCeti.subgradientImage`), the union of the subdifferentials of `f`
for the inner product. The *Aleksandrov Monge–Ampère measure* of `f` is

  `MA_f(s) = μ(∂f(s ∩ D))`

for Borel `s`. It gives the weak (Aleksandrov) sense in which a merely convex function solves
the Monge–Ampère equation `det D²f = ν`. The same formula defines a measure for every `μ`
absolutely continuous with respect to a Haar measure, such as the weighted measure
`s ↦ ∫_{∂f(s ∩ D)} g` for `μ = volume.withDensity g`.

That `s ↦ μ(∂f(s ∩ D))` is a measure rests on two facts.

* A point `y` that is a subgradient at two distinct points `x₁ ≠ x₂` is a point where the
  conjugate `f⋆` has the two subgradients `x₁` and `x₂`, so `f⋆` is not differentiable there.
  By Rademacher's theorem for the convex function `f⋆`, such points form a `μ`-null set
  (`TauCeti.measure_setOf_exists_ne_mem_subdifferential_eq_zero`); this needs no convexity of `f`.
  Hence the subgradient images of disjoint sets are almost disjoint.
* The subgradient image of a compact subset of `D` is compact
  (`TauCeti.isCompact_subgradientImage`). Open subsets of `D` are σ-compact, so their
  subgradient images are measurable; complements are handled by the almost-disjointness, so the
  subgradient image of every Borel subset of `D` is null measurable
  (`TauCeti.nullMeasurableSet_subgradientImage`).

A finite convex function `u` on an open convex set `Ω` is covered by extending it by `⊤` off `Ω`;
then `D = Ω` and the subdifferential is the set of `y` with `u x + ⟪x' - x, y⟫ ≤ u x'` for all
`x' ∈ Ω` (`TauCeti.mongeAmpereMeasure_ite_apply`).

For a convex function that is twice differentiable on `D`, the Aleksandrov measure is the
classical one, `MA_f = det (D²f) dx` on `D` (`TauCeti.mongeAmpereMeasure_eq_withDensity_det`).
On `D` the subdifferential is the gradient, so `MA_f(s) = μ(∇f(s ∩ D))`. The change of variables
formula computes this on the set where the Hessian is nondegenerate, since the gradient is
injective there (`TauCeti.apply_sub_eq_zero_of_gradient_eq`). The gradient image of the set
where the Hessian is degenerate is null, and the Hessian of a convex function has nonnegative
determinant (`TauCeti.isPositive_of_hasFDerivAt_gradient`).

The *Aleksandrov maximum principle* bounds a convex function by its Monge–Ampère mass: if `u` is
convex on a bounded open convex `Ω`, continuous on the closure and nonnegative on the frontier,
then `(-u x₀) ^ n ≤ C diam(Ω) ^ (n - 1) dist(x₀, ∂Ω) MA_u(Ω)` for `x₀ ∈ Ω`, with
`C = 2 ^ (n + 1) / μ (ball 0 1)`
(`TauCeti.ofReal_neg_pow_mul_addHaar_ball_le_mul_mongeAmpereMeasure`). Every slope `p` of an
affine function through `(x₀, u x₀)` lying below `u` on the frontier is a subgradient of `u` at
some point of `Ω` (`TauCeti.exists_forall_add_inner_le_of_forall_frontier`). When `u ≥ 0` on the
frontier, these slopes include a convex set containing a ball of radius `-u x₀ / diam Ω` and a
point of norm `-u x₀ / dist(x₀, ∂Ω)`, and the volume of such a set is bounded below by
`Convex.ofReal_dist_mul_pow_mul_addHaar_ball_le`.

## Main definitions

* `TauCeti.mongeAmpereMeasure μ f` — the Aleksandrov Monge–Ampère measure of `f`; it is `0` when
  `f` is not convex or `μ` is not absolutely continuous with respect to a Haar measure.

## Main statements

* `TauCeti.measure_setOf_exists_ne_mem_subdifferential_eq_zero` and
  `TauCeti.aedisjoint_subgradientImage` — almost no point is a subgradient at two distinct points,
  so subgradient images of disjoint sets are almost disjoint;
* `TauCeti.mongeAmpereMeasure_apply` — `MA_f(s) = μ(∂f(s ∩ D))` for measurable `s`;
* `TauCeti.mongeAmpereMeasure_compl_interior` — `MA_f` is concentrated on `D`;
* `TauCeti.mongeAmpereMeasure_lt_top` and `TauCeti.isLocallyFiniteMeasure_comap_mongeAmpereMeasure`
  — when `μ` is finite on compact sets, `MA_f` is finite on compact subsets of `D`, so it is a
  locally finite measure on `D`;
* `TauCeti.mongeAmpereMeasure_ite_apply` — the formula for a finite convex function on an open
  set;
* `TauCeti.mongeAmpereMeasure_eq_withDensity_det` and
  `TauCeti.mongeAmpereMeasure_ite_eq_withDensity_det` — for a twice differentiable convex function,
  the Aleksandrov measure is `det (D²f) dx` on the interior of the effective domain;
* `TauCeti.exists_forall_add_inner_le_of_forall_frontier` — slopes of affine functions through a
  point of the graph that lie below the boundary values are subgradients at points of `Ω`;
* `TauCeti.ofReal_neg_pow_mul_addHaar_ball_le_mul_mongeAmpereMeasure` — **the Aleksandrov
  maximum principle**.

## References

* A. D. Aleksandrov, *Dirichlet's problem for the equation Det ‖z_{ij}‖ = φ(z₁, …, zₙ, z, x₁, …,
  xₙ). I*, Vestnik Leningrad. Univ. Ser. Mat. Meh. Astr. 13 (1958), 5–24.
* C. E. Gutiérrez, *The Monge–Ampère Equation*, 2nd ed., Progress in Nonlinear Differential
  Equations and Their Applications 89, Birkhäuser, 2016, §1.1, in particular Theorem 1.1.13, and
  §1.4 for the Aleksandrov maximum principle.
* A. Figalli, *The Monge–Ampère Equation and Its Applications*, Zurich Lectures in Advanced
  Mathematics, EMS, 2017, §2.1, in particular Theorem 2.3.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Measure Set Filter Metric Module
open scoped Topology ENNReal Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → EReal}

section Overlap

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- **Almost no point is a subgradient at two distinct points.** For any `f : E → EReal` on a
finite-dimensional real inner product space, the set of `y` lying in the subdifferentials of `f`
at two distinct points is null for every additive Haar measure. -/
theorem measure_setOf_exists_ne_mem_subdifferential_eq_zero (f : E → EReal) :
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

/-- **Subgradient images of disjoint sets are almost disjoint.** For any `f : E → EReal` on a
finite-dimensional real inner product space, the subgradient images of disjoint sets meet in a
null set for every additive Haar measure. -/
theorem aedisjoint_subgradientImage (f : E → EReal) {s t : Set E} (hst : Disjoint s t) :
    AEDisjoint μ (subgradientImage (innerₗ E) f s) (subgradientImage (innerₗ E) f t) := by
  refine measure_mono_null ?_ (measure_setOf_exists_ne_mem_subdifferential_eq_zero μ f)
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
    · refine measure_mono_null (fun y hy => ?_) (aedisjoint_subgradientImage μ f
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
          (fun i j hij => hμ (aedisjoint_subgradientImage ν f
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

section Ite

variable {Ω : Set E} [DecidablePred (· ∈ Ω)] {u : E → ℝ}

/-- **The Aleksandrov Monge–Ampère measure of a finite convex function on an open set.** Let `u`
be convex on an open set `Ω`, extended by `⊤` off `Ω`. On a measurable set `s`, its Monge–Ampère
measure is the measure of the set of `y` that are subgradients of `u` relative to `Ω` at some
point of `s ∩ Ω`, i.e. satisfy `u x + ⟪x' - x, y⟫ ≤ u x'` for every `x' ∈ Ω`. -/
theorem mongeAmpereMeasure_ite_apply (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (hμ : μ ≪ ν)
    {s : Set E} (hs : MeasurableSet s) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) s =
      μ (⋃ x ∈ s ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'}) := by
  rw [mongeAmpereMeasure_apply μ (convex_epigraph_ite hu) ite_ne_bot hμ hs, setOf_ite_ne_top,
    hΩ.interior_eq]
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

end Ite

/-! ### Twice differentiable convex functions -/

section Smooth

variable [μ.IsAddHaarMeasure]

/-- **The Monge–Ampère measure of a twice differentiable convex function is `det (D²f) dx`.**
Let `f : E → EReal` be convex and never `⊥`, with real representative `F x = (f x).toReal`, and
suppose that on the interior `D` of the effective domain both `F` and its gradient `∇ F` are
differentiable. Then for every additive Haar measure `μ`, the Aleksandrov Monge–Ampère measure of
`f` is `μ` restricted to `D` with density `det (D(∇ F))`, the determinant of the Hessian. -/
theorem mongeAmpereMeasure_eq_withDensity_det (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥)
    (hd : ∀ x ∈ interior {x | f x ≠ ⊤}, DifferentiableAt ℝ (fun x' => (f x').toReal) x)
    (hd₂ : ∀ x ∈ interior {x | f x ≠ ⊤},
      DifferentiableAt ℝ (∇ fun x' => (f x').toReal) x) :
    mongeAmpereMeasure μ f = (μ.restrict (interior {x | f x ≠ ⊤})).withDensity
      fun x => ENNReal.ofReal (fderiv ℝ (∇ fun x' => (f x').toReal) x).det := by
  set D := interior {x | f x ≠ ⊤}
  set G := ∇ fun x' => (f x').toReal
  have hH : ∀ x ∈ D, HasFDerivAt G (fderiv ℝ G x) x := fun x hx => (hd₂ x hx).hasFDerivAt
  have hdet : ∀ x ∈ D, 0 ≤ (fderiv ℝ G x).det := fun x hx =>
    (isPositive_of_hasFDerivAt_gradient hf hbot hx
      (eventually_of_mem (isOpen_interior.mem_nhds hx) hd) (hH x hx)).det_nonneg
  -- The nondegenerate set `{det ≠ 0}` is measurable.
  have hN : MeasurableSet {x | (fderiv ℝ G x).det ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage
      (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ G))
  ext s hs
  set S := s ∩ D
  have hS : MeasurableSet S := hs.inter measurableSet_interior
  rw [mongeAmpereMeasure_apply μ hf hbot AbsolutelyContinuous.rfl hs,
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  -- On `D` the subdifferential is the gradient, so the subgradient image of `S` is `G '' S`.
  have himage : subgradientImage (innerₗ E) f S = G '' S := by
    ext y
    simp only [mem_subgradientImage_iff, mem_image]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨x, hx, gradient_toReal_eq_of_mem_subdifferential hy
        (mem_interior_iff_mem_nhds.1 hx.2) (hd x hx.2)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, gradient_toReal_mem_subdifferential hf hbot (interior_subset hx.2) (hd x hx.2)⟩
  rw [himage]
  -- The gradient image of the degenerate part `{det = 0}` is null.
  have hZ : μ (G '' (S \ {x | (fderiv ℝ G x).det ≠ 0})) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hH x hx.1.2).hasFDerivWithinAt) fun x hx => not_not.1 hx.2
  -- The gradient is injective on the nondegenerate part, by the flat-segment lemma.
  have hinj : InjOn G (S ∩ {x | (fderiv ℝ G x).det ≠ 0}) := by
    intro x₁ hx₁ x₂ hx₂ hg
    by_contra hne
    refine hx₁.2 (LinearMap.det_eq_zero_iff_ker_ne_bot.2 ((Submodule.ne_bot_iff _).2
      ⟨x₂ - x₁, LinearMap.mem_ker.2 ?_, sub_ne_zero.2 (Ne.symm hne)⟩))
    exact apply_sub_eq_zero_of_gradient_eq hf hbot hx₁.1.2 hx₂.1.2
      (fun y hy => hd y ((convex_setOf_ne_top hf).interior.segment_subset hx₁.1.2 hx₂.1.2 hy))
      hg (hH x₁ hx₁.1.2)
  calc μ (G '' S) = μ (G '' (S ∩ {x | (fderiv ℝ G x).det ≠ 0})) := by
        refine le_antisymm ?_ (measure_mono (image_mono inter_subset_left))
        calc μ (G '' S)
            = μ (G '' (S ∩ {x | (fderiv ℝ G x).det ≠ 0}) ∪
                G '' (S \ {x | (fderiv ℝ G x).det ≠ 0})) := by
              rw [← image_union, inter_union_sdiff]
          _ ≤ _ := measure_union_le _ _
          _ = _ := by rw [hZ, add_zero]
    _ = ∫⁻ x in S ∩ {x | (fderiv ℝ G x).det ≠ 0}, ENNReal.ofReal |(fderiv ℝ G x).det| ∂μ :=
        (lintegral_abs_det_fderiv_eq_addHaar_image μ (hS.inter hN)
          (fun x hx => (hH x hx.1.2).hasFDerivWithinAt) hinj).symm
    _ = ∫⁻ x in S, ENNReal.ofReal (fderiv ℝ G x).det ∂μ := by
        rw [← lintegral_inter_add_sdiff _ S hN, setLIntegral_congr_fun (hS.diff hN)
          (g := fun _ => 0) fun x hx => by simp [not_not.1 hx.2], lintegral_zero, add_zero]
        exact setLIntegral_congr_fun (hS.inter hN) fun x hx => by
          rw [abs_of_nonneg (hdet x hx.1.2)]

/-- **The Monge–Ampère measure of a twice differentiable convex function on an open set.** If `u`
is convex on an open set `Ω`, and `u` and its gradient are differentiable on `Ω`, then the
Aleksandrov Monge–Ampère measure of `u` (extended by `⊤` off `Ω`) is `det (D²u) dx` on `Ω`: it is
`μ` restricted to `Ω` with density `det (D(∇ u))`, for every additive Haar measure `μ`. This
applies in particular to every convex `u` of class `C²` on `Ω`. -/
theorem mongeAmpereMeasure_ite_eq_withDensity_det {Ω : Set E} [DecidablePred (· ∈ Ω)]
    {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (hd : DifferentiableOn ℝ u Ω)
    (hd₂ : DifferentiableOn ℝ (∇ u) Ω) :
    mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) =
      (μ.restrict Ω).withDensity fun x => ENNReal.ofReal (fderiv ℝ (∇ u) x).det := by
  -- Near each point of `Ω`, the real representative of the extension is `u`.
  have hF : ∀ x ∈ Ω, (fun x' => ((if x' ∈ Ω then (u x' : EReal) else ⊤)).toReal) =ᶠ[𝓝 x] u :=
    fun x hx => eventually_of_mem (hΩ.mem_nhds hx) fun x' hx' => by simp [hx']
  have hG : ∀ x ∈ Ω, (∇ fun x' => ((if x' ∈ Ω then (u x' : EReal) else ⊤)).toReal) =ᶠ[𝓝 x] ∇ u :=
    fun x hx => (hF x hx).gradient
  have hD : interior {x | (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊤} = Ω := by
    rw [setOf_ite_ne_top, hΩ.interior_eq]
  have hdF : ∀ x ∈ interior {x | (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊤},
      DifferentiableAt ℝ (fun x' => ((if x' ∈ Ω then (u x' : EReal) else ⊤)).toReal) x := by
    rw [hD]
    exact fun x hx => ((hd x hx).differentiableAt (hΩ.mem_nhds hx)).congr_of_eventuallyEq (hF x hx)
  have hdG : ∀ x ∈ interior {x | (if x ∈ Ω then (u x : EReal) else ⊤) ≠ ⊤},
      DifferentiableAt ℝ (∇ fun x' => ((if x' ∈ Ω then (u x' : EReal) else ⊤)).toReal) x := by
    rw [hD]
    exact fun x hx =>
      ((hd₂ x hx).differentiableAt (hΩ.mem_nhds hx)).congr_of_eventuallyEq (hG x hx)
  rw [mongeAmpereMeasure_eq_withDensity_det μ (convex_epigraph_ite hu) ite_ne_bot hdF hdG, hD]
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs, Measure.restrict_restrict hs]
  exact setLIntegral_congr_fun (hs.inter hΩ.measurableSet) fun x hx => by
    rw [(hG x hx.2).fderiv_eq]

end Smooth

/-! ### The Aleksandrov maximum principle -/

section MaximumPrinciple

variable {Ω : Set E} {u : E → ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Slopes below the boundary values are subgradients.** Let `Ω` be bounded and `u` continuous
on its closure, and let `x₀ ∈ Ω`. If the affine function `x ↦ u x₀ + ⟪x - x₀, p⟫` lies below `u`
on the frontier of `Ω`, then `p` is a subgradient of `u` relative to `Ω` at some point `x₁ ∈ Ω`:
`u x₁ + ⟪x - x₁, p⟫ ≤ u x` for every `x ∈ Ω`. -/
theorem exists_forall_add_inner_le_of_forall_frontier [ProperSpace E]
    (hΩ : Bornology.IsBounded Ω) (hu : ContinuousOn u (closure Ω)) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {p : E} (hp : ∀ x ∈ frontier Ω, u x₀ + inner ℝ (x - x₀) p ≤ u x) :
    ∃ x₁ ∈ Ω, ∀ x ∈ Ω, u x₁ + inner ℝ (x - x₁) p ≤ u x := by
  -- Minimize `u - ⟪·, p⟫` over the compact closure of `Ω`.
  have hcont : ContinuousOn (fun x => u x - inner ℝ x p) (closure Ω) :=
    hu.sub (continuous_id.inner continuous_const).continuousOn
  obtain ⟨x₁, hx₁, hmin⟩ := hΩ.isCompact_closure.exists_isMinOn ⟨x₀, subset_closure hx₀⟩ hcont
  have hmin' : ∀ x ∈ Ω, u x₁ - inner ℝ x₁ p ≤ u x - inner ℝ x p := fun x hx =>
    isMinOn_iff.1 hmin x (subset_closure hx)
  by_cases h₁ : x₁ ∈ Ω
  · refine ⟨x₁, h₁, fun x hx => ?_⟩
    have := hmin' x hx
    rw [inner_sub_left]
    linarith
  · -- A minimum on the frontier is no smaller than the value at `x₀`, which is then a minimum.
    refine ⟨x₀, hx₀, fun x hx => ?_⟩
    have h₂ := hp x₁ ⟨hx₁, fun h => h₁ (interior_subset h)⟩
    have h₃ := hmin' x hx
    rw [inner_sub_left] at h₂ ⊢
    linarith

variable [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure] [DecidablePred (· ∈ Ω)]

/-- **The Aleksandrov maximum principle.** Let `Ω` be a bounded open convex subset of a real inner
product space `E` of finite dimension `n ≥ 1`, and let `u` be convex on `Ω`, continuous on its
closure, and nonnegative on its frontier. Then at every `x₀ ∈ Ω`,

  `(-u x₀) ^ n * μ (ball 0 1) ≤ 2 ^ (n + 1) * diam Ω ^ (n - 1) * dist(x₀, ∂Ω) * MA_u(Ω)`,

where `dist(x₀, ∂Ω)` is the distance from `x₀` to the complement of `Ω` and `MA_u` is the
Aleksandrov Monge–Ampère measure of `u` (extended by `⊤` off `Ω`) with respect to the additive
Haar measure `μ`. When `MA_u(Ω)` is finite, this bounds `-u` below on `Ω` and shows that
`-u x₀ = O(dist(x₀, ∂Ω) ^ (1 / n))` as `x₀` approaches the boundary. -/
theorem ofReal_neg_pow_mul_addHaar_ball_le_mul_mongeAmpereMeasure (hΩo : IsOpen Ω)
    (hΩ : Bornology.IsBounded Ω) (hu : ConvexOn ℝ Ω u) (hc : ContinuousOn u (closure Ω))
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ENNReal.ofReal (-u x₀) ^ finrank ℝ E * μ (ball 0 1) ≤
      2 ^ (finrank ℝ E + 1) * ENNReal.ofReal (diam Ω ^ (finrank ℝ E - 1) * infDist x₀ Ωᶜ) *
        mongeAmpereMeasure μ (fun x => if x ∈ Ω then (u x : EReal) else ⊤) Ω := by
  -- The subgradient image of `Ω` contains the convex set `P` of slopes of affine functions through
  -- `(x₀, u x₀)` lying below `0` on the frontier. It contains the ball of radius `h / D` about `0`,
  -- with `h = -u x₀` and `D = diam Ω`, and a slope of norm `h / d`, with `d = dist(x₀, ∂Ω)`,
  -- normal to a hyperplane supporting `Ω` at a nearest point of the complement.
  set n := finrank ℝ E
  have hn : 1 ≤ n := finrank_pos
  rcases le_or_gt 0 (u x₀) with hux₀ | hux₀
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_pow (by omega), zero_mul]
    exact bot_le
  set h := -u x₀
  have hh : 0 < h := by linarith
  set d := infDist x₀ Ωᶜ
  set D := diam Ω
  -- The complement of `Ω` is nonempty, and `x₀` is at positive distance `d` from it, attained at
  -- some `z ∉ Ω`; the ball of radius `d` about `x₀` lies in `Ω`, so `D ≥ 2 * d > 0`.
  have hΩc : Ωᶜ.Nonempty := nonempty_compl.2 fun h' => NormedSpace.unbounded_univ ℝ E (h' ▸ hΩ)
  obtain ⟨z, hz, hzd⟩ := hΩo.isClosed_compl.exists_infDist_eq_dist hΩc x₀
  have hd : 0 < d := (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩc).1 fun h' => h' hx₀
  have hD : 0 < D := by
    have hsub : ball x₀ d ⊆ Ω := by simpa using ball_infDist_subset_compl (x := x₀) (s := Ωᶜ)
    have := diam_mono hsub hΩ
    rw [diam_ball_eq x₀ hd.le] at this
    linarith
  -- The admissible slopes.
  set P := {p : E | ∀ x ∈ frontier Ω, u x₀ + inner ℝ (x - x₀) p ≤ 0}
  have hPconv : Convex ℝ P := by
    intro p hp q hq a b ha hb hab x hx
    have h₁ := mul_le_mul_of_nonneg_left (hp x hx) ha
    have h₂ := mul_le_mul_of_nonneg_left (hq x hx) hb
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith
  have hball : ball 0 (h / D) ⊆ P := by
    intro p hp x hx
    rw [mem_ball_zero_iff] at hp
    have hxD : ‖x - x₀‖ ≤ D := by
      rw [← dist_eq_norm]
      calc dist x x₀ ≤ diam (closure Ω) :=
            dist_le_diam_of_mem hΩ.closure (frontier_subset_closure hx) (subset_closure hx₀)
        _ = D := diam_closure Ω
    have := (real_inner_le_norm (x - x₀) p).trans
      (mul_le_mul hxD hp.le (norm_nonneg p) hD.le)
    rw [mul_div_cancel₀ h hD.ne'] at this
    linarith
  -- A supporting half-space of `Ω` through `z` gives a slope of norm `h / d`.
  obtain ⟨g, hg⟩ := geometric_hahn_banach_open_point hu.1 hΩo hz
  set w := (InnerProductSpace.toDual ℝ E).symm g
  have hw : ∀ a, inner ℝ w a = g a := fun a => InnerProductSpace.toDual_symm_apply
  have hw0 : w ≠ 0 := fun h' => by simpa [← hw, h'] using hg x₀ hx₀
  have hw0' : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hq : (h / (d * ‖w‖)) • w ∈ P := by
    intro x hx
    have hgx : g x ≤ g z :=
      closure_minimal (fun a ha => (hg a ha).le) (isClosed_le g.continuous continuous_const)
        (frontier_subset_closure hx)
    have hdz : d = ‖z - x₀‖ := by
      rw [dist_comm, dist_eq_norm] at hzd
      exact hzd
    have hgz : g (z - x₀) ≤ ‖w‖ * d := by
      rw [← hw, hdz]
      exact real_inner_le_norm w (z - x₀)
    rw [map_sub] at hgz
    have key : h / (d * ‖w‖) * (g x - g x₀) ≤ h :=
      calc h / (d * ‖w‖) * (g x - g x₀) ≤ h / (d * ‖w‖) * (‖w‖ * d) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = h := by field_simp
    rw [real_inner_smul_right, real_inner_comm, hw, map_sub]
    have hdef : h = -u x₀ := rfl
    linarith
  have hqn : dist ((h / (d * ‖w‖)) • w) 0 = h / d := by
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  -- Every admissible slope is a subgradient of `u` relative to `Ω` at a point of `Ω`.
  have hPS : P ⊆ ⋃ x ∈ Ω ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'} := by
    intro p hp
    obtain ⟨x₁, hx₁, hx₁'⟩ := exists_forall_add_inner_le_of_forall_frontier hΩ hc hx₀
      fun x hx => (hp x hx).trans (hfr x hx)
    exact mem_biUnion ⟨hx₁, hx₁⟩ hx₁'
  -- Multiply the volume bound for `P` through by `D ^ (n - 1) * d`.
  have hreal : D ^ (n - 1) * d * (h / d * (h / D) ^ (n - 1)) = h ^ n := by
    rw [div_pow, ← Nat.sub_add_cancel hn, pow_succ']
    simp only [Nat.add_sub_cancel]
    field_simp
  calc ENNReal.ofReal h ^ n * μ (ball 0 1)
      = ENNReal.ofReal (D ^ (n - 1) * d) *
          (ENNReal.ofReal (h / d * (h / D) ^ (n - 1)) * μ (ball 0 1)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), hreal,
          ENNReal.ofReal_pow hh.le]
    _ ≤ ENNReal.ofReal (D ^ (n - 1) * d) * (2 ^ (n + 1) * μ P) := by
        rw [← hqn]
        gcongr _ * ?_
        exact hPconv.ofReal_dist_mul_pow_mul_addHaar_ball_le (μ := μ) (div_pos hh hD) hball hq
    _ ≤ ENNReal.ofReal (D ^ (n - 1) * d) *
          (2 ^ (n + 1) * μ (⋃ x ∈ Ω ∩ Ω, {y | ∀ x' ∈ Ω, u x + inner ℝ (x' - x) y ≤ u x'})) := by
        gcongr
    _ = _ := by
        rw [mongeAmpereMeasure_ite_apply μ hΩo hu AbsolutelyContinuous.rfl hΩo.measurableSet]
        ring

end MaximumPrinciple

end TauCeti
