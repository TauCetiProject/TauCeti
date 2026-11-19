/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.Perfect
public import TauCeti.Topology.Bases

/-!
# Perfect sets in metric spaces

A Polish space has at most continuum many points
(`TauCeti.mk_le_continuum_of_secondCountableTopology`). A nonempty perfect subset of a completely
metrizable space contains a copy of Cantor space, so it has at least continuum many points.
Together these give the cardinality of a nonempty perfect subset of a Polish space: exactly `𝔠`.

In a perfect extended metric space, a nonempty open set also splits into two disjoint nonempty
open sets of small diameter whose closures stay inside it: the open-set counterpart of Mathlib's
`Perfect.small_diam_splitting`, used to build Cantor schemes of open sets.

The same split holds for an open set with uncountable image under a continuous map `f` from a
second countable extended pseudometric space into a Hausdorff space, with uncountable and disjoint
images: the points with a neighbourhood of countable image have countable image by second
countability, so the open set contains two condensation points of `f` with distinct values. This
is the step of the perfect set theorem for analytic sets.

## Main results

* `Perfect.continuum_le_mk`: a nonempty perfect subset of a completely metrizable space has at
  least `𝔠` points.
* `Perfect.mk_eq_continuum`: a nonempty perfect subset of a Polish space has exactly `𝔠` points.
* `IsOpen.exists_disjoint_closure_subset`: in a perfect extended metric space, a nonempty open set
  contains two disjoint nonempty open sets of small diameter, with closures inside it.
* `Continuous.exists_split_of_not_countable_image`: for a continuous map from a second countable
  extended pseudometric space into a Hausdorff space, an open set with uncountable image contains
  two open sets of small diameter, with closures inside it, with uncountable and disjoint images.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 6.2 and Corollary 6.3.
-/

public section

open Set Function Filter Cardinal TopologicalSpace Topology
open scoped ENNReal

universe u

variable {X : Type u} [TopologicalSpace X] {C : Set X}

/-- **A nonempty perfect set in a completely metrizable space has at least continuum many
points**: it contains the range of a continuous injection of Cantor space. -/
theorem Perfect.continuum_le_mk [IsCompletelyMetrizableSpace X] (hC : Perfect C)
    (hne : C.Nonempty) : 𝔠 ≤ #C := by
  let := upgradeIsCompletelyMetrizable X
  obtain ⟨f, hfC, -, hf⟩ := hC.exists_nat_bool_injection hne
  have hinj : Injective fun x => (⟨f x, hfC (mem_range_self x)⟩ : C) := fun x y hxy =>
    hf (congrArg Subtype.val hxy)
  simpa using lift_mk_le_lift_mk_of_injective hinj

/-- **A nonempty perfect set in a Polish space has cardinality continuum.** -/
theorem Perfect.mk_eq_continuum [PolishSpace X] (hC : Perfect C) (hne : C.Nonempty) :
    #C = 𝔠 :=
  le_antisymm (TauCeti.mk_le_continuum_of_secondCountableTopology C) (hC.continuum_le_mk hne)

section Split

variable {X : Type*} [EMetricSpace X]

/-- **Splitting a nonempty open set** in a perfect extended metric space: a nonempty open set `V`
contains two disjoint nonempty open sets of diameter at most `ε`, with closures inside `V`. -/
theorem IsOpen.exists_disjoint_closure_subset [PerfectSpace X] {V : Set X} (hV : IsOpen V)
    (hne : V.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Bool → Set X, (∀ b, IsOpen (W b)) ∧ (∀ b, (W b).Nonempty) ∧
      (∀ b, closure (W b) ⊆ V) ∧ (∀ b, Metric.ediam (W b) ≤ ε) ∧ Disjoint (W false) (W true) := by
  -- an open neighbourhood of `z` inside the ball of radius `r`, with closure inside `V`
  have hsmall (z : X) (hz : z ∈ V) (r : ℝ≥0∞) (hr : 0 < r) : ∃ W, IsOpen W ∧ z ∈ W ∧
      closure W ⊆ V ∧ W ⊆ Metric.eball z r := by
    obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hV.mem_nhds hz)
    refine ⟨interior t ∩ Metric.eball z r, isOpen_interior.inter Metric.isOpen_eball,
      ⟨mem_interior_iff_mem_nhds.2 ht, Metric.mem_eball_self hr⟩, ?_, inter_subset_right⟩
    exact (htc.closure_subset_iff.2 (inter_subset_left.trans interior_subset)).trans htV
  -- two distinct points of `V`, at positive distance `d`
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyV, hyx⟩ :=
    (𝓝[≠] x).nonempty_of_mem (sdiff_mem_nhdsWithin_compl (hV.mem_nhds hx) {x})
  have hd : 0 < edist x y := edist_pos.2 (Ne.symm hyx)
  set r := min (edist x y / 2) (ε / 2)
  have hr : 0 < r := lt_min (ENNReal.half_pos hd.ne') (ENNReal.half_pos hε.ne')
  obtain ⟨W₀, hW₀o, hxW₀, hW₀V, hW₀r⟩ := hsmall x hx r hr
  obtain ⟨W₁, hW₁o, hyW₁, hW₁V, hW₁r⟩ := hsmall y hyV r hr
  have h2r : 2 * r ≤ ε :=
    calc 2 * r ≤ 2 * (ε / 2) := by gcongr; exact min_le_right _ _
      _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hdiam {z : X} {W : Set X} (hW : W ⊆ Metric.eball z r) : Metric.ediam W ≤ ε :=
    ((Metric.ediam_mono hW).trans Metric.ediam_eball_le).trans h2r
  refine ⟨fun b => cond b W₁ W₀, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, ?_⟩
  · cases b <;> assumption
  · cases b
    exacts [⟨x, hxW₀⟩, ⟨y, hyW₁⟩]
  · cases b <;> assumption
  · cases b
    exacts [hdiam hW₀r, hdiam hW₁r]
  · refine (Metric.eball_disjoint ?_).mono hW₀r hW₁r
    exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans (ENNReal.add_halves _).le

end Split

section SplitImage

variable {Y : Type*}

/-- **Splitting an open set with uncountable image**: an open set `U` with uncountable image
under a continuous map `f` from a second countable extended pseudometric space into a Hausdorff
space contains two open sets of diameter at most `ε`, with closures inside `U`, with uncountable
images under `f`, and whose images under `f` are disjoint. -/
theorem Continuous.exists_split_of_not_countable_image [PseudoEMetricSpace Y]
    [SecondCountableTopology Y] [T2Space X] {f : Y → X} (hf : Continuous f) {U : Set Y}
    (hU : IsOpen U) (hfU : ¬(f '' U).Countable) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Bool → Set Y, (∀ b, IsOpen (W b) ∧ ¬(f '' W b).Countable ∧ closure (W b) ⊆ U ∧
      Metric.ediam (W b) ≤ ε) ∧ ∀ x ∈ W false, ∀ y ∈ W true, f x ≠ f y := by
  -- the points with a neighbourhood of countable image have countable image
  set N := {y | ∃ V ∈ 𝓝 y, (f '' V).Countable}
  have hN : (f '' N).Countable := by
    choose! V hV hVc using fun y (hy : y ∈ N) => hy
    obtain ⟨t, htN, htc, hNt⟩ :=
      TopologicalSpace.countable_cover_nhdsWithin fun y hy => mem_nhdsWithin_of_mem_nhds (hV y hy)
    refine (htc.biUnion fun y hy => hVc y (htN hy)).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hNt hy)
    exact mem_iUnion₂.2 ⟨z, hz, mem_image_of_mem f hyz⟩
  -- so `U` contains two condensation points with distinct values
  have hdiff : ¬(f '' (U \ N)).Countable := fun h =>
    hfU <| (h.union hN).mono fun _ ⟨y, hyU, hy⟩ => by
      by_cases hyN : y ∈ N
      · exact Or.inr ⟨y, hyN, hy⟩
      · exact Or.inl ⟨y, ⟨hyU, hyN⟩, hy⟩
  obtain ⟨_, ⟨y₀, ⟨hy₀U, hy₀N⟩, rfl⟩, _, ⟨y₁, ⟨hy₁U, hy₁N⟩, rfl⟩, hne⟩ :=
    not_subsingleton_iff.1 fun h => hdiff h.countable
  obtain ⟨V₀, V₁, hV₀, hV₁, hy₀V, hy₁V, hV⟩ := t2_separation hne
  -- a small open neighbourhood of a condensation point, inside `U` and mapped into `V`
  have piece (y : Y) (hyU : y ∈ U) (hyN : y ∉ N) (V : Set X) (hVo : IsOpen V) (hyV : f y ∈ V) :
      ∃ W, IsOpen W ∧ ¬(f '' W).Countable ∧ closure W ⊆ U ∧ Metric.ediam W ≤ ε ∧ W ⊆ f ⁻¹' V := by
    obtain ⟨t, ht, htc, htUV⟩ :=
      exists_mem_nhds_isClosed_subset ((hU.inter (hVo.preimage hf)).mem_nhds ⟨hyU, hyV⟩)
    have hsub : closure (interior t ∩ Metric.eball y (ε / 2)) ⊆ U ∩ f ⁻¹' V :=
      ((closure_mono (inter_subset_left.trans interior_subset)).trans htc.closure_subset).trans
        htUV
    refine ⟨interior t ∩ Metric.eball y (ε / 2), isOpen_interior.inter Metric.isOpen_eball,
      fun hc => hyN ⟨_, inter_mem (interior_mem_nhds.2 ht)
        (Metric.eball_mem_nhds y (ENNReal.half_pos hε.ne')), hc⟩,
      hsub.trans inter_subset_left, ?_, subset_closure.trans (hsub.trans inter_subset_right)⟩
    calc Metric.ediam (interior t ∩ Metric.eball y (ε / 2))
        ≤ Metric.ediam (Metric.eball y (ε / 2)) := Metric.ediam_mono inter_subset_right
      _ ≤ 2 * (ε / 2) := Metric.ediam_eball_le
      _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  obtain ⟨W₀, hW₀⟩ := piece y₀ hy₀U hy₀N V₀ hV₀ hy₀V
  obtain ⟨W₁, hW₁⟩ := piece y₁ hy₁U hy₁N V₁ hV₁ hy₁V
  refine ⟨fun b => bif b then W₁ else W₀, fun b => ?_, fun x hx y hy hxy => ?_⟩
  · cases b
    exacts [⟨hW₀.1, hW₀.2.1, hW₀.2.2.1, hW₀.2.2.2.1⟩, ⟨hW₁.1, hW₁.2.1, hW₁.2.2.1, hW₁.2.2.2.1⟩]
  · exact hV.ne_of_mem (hW₀.2.2.2.2 hx) (hW₁.2.2.2.2 hy) hxy

end SplitImage
