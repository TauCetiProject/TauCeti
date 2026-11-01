/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.CantorScheme

/-!
# The perfect set theorem for analytic sets

Souslin's perfect set theorem says that an uncountable analytic subset of a Hausdorff space
contains the range of a continuous injection of Cantor space. Consequently an analytic set is
countable or has exactly continuum many points.

An analytic set is the range of a continuous map `f` on a Polish space, so the theorem follows
from a statement about such maps: if `f` has uncountable range, then there is a continuous map
`g` of Cantor space into the domain with `f ∘ g` injective. In the vocabulary of antichains, the
kernel `Setoid.ker f` (the relation `f x = f y`) has a Cantor antichain.

The proof is a Cantor scheme of open sets with uncountable images. Call a point of the domain a
condensation point of `f` when every neighbourhood of it has uncountable image. By second
countability the non-condensation points have countable image, so an open set `U` with
uncountable image contains two condensation points with distinct values. The two values have
disjoint neighbourhoods in the Hausdorff target; shrinking around the two points gives two open
sets of small diameter, with closures inside `U`, with uncountable images, and whose images are
disjoint. Iterating this split produces a closure-antitone scheme of vanishing diameter in a
complete metric on the domain, and `CantorScheme.VanishingDiam.hasCantorAntichainOn` turns it
into a Cantor antichain of `Setoid.ker f`.

## Main results

* `Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range`: a continuous map from a Polish
  space to a Hausdorff space with uncountable range has a Cantor antichain for its kernel.
* `MeasureTheory.AnalyticSet.exists_nat_bool_injection_of_not_countable`: **the perfect set
  theorem for analytic sets**.
* `MeasureTheory.AnalyticSet.mk_le_continuum`: an analytic set has at most `𝔠` points.
* `MeasureTheory.AnalyticSet.mk_eq_continuum_of_not_countable`: an uncountable analytic subset of
  a Hausdorff space has exactly `𝔠` points.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 29.1 (the perfect set theorem for analytic sets, by a Cantor scheme on
  the condensation points of a parametrization).
* The scheme is assembled as in Mathlib's `Perfect.exists_nat_bool_injection`.
-/

public section

open Set Function Filter Topology Cardinal CantorScheme
open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X]

/-- The splitting step of the scheme: an open set with uncountable image under a continuous map
into a Hausdorff space contains two open sets of diameter at most `ε`, with closures inside it,
with uncountable images, and whose images are disjoint. -/
private theorem exists_split_of_not_countable_image [PseudoMetricSpace Y]
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

/-- **Cantor antichains for the kernel of a continuous map.** A continuous map from a Polish
space to a Hausdorff space with uncountable range has a Cantor antichain for its kernel: a
continuous map `g` of Cantor space into the domain with `f ∘ g` injective. -/
theorem Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range [TopologicalSpace Y]
    [PolishSpace Y] [T2Space X]
    {f : Y → X} (hf : Continuous f) (hrange : ¬(range f).Countable) :
    (Setoid.ker f).HasCantorAntichainOn univ := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Y
  obtain ⟨u, -, hu, hu0⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  -- the open sets with uncountable image
  let P := {U : Set Y // IsOpen U ∧ ¬(f '' U).Countable}
  choose W hW hsep using fun (U : P) (n : ℕ) =>
    exists_split_of_not_countable_image hf U.2.1 U.2.2 (hu n).1
  let D : List Bool → P := fun l => l.rec ⟨univ, isOpen_univ, by rwa [image_univ]⟩
    fun a l U => ⟨W U l.length a, (hW U l.length a).1, (hW U l.length a).2.1⟩
  let A : List Bool → Set Y := fun l => (D l).1
  have hA (a : Bool) (l : List Bool) : A (a :: l) = W (D l) l.length a := rfl
  have hanti : ClosureAntitone A := fun l a => by
    rw [hA]
    exact (hW (D l) l.length a).2.2.1
  have hdiam : VanishingDiam A := fun x => by
    refine (tendsto_add_atTop_iff_nat 1).1 <|
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0 (fun _ => zero_le)
        fun n => ?_
    rw [PiNat.res_succ, hA, PiNat.res_length]
    exact (hW (D (PiNat.res x n)) n (x n)).2.2.2
  have hne (l : List Bool) : (A l).Nonempty :=
    nonempty_iff_ne_empty.2 fun h => (D l).2.2 (by simp [A, h])
  have hdom := hanti.map_of_vanishingDiam hdiam hne
  have hlim (x : ℕ → Bool) : (⋂ n, A (PiNat.res x n)).Nonempty :=
    ⟨_, mem_iInter.2 (map_mem ⟨x, hdom ▸ mem_univ x⟩)⟩
  exact hdiam.hasCantorAntichainOn (Setoid.ker f) hlim fun l x hx y hy => by
    rw [hA] at hx hy
    exact hsep (D l) l.length x hx y hy

namespace MeasureTheory

/-- **The perfect set theorem for analytic sets** (Souslin). An uncountable analytic subset of a
Hausdorff space contains the range of a continuous injection of Cantor space. -/
theorem AnalyticSet.exists_nat_bool_injection_of_not_countable [T2Space X] {s : Set X}
    (hs : AnalyticSet s) (hunc : ¬s.Countable) :
    ∃ f : (ℕ → Bool) → X, range f ⊆ s ∧ Continuous f ∧ Injective f := by
  rw [AnalyticSet] at hs
  obtain rfl | ⟨g, hg, rfl⟩ := hs
  · exact absurd countable_empty hunc
  obtain ⟨h, hh, -, hker⟩ :=
    Setoid.hasCantorAntichainOn_iff.1 (Setoid.hasCantorAntichainOn_ker_univ_of_not_countable_range
      hg hunc)
  exact ⟨g ∘ h, range_comp_subset_range h g, hg.comp hh,
    fun a b hab => by_contra fun hne => hker a b hne hab⟩

/-- An analytic set has at most continuum many points. -/
theorem AnalyticSet.mk_le_continuum {s : Set X} (hs : AnalyticSet s) : #s ≤ 𝔠 := by
  rw [AnalyticSet] at hs
  obtain rfl | ⟨g, -, rfl⟩ := hs
  · simp
  · simpa [mk_arrow, aleph0_power_aleph0] using mk_range_le_lift (f := g)

/-- **Analytic sets satisfy the continuum hypothesis.** An uncountable analytic subset of a
Hausdorff space has exactly continuum many points. -/
theorem AnalyticSet.mk_eq_continuum_of_not_countable [T2Space X] {s : Set X} (hs : AnalyticSet s)
    (hunc : ¬s.Countable) : #s = 𝔠 := by
  refine hs.mk_le_continuum.antisymm ?_
  obtain ⟨f, hfs, -, hf⟩ := hs.exists_nat_bool_injection_of_not_countable hunc
  have hinj : Injective fun a => (⟨f a, hfs (mem_range_self a)⟩ : s) :=
    fun a b hab => hf (congrArg Subtype.val hab)
  simpa using lift_mk_le_lift_mk_of_injective hinj

end MeasureTheory
