/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.IsLUB

/-!
# Limits of total variation bounds

This file transfers eventual upper bounds on the total variations of a family of maps to a
`liminf` bound on the total variation of a pointwise limit. It also computes the variation of a
composition with an antitone map on an interval, proves stability of bounded variation under
addition and subtraction, shows that the variation is unchanged by postcomposition with a map
that preserves the distances between the values of the function, and proves bounded variation of
constant extensions from closed intervals.
Total variation on continuous maps is lower semicontinuous for the compact-open topology,
allowing measurable path-space applications. Nested finite subsets recover the full extended
variation, while containing any prescribed sequence of finite subsets.

## Main results

* `eVariationOn.eq_iSup_finset`: variation is the supremum over finite subsets.
* `eVariationOn.exists_monotone_finset_tendsto`: nested finite subsets recover variation.
* `ContinuousMap.lowerSemicontinuous_eVariationOn`: lower semicontinuity on continuous path space.
* `TauCeti.eVariationOn_le_liminf_of_eventually_le`: an eventual bound on the total variations of
  a family of maps bounds the total variation of a pointwise limit by the `liminf` of the bounds.
* `eVariationOn.comp_inter_Icc_eq_of_antitoneOn`: the antitone counterpart of Mathlib's
  `eVariationOn.comp_inter_Icc_eq_of_monotoneOn`.
* `eVariationOn.comp_eq_of_edist_eq`: postcomposition with a map preserving the distances between
  the values of a function does not change its variation.
* `BoundedVariationOn.IccExtend`: constant extension from a closed interval preserves bounded
  variation.
* `TauCeti.eVariationOn_id_unitInterval` and `LipschitzWith.eVariationOn_unitInterval_le`: the
  identity of the unit interval has total variation `1`, so a `C`-Lipschitz map on the unit
  interval has total variation at most `C`.
-/

public section

/-- Total variation is lower semicontinuous on continuous paths with the compact-open topology.
The variation is allowed to be infinite. -/
theorem ContinuousMap.lowerSemicontinuous_eVariationOn
    {α E : Type*} [LinearOrder α] [TopologicalSpace α] [PseudoEMetricSpace E] (s : Set α) :
    LowerSemicontinuous (fun f : C(α, E) => eVariationOn f s) := by
  intro f v hv
  exact eVariationOn.lowerSemicontinuous_aux
    (fun x _ => (continuous_eval_const x).continuousAt) hv

open Filter Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [LinearOrder α] {X : Type*}

section WeakPseudoEMetricSpace

variable [TopologicalSpace X] [WeakPseudoEMetricSpace X]

/-- The metric variation of a path in a subtype is unchanged by applying its coercion. -/
@[simp] theorem eVariationOn_subtypeVal_comp {s : Set X} {f : α → s} {t : Set α} :
    eVariationOn f t = eVariationOn ((Subtype.val : s → X) ∘ f) t := by
  rfl

end WeakPseudoEMetricSpace

variable [PseudoEMetricSpace X]

/-- If the total variations of the maps `F i` on `s` are eventually bounded by `u i`, then the
total variation on `s` of a pointwise limit of the `F i` is at most `liminf u`. -/
theorem eVariationOn_le_liminf_of_eventually_le {ι : Type*} {l : Filter ι} {s : Set α}
    {f : α → X} {F : ι → α → X} {u : ι → ℝ≥0∞}
    (hu : ∀ᶠ i in l, eVariationOn (F i) s ≤ u i)
    (hf : ∀ x ∈ s, Tendsto (fun i ↦ F i x) l (nhds (f x))) :
    eVariationOn f s ≤ liminf u l := by
  rw [le_liminf_iff]
  intro v hv
  filter_upwards [eVariationOn.lowerSemicontinuous_aux hf hv, hu] with i hi hui
  exact hi.trans_le hui

open scoped unitInterval

/-- The inclusion of the unit interval into `ℝ` has total variation `1`. This is the simp-normal
form of `TauCeti.eVariationOn_id_unitInterval`. -/
@[simp]
theorem eVariationOn_subtypeVal_unitInterval : eVariationOn (Subtype.val : I → ℝ) univ = 1 := by
  rw [← Function.id_comp Subtype.val,
    eVariationOn.comp_eq_of_monotoneOn id Subtype.val (fun _ _ _ _ h ↦ h), image_univ,
    Subtype.range_coe_subtype, ofPred_mem_eq, unitInterval, eVariationOn_id_Icc, sub_zero,
    ENNReal.ofReal_one]

/-- The identity of the unit interval has total variation `1`. -/
theorem eVariationOn_id_unitInterval : eVariationOn (id : I → I) univ = 1 := by
  rw [eVariationOn_subtypeVal_comp, Function.comp_id, eVariationOn_subtypeVal_unitInterval]

end TauCeti

open scoped NNReal unitInterval in
/-- A `C`-Lipschitz map on the unit interval has total variation at most `C`. -/
theorem LipschitzWith.eVariationOn_unitInterval_le {X : Type*} [PseudoEMetricSpace X]
    {f : I → X} {C : ℝ≥0} (hf : LipschitzWith C f) : eVariationOn f univ ≤ C := by
  simpa only [Function.comp_id, TauCeti.eVariationOn_id_unitInterval, mul_one] using
    hf.lipschitzOnWith.comp_eVariationOn_le (mapsTo_id univ)

namespace eVariationOn

variable {α β E : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace E]
  [WeakPseudoEMetricSpace E]

/-- Postcomposing `f` with a map `g` that preserves the distances between the values of `f` on `s`
does not change the variation of `f` on `s`. -/
theorem comp_eq_of_edist_eq {F : Type*} [TopologicalSpace F] [WeakPseudoEMetricSpace F]
    {f : α → E} {g : E → F} {s : Set α}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (g (f x)) (g (f y)) = edist (f x) (f y)) :
    eVariationOn (g ∘ f) s = eVariationOn f s := by
  refine iSup_congr fun p ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  exact h _ (p.2.2.2 _) _ (p.2.2.2 _)

open OrderDual in
/-- The variation of `f ∘ φ` on `t ∩ [x, y]` for an antitone `φ` is the variation of `f` on the
corresponding reversed interval of `φ '' t`. -/
theorem comp_inter_Icc_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    eVariationOn (f ∘ φ) (t ∩ Icc x y) = eVariationOn f (φ '' t ∩ Icc (φ y) (φ x)) := by
  have := comp_inter_Icc_eq_of_monotoneOn (f ∘ ofDual) (toDual ∘ φ) hφ.dual_right hx hy
  rwa [Function.comp_apply, Function.comp_apply, Icc_toDual, image_comp,
    Equiv.image_eq_preimage_symm, toDual_symm_eq, ← preimage_inter, comp_ofDual] at this

end eVariationOn

/-- Constant extension of a path outside a closed interval preserves bounded variation. -/
theorem BoundedVariationOn.IccExtend {α E : Type*} [LinearOrder α]
    [TopologicalSpace E] [WeakPseudoEMetricSpace E] {f : α → E} {a b : α}
    (hf : BoundedVariationOn f (Icc a b)) (hab : a ≤ b) :
    BoundedVariationOn (IccExtend hab (f ∘ Subtype.val)) univ := by
  exact ne_top_of_le_ne_top hf (eVariationOn.comp_le_of_monotoneOn f
    (fun x : α ↦ (projIcc a b hab x : α))
    (fun _ _ _ _ h ↦ (monotone_projIcc hab h : _ ≤ _))
    (fun x _ ↦ (projIcc a b hab x).property))

section Congruence

variable {α E : Type*} [LinearOrder α] [TopologicalSpace E] [WeakPseudoEMetricSpace E]
  {f g : α → E} {s : Set α}

/-- Bounded variation is preserved when functions agree on the domain. -/
theorem BoundedVariationOn.congr (hf : BoundedVariationOn f s) (h : EqOn f g s) :
    BoundedVariationOn g s := by
  unfold BoundedVariationOn at *
  rwa [← eVariationOn.congr h]

/-- Local bounded variation is preserved when functions agree on the domain. -/
theorem LocallyBoundedVariationOn.congr (hf : LocallyBoundedVariationOn f s)
    (h : EqOn f g s) : LocallyBoundedVariationOn g s :=
  fun a b ha hb ↦ (hf a b ha hb).congr (h.mono inter_subset_left)

end Congruence

section AdditionSubtraction

variable {α E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]
  {f g : α → E} {s : Set α}

/-- The variation of a sum is at most the sum of the variations. -/
theorem eVariationOn.add_le :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact edist_add_add_le (f (u (i + 1))) (g (u (i + 1))) (f (u i)) (g (u i))
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-- Negation does not change the variation of a function. -/
@[simp] theorem eVariationOn.neg : eVariationOn (-f) s = eVariationOn f s := by
  exact eVariationOn.comp_eq_of_edist_eq (g := fun x : E ↦ -x)
    (fun _ _ _ _ ↦ edist_neg_neg _ _)

/-- The variation of a difference is at most the sum of the variations. -/
theorem eVariationOn.sub_le :
    eVariationOn (f - g) s ≤ eVariationOn f s + eVariationOn g s := by
  simpa only [sub_eq_add_neg, eVariationOn.neg] using
    (eVariationOn.add_le (f := f) (g := -g) (s := s))

/-- The sum of two bounded-variation functions has bounded variation. -/
theorem BoundedVariationOn.add (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) eVariationOn.add_le

/-- Local bounded variation is stable under addition. -/
theorem LocallyBoundedVariationOn.add
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f + g) s :=
  fun a b ha hb ↦ (hf a b ha hb).add (hg a b ha hb)

/-- The difference of two bounded-variation functions has bounded variation. -/
theorem BoundedVariationOn.sub (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f - g) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) eVariationOn.sub_le

/-- Local bounded variation is stable under subtraction. -/
theorem LocallyBoundedVariationOn.sub
    (hf : LocallyBoundedVariationOn f s) (hg : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f - g) s :=
  fun a b ha hb ↦ (hf a b ha hb).sub (hg a b ha hb)

end AdditionSubtraction

namespace eVariationOn

open scoped Topology

variable {α E : Type*} [LinearOrder α] [TopologicalSpace E] [WeakPseudoEMetricSpace E]

/-- Total variation is the supremum of variations on finite subsets of the domain. -/
theorem eq_iSup_finset (f : α → E) (s : Set α) :
    eVariationOn f s = ⨆ p : {p : Finset α // (p : Set α) ⊆ s},
      eVariationOn f (p.1 : Set α) := by
  classical
  apply le_antisymm
  · refine iSup_le fun ⟨n, u, hu, hus⟩ ↦ ?_
    let p := (Finset.range (n + 1)).image u
    have hp : (p : Set α) ⊆ s := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hus i
    exact (sum_le_of_monotoneOn_Iic (hu.monotoneOn _) (fun i hi ↦ by
      simp only [p, Finset.mem_coe, Finset.mem_image, Finset.mem_range]
      exact ⟨i, by omega, rfl⟩)).trans
      (le_iSup (fun p : {p : Finset α // (p : Set α) ⊆ s} ↦
        eVariationOn f (p.1 : Set α)) ⟨p, hp⟩)
  · exact iSup_le fun p ↦ mono f p.2

/-- Nested finite subsets recover the full extended variation. A prescribed finite set may be
adjoined at each stage; this does not require any regularity of the function. -/
theorem exists_monotone_finset_tendsto (f : α → E) (s : Set α) (q : ℕ → Finset α)
    (hq : ∀ n, (q n : Set α) ⊆ s) :
    ∃ p : ℕ → Finset α, Monotone p ∧ (∀ n, (p n : Set α) ⊆ s) ∧
      (∀ n, q n ⊆ p n) ∧
      Tendsto (fun n ↦ eVariationOn f (p n : Set α)) atTop (𝓝 (eVariationOn f s)) := by
  classical
  let S := {p : Finset α // (p : Set α) ⊆ s}
  let v : S → ℝ≥0∞ := fun p ↦ eVariationOn f (p.1 : Set α)
  have hne : (range v).Nonempty := ⟨v ⟨∅, by simp⟩, mem_range_self _⟩
  obtain ⟨w, _, _, hw, hmem⟩ := (isLUB_iSup (f := v)).exists_seq_monotone_tendsto hne
  choose r hr using hmem
  let p (n : ℕ) := (Finset.range (n + 1)).biUnion fun i ↦ (r i).1 ∪ q i
  have hmono : Monotone p := by
    intro i j hij x hx
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨k, Finset.range_mono (by omega) hk, hx⟩
  have hp (n : ℕ) : (p n : Set α) ⊆ s := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_union.mp hi).elim (fun h ↦ (r i).2 h) (fun h ↦ hq i h)
  have hrp (n : ℕ) : (r n).1 ⊆ p n := fun x hx ↦
    Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_left _ hx⟩
  refine ⟨p, hmono, hp, fun n x hx ↦
    Finset.mem_biUnion.mpr ⟨n, by simp, Finset.mem_union_right _ hx⟩, ?_⟩
  rw [eq_iSup_finset f s]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hw tendsto_const_nhds
    (fun n ↦ (hr n).symm ▸ mono f (hrp n))
    (fun n ↦ (mono f (hp n)).trans_eq (eq_iSup_finset f s))

end eVariationOn
