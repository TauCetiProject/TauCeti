/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Compact

import Mathlib.Topology.Sequences

/-!
# Kuratowski limits of sets

Let `Z i` be subsets of a topological space `X`, indexed along a filter `l`. A set `Z₀` is their
**Kuratowski limit** (`TauCeti.IsKuratowskiLimit`) when

* every neighbourhood of a point of `Z₀` eventually meets `Z i`, and
* every point outside `Z₀` has a neighbourhood that `Z i` eventually misses.

So `Z₀` is at the same time the lower limit (the points every neighbourhood of which eventually
meets the sets) and the upper limit (the points every neighbourhood of which frequently meets
them) of the family; this is Painlevé–Kuratowski convergence. Along a nontrivial filter the limit
is determined by the family (`TauCeti.IsKuratowskiLimit.mem_iff_eventually`,
`TauCeti.IsKuratowskiLimit.mem_iff_frequently`, `TauCeti.IsKuratowskiLimit.unique`) and is
closed (`TauCeti.IsKuratowskiLimit.isClosed`); the constant family `s` has limit `closure s`
(`TauCeti.isKuratowskiLimit_const`).

Unlike convergence in the Hausdorff distance, Kuratowski convergence is local, and it is the
notion of convergence of the zero sets of a sequence of sections on a noncompact manifold:

* **Compact separation.** A compact set disjoint from the limit has a neighbourhood that the sets
  eventually miss (`TauCeti.IsKuratowskiLimit.exists_mem_nhdsSet_eventually_disjoint`).
* **Limits of points.** If `y i ∈ Z i` eventually and `y i → x`, then `x ∈ Z₀`
  (`TauCeti.IsKuratowskiLimit.mem_of_tendsto`).
* **Sequential compactness.** In a second-countable space every sequence of sets has a
  subsequence with a Kuratowski limit (`TauCeti.exists_strictMono_isKuratowskiLimit`). The proof
  records, for each set `b` of a countable basis, whether `Z n` meets `b`; this is a point of the
  compact metrizable space `b ↦ Bool`, and a convergent subsequence of these points decides, for
  every `b`, whether the subsequence eventually meets `b` or eventually misses it.

In a metric space, Hausdorff convergence of closed sets implies Kuratowski convergence, and the
two agree when the space is compact (`TauCeti.isKuratowskiLimit_iff_tendsto` in
`TauCeti.Topology.MetricSpace.Closeds`).

## Main definitions

* `TauCeti.IsKuratowskiLimit l Z Z₀`: the sets `Z i` converge to `Z₀` along `l` in the sense of
  Kuratowski.

## Main results

* `TauCeti.IsKuratowskiLimit.unique`, `TauCeti.IsKuratowskiLimit.isClosed`: along a nontrivial
  filter the limit is unique and closed.
* `TauCeti.IsKuratowskiLimit.exists_mem_nhdsSet_eventually_disjoint`: compact sets disjoint from
  the limit are eventually separated from the sets by a neighbourhood.
* `TauCeti.exists_strictMono_isKuratowskiLimit`: sequential compactness of the Kuratowski
  convergence in second-countable spaces.

## References

* K. Kuratowski, *Topology*, Vol. I, Academic Press, 1966, §29.
* G. Beer, *Topologies on Closed and Closed Convex Sets*, Kluwer, 1993, §5.2.
-/

public section

open Filter Set Topology TopologicalSpace

namespace TauCeti

variable {X ι κ : Type*} [TopologicalSpace X]

/-- The sets `Z i` **converge to `Z₀` along `l` in the sense of Kuratowski**: every neighbourhood
of a point of `Z₀` eventually meets `Z i`, and every point outside `Z₀` has a neighbourhood that
`Z i` eventually misses. -/
@[mk_iff]
structure IsKuratowskiLimit (l : Filter ι) (Z : ι → Set X) (Z₀ : Set X) : Prop where
  /-- Every neighbourhood of a point of the limit eventually meets the sets. -/
  eventually_inter_nonempty : ∀ x ∈ Z₀, ∀ U ∈ 𝓝 x, ∀ᶠ i in l, (Z i ∩ U).Nonempty
  /-- Every point outside the limit has a neighbourhood that the sets eventually miss. -/
  exists_mem_nhds_eventually_disjoint : ∀ x ∉ Z₀, ∃ U ∈ 𝓝 x, ∀ᶠ i in l, Disjoint (Z i) U

namespace IsKuratowskiLimit

variable {l : Filter ι} {Z : ι → Set X} {Z₀ Z₁ : Set X}

/-- Kuratowski limits are preserved by reindexing along a map tending to the filter, in
particular by passing to a subsequence or to a finer filter. -/
theorem comp (h : IsKuratowskiLimit l Z Z₀) {l' : Filter κ} {φ : κ → ι}
    (hφ : Tendsto φ l' l) : IsKuratowskiLimit l' (Z ∘ φ) Z₀ where
  eventually_inter_nonempty x hx U hU := hφ.eventually (h.eventually_inter_nonempty x hx U hU)
  exists_mem_nhds_eventually_disjoint x hx := by
    obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x hx
    exact ⟨U, hU, hφ.eventually hZU⟩

/-- Along a nontrivial filter, a point lies in the Kuratowski limit exactly when every
neighbourhood of it eventually meets the sets. -/
theorem mem_iff_eventually [l.NeBot] (h : IsKuratowskiLimit l Z Z₀) {x : X} :
    x ∈ Z₀ ↔ ∀ U ∈ 𝓝 x, ∀ᶠ i in l, (Z i ∩ U).Nonempty := by
  refine ⟨h.eventually_inter_nonempty x, fun hx ↦ ?_⟩
  by_contra hx₀
  obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x hx₀
  obtain ⟨i, hi, hi'⟩ := ((hx U hU).and hZU).exists
  exact hi.ne_empty (Set.disjoint_iff_inter_eq_empty.1 hi')

/-- Along a nontrivial filter, a point lies in the Kuratowski limit exactly when every
neighbourhood of it frequently meets the sets. -/
theorem mem_iff_frequently [l.NeBot] (h : IsKuratowskiLimit l Z Z₀) {x : X} :
    x ∈ Z₀ ↔ ∀ U ∈ 𝓝 x, ∃ᶠ i in l, (Z i ∩ U).Nonempty := by
  refine ⟨fun hx U hU ↦ (h.eventually_inter_nonempty x hx U hU).frequently, fun hx ↦ ?_⟩
  by_contra hx₀
  obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x hx₀
  obtain ⟨i, hi, hi'⟩ := ((hx U hU).and_eventually hZU).exists
  exact hi.ne_empty (Set.disjoint_iff_inter_eq_empty.1 hi')

/-- Along a nontrivial filter, the Kuratowski limit of a family of sets is unique. -/
theorem unique [l.NeBot] (h₀ : IsKuratowskiLimit l Z Z₀) (h₁ : IsKuratowskiLimit l Z Z₁) :
    Z₀ = Z₁ :=
  Set.ext fun _ ↦ h₀.mem_iff_eventually.trans h₁.mem_iff_eventually.symm

/-- Along a nontrivial filter, a Kuratowski limit is closed. -/
theorem isClosed [l.NeBot] (h : IsKuratowskiLimit l Z Z₀) : IsClosed Z₀ := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_)
  obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x hx
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  -- Every point `y` of the open set `V` has the neighbourhood `V`, which the sets eventually miss.
  refine Filter.mem_of_superset (hV.mem_nhds hxV) fun y hy hyZ ↦ ?_
  obtain ⟨i, hi, hi'⟩ :=
    ((h.eventually_inter_nonempty y hyZ V (hV.mem_nhds hy)).and hZU).exists
  exact hi.ne_empty (Set.disjoint_iff_inter_eq_empty.1 (hi'.mono_right hVU))

/-- **Compact separation from a Kuratowski limit.** A compact set `K` disjoint from the
Kuratowski limit has a neighbourhood that the sets eventually miss. -/
theorem exists_mem_nhdsSet_eventually_disjoint (h : IsKuratowskiLimit l Z Z₀) {K : Set X}
    (hK : IsCompact K) (hKZ : Disjoint K Z₀) :
    ∃ U ∈ 𝓝ˢ K, ∀ᶠ i in l, Disjoint (Z i) U := by
  refine hK.induction_on (p := fun s ↦ ∃ U ∈ 𝓝ˢ s, ∀ᶠ i in l, Disjoint (Z i) U)
    ⟨∅, by simp, by simp⟩ (fun s t hst ⟨U, hU, hZU⟩ ↦ ⟨U, nhdsSet_mono hst hU, hZU⟩)
    (fun s t ⟨U, hU, hZU⟩ ⟨V, hV, hZV⟩ ↦ ⟨U ∪ V, union_mem_nhdsSet hU hV, ?_⟩) fun x hx ↦ ?_
  · filter_upwards [hZU, hZV] with i hi hi' using Disjoint.union_right hi hi'
  -- Near each point of `K` the sets eventually miss an open neighbourhood of that point.
  obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x (hKZ.notMem_of_mem_left hx)
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.1 hU
  exact ⟨V, mem_nhdsWithin_of_mem_nhds (hV.mem_nhds hxV), V, hV.mem_nhdsSet.2 subset_rfl,
    hZU.mono fun i hi ↦ hi.mono_right hVU⟩

/-- **Limits of points of the sets lie in the Kuratowski limit.** If eventually `y i ∈ Z i`, and
`y i → x` along a nontrivial filter, then `x` lies in the Kuratowski limit. -/
theorem mem_of_tendsto [l.NeBot] (h : IsKuratowskiLimit l Z Z₀) {y : ι → X} {x : X}
    (hy : ∀ᶠ i in l, y i ∈ Z i) (hyx : Tendsto y l (𝓝 x)) : x ∈ Z₀ := by
  by_contra hx
  obtain ⟨U, hU, hZU⟩ := h.exists_mem_nhds_eventually_disjoint x hx
  obtain ⟨i, hi, hiU, hi'⟩ := (hy.and ((hyx.eventually_mem hU).and hZU)).exists
  exact Set.disjoint_left.1 hi' hi hiU

end IsKuratowskiLimit

/-- The constant family `s` converges in the sense of Kuratowski to the closure of `s`. -/
theorem isKuratowskiLimit_const (l : Filter ι) (s : Set X) :
    IsKuratowskiLimit l (fun _ ↦ s) (closure s) where
  eventually_inter_nonempty _ hx _ hU := Eventually.of_forall fun _ ↦
    (mem_closure_iff_nhds.1 hx _ hU).mono fun _ ↦ And.symm
  exists_mem_nhds_eventually_disjoint _ hx :=
    ⟨(closure s)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx,
      Eventually.of_forall fun _ ↦ Set.disjoint_compl_right_iff_subset.2 subset_closure⟩

/-- **Sequential compactness of Kuratowski convergence.** In a second-countable space, every
sequence of sets has a subsequence that converges in the sense of Kuratowski. -/
theorem exists_strictMono_isKuratowskiLimit [SecondCountableTopology X] (Z : ℕ → Set X) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z₀ : Set X, IsKuratowskiLimit atTop (Z ∘ φ) Z₀ := by
  classical
  obtain ⟨B, hBc, -, hB⟩ := exists_countable_basis X
  have := hBc.to_subtype
  -- Record which basic open sets `Z n` meets, as a point of the compact space `B → Bool`.
  obtain ⟨w, φ, hφ, hw⟩ := CompactSpace.tendsto_subseq
    fun n (b : B) ↦ decide ((Z n ∩ (b : Set X)).Nonempty)
  have hw' (b : B) : ∀ᶠ n in atTop, decide ((Z (φ n) ∩ (b : Set X)).Nonempty) = w b := by
    have := tendsto_pi_nhds.1 hw b
    rwa [nhds_discrete, tendsto_pure] at this
  refine ⟨φ, hφ, {x | ∀ b : B, x ∈ (b : Set X) → w b = true}, fun x hx U hU ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨b, hb, hxb, hbU⟩ := hB.mem_nhds_iff.1 hU
    filter_upwards [hw' ⟨b, hb⟩] with n hn
    rw [hx ⟨b, hb⟩ hxb, decide_eq_true_iff] at hn
    exact hn.mono (Set.inter_subset_inter_right _ hbU)
  · simp only [Set.mem_ofPred_eq, not_forall, Bool.not_eq_true] at hx
    obtain ⟨b, hxb, hb⟩ := hx
    refine ⟨b, (hB.isOpen b.property).mem_nhds hxb, ?_⟩
    filter_upwards [hw' b] with n hn
    rw [hb, decide_eq_false_iff_not, Set.not_nonempty_iff_eq_empty] at hn
    exact Set.disjoint_iff_inter_eq_empty.2 hn

end TauCeti
