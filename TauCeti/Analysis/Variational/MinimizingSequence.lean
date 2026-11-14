/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Analysis.Variational.BoundedSublevels
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Variational.DirectMethod
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Minimizing sequences and the sequential direct method

For a real-valued energy `E` bounded below on a nonempty admissible set `S`, quantitative
minimizing sequences `u : ℕ → X` in `S` satisfying `E (u n) < sInf (E '' S) + 1 / (n + 1)` and
`E (u n) → sInf (E '' S)` always exist (`TauCeti.exists_seq_forall_mem_and_lt_sInf_add_one_div`);
for general first-countable conditionally complete linear orders, antitone minimizing sequences are
provided by `TauCeti.exists_seq_forall_mem_and_tendsto_sInf` in `TauCeti.Topology.Order.IsLUB`.

In a reflexive real or complex normed space (where `NormedSpace.inclusionInDoubleDual 𝕜 V` is
surjective, without assuming completeness), every norm-bounded minimizing sequence in a subset `T`
whose weak limits lie in `S` and satisfy the lower-limit bound for `E` admits a subsequence
converging weakly to a minimizer `v ∈ S` with `E v = sInf (E '' S)` whenever the codomain is a
conditionally complete lattice. In particular, existence of one norm-bounded minimizing sequence in
a sequentially weakly closed set `S` suffices for attainment of the infimum
(`TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`), including when sequential closedness
and sequential lower semicontinuity hold only on a single bounded sublevel containing the sequence,
and when the minimizer is unique the entire minimizing sequence converges weakly to it.

Finally, combining sequential sublevel closedness with the sequential-closure form of
Eberlein–Šmulian shows that bounded sublevels of a sequentially weakly lower semicontinuous energy
on a sequentially weakly closed set are weakly compact, yielding the sequential direct method and
weak compactness of minimizer sets for any linearly ordered codomain without a separate lower-bound
assumption.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 1 and proof of Theorem 4.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

section MinimizingSequence

/-- On a nonempty set where a real-valued energy `E` is bounded below, there exists a minimizing
sequence `u` in `S` satisfying the quantitative bound `E (u n) < sInf (E '' S) + 1 / (n + 1)`. -/
theorem exists_seq_forall_mem_and_lt_sInf_add_one_div {X : Type*} {E : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hbdd : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  have hex (n : ℕ) : ∃ u ∈ S, E u < sInf (E '' S) + 1 / ((n : ℝ) + 1) := by
    have hlt : sInf (E '' S) < sInf (E '' S) + 1 / ((n : ℝ) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨_, ⟨u, hu, rfl⟩, hu_lt⟩ := exists_lt_of_csInf_lt (hne.image E) hlt
    exact ⟨u, hu, hu_lt⟩
  choose u hu hEu using hex
  refine ⟨u, hu, hEu, ?_⟩
  have hupper : Tendsto (fun n : ℕ ↦ sInf (E '' S) + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (sInf (E '' S))) := by
    simpa only [add_zero] using
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n ↦ csInf_le hbdd (mem_image_of_mem E (hu n))) fun n ↦ (hEu n).le

end MinimizingSequence

section MinimizingSequenceConvergence

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Subsequential weak convergence of bounded minimizing sequences.** In a reflexive normed
space, every norm-bounded sequence `u` in `T` with `E (u n) → sInf (E '' S)`, where weak limits of
sequences in `T` lie in `S` and satisfy the lower-limit inequality for `E`, admits a subsequence
converging weakly to a minimizer `v ∈ S` with `E v = sInf (E '' S)`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn {β : Type*}
    [ConditionallyCompleteLattice β] [TopologicalSpace β] {E : V → β} {S T : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ T) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hE : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, (∀ n, w n ∈ T) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ T) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v ∧ E v = sInf (E '' S) := by
  have hcomp : IsCompact (closure (toWeakSpace 𝕜 V '' range u)) :=
    isCompact_closure_toWeakSpace hV hb
  obtain ⟨v, φ, hφ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hcomp fun n ↦ mem_range_self n
  have hv : v ∈ S := hS (fun n ↦ hu (φ n)) hlim
  have hEv_le : E v ≤ sInf (E '' S) :=
    hE (fun n ↦ hu (φ n)) hlim (hmin.comp hφ.tendsto_atTop)
  have hEv : E v = sInf (E '' S) :=
    hEv_le.antisymm (csInf_le hbdd (mem_image_of_mem E hv))
  exact ⟨v, hv, φ, hφ, hlim, (isMinOn_iff_eq_csInf hv hbdd).2 hEv, hEv⟩

/-- **The sequential direct method.** In a reflexive normed space, an energy bounded below on a
sequentially weakly closed set, sequentially weakly lower semicontinuous there, attains its
minimum as soon as one norm-bounded minimizing sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence {β : Type*}
    [ConditionallyCompleteLattice β] [TopologicalSpace β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hE : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hv, -, -, -, hminv, -⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn hV hbdd hS hE hu hb hmin
  exact ⟨v, hv, hminv⟩

/-- Single-sublevel variant of the sequential direct method: weak limits of sequences in one
bounded relative sublevel `{x ∈ S | E x ≤ b}` containing the minimizing sequence need only lie in
`S` and satisfy the lower-limit bound for `E`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_sublevel {β : Type*}
    [ConditionallyCompleteLattice β] [TopologicalSpace β] {E : V → β} {S : Set V} {b : β}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hb : IsBounded {x ∈ S | E x ≤ b})
    (hS : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S ∧ E (w n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hE : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, (∀ n, w n ∈ S ∧ E (w n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ n, E (u n) ≤ b)
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hv, -, -, -, hminv, -⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn (T := {x ∈ S | E x ≤ b}) hV hbdd hS hE
      (fun n ↦ ⟨hu n, hub n⟩) (hb.subset (range_subset_iff.2 fun n ↦ ⟨hu n, hub n⟩)) hmin
  exact ⟨v, hv, hminv⟩

/-- Subsequential weak convergence of a norm-bounded minimizing sequence phrased in terms of
`IsSeqClosed` and `SeqLowerSemicontinuousOn` on `WeakSpace 𝕜 V`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_seqLowerSemicontinuousOn {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v ∧ E v = sInf (E '' S) := by
  have hS' := isSeqClosed_toWeakSpace_image_iff.1 hS
  exact exists_subseq_tendsto_toWeakSpace_isMinOn hV hbdd hS'
    (fun _ _ _ hw hlim hElim ↦ (toWeakSpace 𝕜 V).toEquiv.le_of_seqLowerSemicontinuousOn_image
      hE (hS' hw hlim) hw hlim hElim) hu hb hmin

/-- Sequential direct method phrased in terms of `IsSeqClosed` and `SeqLowerSemicontinuousOn` on
`WeakSpace 𝕜 V`. -/
theorem exists_isMinOn_of_seqLowerSemicontinuousOn_of_bounded_minimizing_sequence {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hv, -, -, -, hminv, -⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_seqLowerSemicontinuousOn
      hV hbdd hS hE hu hb hmin
  exact ⟨v, hv, hminv⟩

/-- When `v` is the unique minimizer of `E` on `S`, the entire norm-bounded minimizing sequence
`u` converges weakly to `v` without passing to a subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn {β : Type*}
    [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V} {v : V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) → z ∈ S)
    (hE : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄ ⦃r : β⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E z ≤ r)
    (huniq : ∀ w ∈ S, IsMinOn E S w → w = v)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hb' : IsBounded (range (u ∘ ns)) := hb.subset (range_comp_subset_range ns u)
  obtain ⟨w, hw, φ, -, hlim, hminw, -⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn
      hV hbdd hS hE (fun n ↦ hu (ns n)) hb' (hmin.comp hns)
  exact ⟨φ, huniq w hw hminw ▸ hlim⟩

/-- Full-sequence weak convergence to a unique minimizer phrased in terms of `IsSeqClosed` and
`SeqLowerSemicontinuousOn` on `WeakSpace 𝕜 V`. -/
theorem tendsto_toWeakSpace_of_seqLowerSemicontinuousOn_of_unique_isMinOn {β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V} {v : V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (huniq : ∀ w ∈ S, IsMinOn E S w → w = v)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  have hS' := isSeqClosed_toWeakSpace_image_iff.1 hS
  exact tendsto_toWeakSpace_of_unique_isMinOn hV hbdd hS'
    (fun _ _ _ hw hlim hElim ↦ (toWeakSpace 𝕜 V).toEquiv.le_of_seqLowerSemicontinuousOn_image
      hE (hS' hw hlim) hw hlim hElim) huniq hu hb hmin

end MinimizingSequenceConvergence

section SequentialBoundedSublevels

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive normed space, every norm-bounded sublevel
of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq]
  have hseq : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    rw [heq]
    exact hE.isSeqClosed_sublevel hS b
  have hcomp_cl : IsCompact (closure (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :=
    isCompact_closure_toWeakSpace hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_weakSpace_iff_isSeqClosed hcomp_cl).2 hseq
  simpa only [hclosed.closure_eq] using hcomp_cl

/-- A single nonempty norm-bounded sublevel suffices for the sequential direct method on a
sequentially weakly closed admissible set, without assuming a lower bound on the energy or a
topology on the linearly ordered codomain. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE b hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono fun _ hx ↦ hx.1
  have hlsc : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (lowerSemicontinuousOn_weakSpace_iff_seqLowerSemicontinuousOn hcompact).2 (hE.mono hsubset)
  obtain ⟨u, hu, hmin⟩ :=
    exists_isMinOn_of_weak_closed hV hne hcompact.isClosed hlsc (hb.hasBoundedSublevelsOn E)
  exact ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 hmin⟩

/-- **The sequential direct method under bounded sublevels.** A sequentially weakly lower
semicontinuous energy with norm-bounded sublevels on a nonempty sequentially weakly closed set in
a reflexive normed space attains its minimum. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a sequentially weakly lower semicontinuous energy on a
sequentially weakly closed set in a reflexive normed space is norm bounded, then it is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE (E u) hb

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive normed space, the set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end SequentialBoundedSublevels

end TauCeti
