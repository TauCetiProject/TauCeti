/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Variational.WeakLowerSemicontinuous
public import TauCeti.Order.Filter.Extr

/-!
# The direct method in the weak topology

This file establishes both the topological and the sequential formulations of the direct method
of the calculus of variations in reflexive spaces, where reflexivity is expressed by
surjectivity of `NormedSpace.inclusionInDoubleDual 𝕜 V` without assuming completeness or
separability.

* **Topological direct method** (`exists_isMinOn_of_weak_closed`,
  `isCompact_toWeakSpace_minimizers`): over any proper nontrivially normed field `𝕜` and
  seminormed space `V`, a weakly lower semicontinuous energy into a linear order on a nonempty
  weakly closed set with norm-bounded sublevels attains its minimum, and both its sublevels and
  its full set of minimizers are weakly compact.
* **Minimizing sequences** (`exists_seq_mem_lt_csInf_add_one_div`,
  `exists_antitone_minimizing_seq`, `HasBoundedSublevelsOn.isBounded_range_of_tendsto`):
  existence of admissible sequences approaching `sInf (E '' S)` (with quantitative `1 / (n + 1)`
  error for real energies, or monotonically decreasing energies in first-countable conditionally
  complete linear order topologies), and boundedness of their ranges under bounded sublevels.
* **Sequential direct method** (`exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence`,
  `exists_isMinOn_of_bounded_minimizing_sequence`, `tendsto_toWeakSpace_of_unique_isMinOn`,
  `exists_isMinOn_of_isSeqClosed`, `isCompact_toWeakSpace_minimizers_of_isSeqClosed`): over a
  real or complex normed space `V` with surjective canonical bidual map, every norm-bounded
  minimizing sequence in a weakly sequentially closed set for a weakly sequentially lower
  semicontinuous energy admits a subsequence converging weakly to a minimizer realizing
  `sInf (E '' S)` (with full weak convergence when the minimizer is unique). Combining weak
  sequential hypotheses with the Kaplansky–Šmulian theorem upgrades bounded sublevels directly
  to weak compactness for energies into any linear order without assuming `BddBelow`.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, proof of Theorem 4.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  §3.5, Corollary 3.23 and Remark 6.
* B. Dacorogna, *Direct Methods in the Calculus of Variations*, 2nd ed., Theorem 3.6.
-/

public section

open Set Bornology Filter NormedSpace Topology

namespace TauCeti

section TopologicalDirectMethod

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a weakly closed set in a reflexive space, a bounded sublevel of a weakly lower
semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel hS).1 hE b
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace_of_isBounded hV hb

/-- A single nonempty bounded sublevel suffices for the direct method on a weakly
closed admissible set. -/
theorem exists_isMinOn_of_weak_closed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel hV hS hE b hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono (sep_subset S _)
  obtain ⟨w, hw, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact (hE.mono hsubset)
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The direct method.** A weakly lower semicontinuous energy with bounded sublevels on
a nonempty weakly closed set in a reflexive space attains its minimum. -/
theorem exists_isMinOn_of_weak_closed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_weak_closed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a weakly lower semicontinuous energy on a weakly
closed set in a reflexive space is bounded, then that set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel hV hS hE (E u) hb

/-- For a weakly lower semicontinuous energy with bounded sublevels on a weakly closed set
in a reflexive space, the set of minimizers is weakly compact, including when the admissible
set is empty. -/
theorem isCompact_toWeakSpace_minimizers
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isBounded hV hS hE hb.isBounded_minimizers

end TopologicalDirectMethod

section MinimizingSequences

/-- For any real-valued energy bounded below on a nonempty set `S`, there exists a minimizing
sequence `u` in `S` satisfying `E (u n) < sInf (E '' S) + 1 / (n + 1)` and
`E (u n) → sInf (E '' S)`. -/
theorem exists_seq_mem_lt_csInf_add_one_div {X : Type*} {E : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hbdd : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S))) := by
  have hex (n : ℕ) : ∃ x ∈ S, E x < sInf (E '' S) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image E)
      (lt_add_of_pos_right _ (one_div_pos.2 (Nat.cast_add_one_pos n)))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbdd (mem_image_of_mem E (hu n))) (fun n ↦ (hlt n).le)⟩
  simpa only [add_zero] using
    (tendsto_const_nhds (x := sInf (E '' S))).add tendsto_one_div_add_atTop_nhds_zero_nat

/-- In a first-countable conditionally complete linear order topology, any energy bounded below
on a nonempty set `S` admits an admissible minimizing sequence with antitone energy values
converging to `sInf (E '' S)`. -/
theorem exists_antitone_minimizing_seq {X β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {E : X → β} {S : Set X}
    (hne : S.Nonempty) (hbdd : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ Antitone (E ∘ u) ∧
      Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S))) := by
  obtain ⟨y, hanti, hlim, hmem⟩ := exists_seq_tendsto_sInf (hne.image E) hbdd
  choose u hu hEu using hmem
  have hcomp : E ∘ u = y := funext hEu
  exact ⟨u, hu, hcomp ▸ hanti, hcomp ▸ hlim⟩

/-- Under `HasBoundedSublevelsOn E S`, any admissible sequence whose energies converge in a
linear order topology has bounded range. -/
theorem HasBoundedSublevelsOn.isBounded_range_of_tendsto {X β : Type*} [Bornology X]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] {E : X → β} {S : Set X}
    (h : HasBoundedSublevelsOn E S) {u : ℕ → X} {b : β}
    (hu : ∀ n, u n ∈ S) (hEu : Tendsto (E ∘ u) atTop (𝓝 b)) :
    IsBounded (range u) :=
  h.isBounded_range hu hEu.bddAbove_range

end MinimizingSequences

section SequentialDirectMethod

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

section MinimizingSequenceConvergence

variable {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
  {E : V → β} {S : Set V}

/-- **Sequential direct method (subsequential convergence).** In a reflexive normed space, any
norm-bounded minimizing sequence in a weakly sequentially closed set `S` for a weakly
sequentially lower semicontinuous energy `E` bounded below on `S` admits a subsequence
converging weakly to an admissible minimizer `v ∈ S` with `E v = sInf (E '' S)`. -/
theorem exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hu_bdd : IsBounded (range u))
    (hu_min : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v ∧ E v = sInf (E '' S) := by
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace_of_isBounded hV hu_bdd) (fun n ↦ mem_range_self n)
  have hv : v ∈ S := isSeqClosed_toWeakSpace_iff.1 hS (fun n ↦ hu (φ n)) hlim
  have hle : E v ≤ sInf (E '' S) := hE.le_of_tendsto_toWeakSpace hv (fun n ↦ hu (φ n)) hlim
    (hu_min.comp hφ.tendsto_atTop)
  have hmin : IsMinOn E S v := (isMinOn_iff_le_csInf_image ⟨u 0, hu 0⟩ hbdd).2 hle
  exact ⟨v, hv, φ, hφ, hlim, hmin, (hmin.csInf_image_eq hv).symm⟩

/-- **Sequential direct method.** If `E` is bounded below and weakly sequentially lower
semicontinuous on a weakly sequentially closed set `S` in a reflexive normed space, and `u` is
a norm-bounded minimizing sequence in `S`, then `E` attains its minimum on `S` and the minimum
value equals `sInf (E '' S)`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hu_bdd : IsBounded (range u))
    (hu_min : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) := by
  obtain ⟨v, hv, -, -, -, hmin, hEq⟩ :=
    exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence hV hbdd hS hE hu hu_bdd hu_min
  exact ⟨v, hv, hmin, hEq⟩

/-- If every minimizer of `E` on `S` equals `v` (in particular, if `v ∈ S` is the unique
minimizer), then under the hypotheses of the sequential direct method every norm-bounded
minimizing sequence in `S` converges weakly to `v` without passing to a subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hu_bdd : IsBounded (range u))
    (hu_min : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  rw [(nhds_basis_opens _).tendsto_right_iff]
  by_contra! hnot
  obtain ⟨U, ⟨hvU, hUopen⟩, hfreq⟩ := hnot
  obtain ⟨ψ, hψ, hnotU⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨w, hw, φ, -, hlim, hmin_w, -⟩ :=
    exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence hV hbdd hS hE
      (fun n ↦ hu (ψ n)) (hu_bdd.subset (range_comp_subset_range ψ u))
      (hu_min.comp hψ.tendsto_atTop)
  rw [huniq w hw hmin_w] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (hUopen.mem_nhds hvU)).exists
  exact hnotU (φ n) hn

/-- **Sublevel-localized sequential direct method.** Weak sequential closedness and weak
sequential lower semicontinuity need only hold on a single sublevel `{x ∈ S | E x ≤ b}`
containing the norm-bounded minimizing sequence. -/
theorem exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S)) {b : β}
    (hSb : IsSeqClosed (toWeakSpace 𝕜 V '' {x ∈ S | E x ≤ b}))
    (hEb : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' {x ∈ S | E x ≤ b}))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ n, E (u n) ≤ b) (hu_bdd : IsBounded (range u))
    (hu_min : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v ∧ E v = sInf (E '' S) := by
  set Sb : Set V := {x ∈ S | E x ≤ b}
  have huSb (n : ℕ) : u n ∈ Sb := ⟨hu n, hub n⟩
  have hbdd_Sb : BddBelow (E '' Sb) := hbdd.mono (image_mono (sep_subset S _))
  have hsInf_eq : sInf (E '' Sb) = sInf (E '' S) := by
    refine le_antisymm ?_ (csInf_le_csInf hbdd ⟨E (u 0), mem_image_of_mem E (huSb 0)⟩
      (image_mono (sep_subset S _)))
    exact ge_of_tendsto' hu_min fun n ↦ csInf_le hbdd_Sb (mem_image_of_mem E (huSb n))
  obtain ⟨v, ⟨hvS, hvb⟩, φ, hφ, hlim, hmin_Sb, hEq⟩ :=
    exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence hV hbdd_Sb hSb hEb huSb hu_bdd
      (hsInf_eq.symm ▸ hu_min)
  exact ⟨v, hvS, φ, hφ, hlim, (isMinOn_sublevel_iff hvb).1 hmin_Sb, hEq.trans hsInf_eq⟩

/-- Sublevel-localized existence corollary for a norm-bounded minimizing sequence. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbdd : BddBelow (E '' S)) {b : β}
    (hSb : IsSeqClosed (toWeakSpace 𝕜 V '' {x ∈ S | E x ≤ b}))
    (hEb : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' {x ∈ S | E x ≤ b}))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ n, E (u n) ≤ b) (hu_bdd : IsBounded (range u))
    (hu_min : Tendsto (E ∘ u) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) := by
  obtain ⟨v, hv, -, -, -, hmin, hEq⟩ :=
    exists_tendsto_subseq_isMinOn_of_bounded_minimizing_sequence_sublevel hV hbdd hSb hEb
      hu hub hu_bdd hu_min
  exact ⟨v, hv, hmin, hEq⟩

end MinimizingSequenceConvergence

section SequentialBoundedSublevels

variable {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

/-- On a weakly sequentially closed set in a reflexive real or complex normed space, a bounded
sublevel of a weakly sequentially lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hcompact_cl := isCompact_closure_toWeakSpace_of_isBounded hV hb
  have hseq : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isCompact_closure hcompact_cl).2 hseq
  simpa only [hclosed.closure_eq] using hcompact_cl

/-- A single nonempty bounded sublevel suffices for the sequential direct method on a weakly
sequentially closed admissible set, into any linear order and without assuming `BddBelow`. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE b hb
  have hsubset : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} ⊆ toWeakSpace 𝕜 V '' S :=
    image_mono (sep_subset S _)
  have hlsc : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact hcompact).2
      (hE.mono hsubset)
  obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hlsc
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **Sequential direct method under bounded sublevels.** A weakly sequentially lower
semicontinuous energy with bounded sublevels on a nonempty weakly sequentially closed set in a
reflexive real or complex normed space attains its minimum. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a weakly sequentially lower semicontinuous energy on a
weakly sequentially closed set in a reflexive normed space is bounded, then that set of
minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : IsBounded {u ∈ S | IsMinOn E S u}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) := by
  obtain hempty | ⟨u, hu, hmin⟩ := {u ∈ S | IsMinOn E S u}.eq_empty_or_nonempty
  · simp [hempty]
  · rw [hmin.minimizers_eq_sublevel hu] at hb ⊢
    exact isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE (E u) hb

/-- For a weakly sequentially lower semicontinuous energy with bounded sublevels on a weakly
sequentially closed set in a reflexive normed space, the set of minimizers is weakly compact,
including when the admissible set is empty. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end SequentialBoundedSublevels

end SequentialDirectMethod

end TauCeti
