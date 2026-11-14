/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Variational.DirectMethod
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Semicontinuity.Sequential
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# The sequential direct method in the weak topology

In a real or complex seminormed space, every relatively weakly compact set is Fréchet–Urysohn in the
subspace weak topology (`TauCeti.frechetUrysohnSpace_toWeakSpace_of_isCompact_closure`), so
sequential weak lower semicontinuity and topological weak lower semicontinuity coincide on
relatively weakly compact sets — and, when the continuous bidual inclusion is surjective, on all
norm-bounded sets
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded`).

Consequently, the direct method holds under purely sequential weak hypotheses without assuming the
admissible set `S` is topologically weakly closed or the energy is bounded below:

* `TauCeti.isCompact_toWeakSpace_sublevel_of_isSeqClosed`: on a sequentially weakly closed set in a
  reflexive space, every norm-bounded sublevel of a sequentially weakly lower semicontinuous energy
  into a linear order is weakly compact.
* `TauCeti.exists_isMinOn_of_isSeqClosed`: a sequentially weakly lower semicontinuous energy with
  bounded sublevels on a nonempty sequentially weakly closed set attains its minimum, and its
  minimizer set is weakly compact (`TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`).
* `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: when `E '' S` is bounded below in a
  topological conditionally complete lattice and a norm-bounded minimizing sequence in `S` exists,
  every weak subsequential limit is an admissible minimizer; when the minimizer is unique, the
  entire minimizing sequence converges weakly to it
  (`TauCeti.tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence`).

Neither completeness of `V` nor point-separation of the seminorm is assumed.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 4.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.8, Theorem 2.8.14.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

section SemicontinuityEquivalence

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [Preorder β] {E : V → β} {K : Set V}

/-- On a relatively weakly compact set in a real or complex seminormed space, sequential weak lower
semicontinuity and topological weak lower semicontinuity coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (hK : IsCompact (closure (toWeakSpace 𝕜 V '' K))) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := frechetUrysohnSpace_toWeakSpace_of_isCompact_closure hK
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

/-- On a weakly compact set in a real or complex seminormed space, sequential weak lower
semicontinuity and topological weak lower semicontinuity coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure hK.closure

/-- In a reflexive seminormed space over `ℝ` or `ℂ`, sequential weak lower semicontinuity and
topological weak lower semicontinuity coincide on every norm-bounded set. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V)) (hK : IsBounded K) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) :=
  seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (isCompact_closure_toWeakSpace hV hK)

end SemicontinuityEquivalence

section LinearOrder

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}

private theorem isSeqClosed_toWeakSpace_sublevel
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) :
    IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq]
  exact heq ▸ hE.isSeqClosed_sublevel hS b

/-- On a sequentially weakly closed set in a reflexive space over `ℝ` or `ℂ`, a norm-bounded
sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded hV hb).2
      (isSeqClosed_toWeakSpace_sublevel hS hE b)
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb

/-- **Local sublevel sequential direct method.** If a single nonempty norm-bounded sublevel
`{u ∈ S | E u ≤ b}` is sequentially weakly closed and `E` is sequentially weakly lower
semicontinuous on that sublevel alone, then `E` attains its minimum on all of `S`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isBounded hV hb).2 hsub
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
    simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb
  have hEL : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact hcompact).1 hE
  obtain ⟨_, ⟨u, hu, rfl⟩, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hEL
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- A single nonempty norm-bounded sublevel suffices for the sequential direct method on a
sequentially weakly closed admissible set. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isSeqClosed_sublevel hV
    (isSeqClosed_toWeakSpace_sublevel hS hE b)
    (hE.mono (image_mono fun _ hx ↦ hx.1)) hne hb

/-- **Sequential direct method (sublevel form).** A sequentially weakly lower semicontinuous energy
with bounded sublevels on a nonempty sequentially weakly closed set in a reflexive space over `ℝ`
or `ℂ` attains its minimum. Neither topological weak closedness of `S` nor boundedness below of `E`
is assumed. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the set of minimizers of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive space is norm-bounded, then that set of minimizers is weakly
compact. -/
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

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive space, the set of minimizers is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end LinearOrder

section MinimizingSequence

variable {𝕜 V : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Subsequential convergence of bounded minimizing sequences.** In a reflexive seminormed space
over `ℝ` or `ℂ`, every norm-bounded minimizing sequence in a sequentially weakly closed set for a
sequentially weakly lower semicontinuous energy bounded below has a subsequence converging weakly to
an admissible minimizer. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v := by
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure
    (isCompact_closure_toWeakSpace hreflexive hb) mem_range_self
  have hvS : v ∈ S := hseqclosed (fun n ↦ hu (φ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hseqlsc hvS (fun n ↦ hu (φ n)) hlim (hminseq.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, φ, hφ, hlim, fun w hw ↦ hEv.trans (csInf_le hbelow (mem_image_of_mem E hw))⟩

/-- **The sequential direct method.** In a reflexive seminormed space over `ℝ` or `ℂ`, an energy
bounded below on a sequentially weakly closed set, sequentially weakly lower semicontinuous along
convergent energy sequences, attains its minimum on `S` as soon as one norm-bounded minimizing
sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, -, -, -, hmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  exact ⟨v, hvS, hmin⟩

/-- Bundled-predicate form of `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence` using
`IsSeqClosed` and `TauCeti.SeqLowerSemicontinuousOn`. -/
theorem SeqLowerSemicontinuousOn.exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v :=
  TauCeti.exists_isMinOn_of_bounded_minimizing_sequence hreflexive hbelow
    (isSeqClosed_toWeakSpace_iff.1 hS)
    (fun w v r hvS hw hlim hElim ↦ by
      simpa only [LinearEquiv.symm_apply_apply] using
        hE.le_of_tendsto (mem_image_of_mem _ hvS)
          (fun n ↦ mem_image_of_mem _ (hw n)) hlim
          (by simpa only [LinearEquiv.symm_apply_apply] using hElim))
    hu hb hminseq

/-- **Full-sequence weak convergence to a unique minimizer.** Under the hypotheses of the sequential
direct method, if at most one admissible point `v` can minimize `E` on `S` (`∀ w ∈ S, IsMinOn E S w
→ w = v`), then `v` is an admissible minimizer and the entire norm-bounded minimizing sequence
converges weakly to `v` without passing to a subsequence. -/
theorem tendsto_toWeakSpace_of_unique_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄, (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) → z ∈ S)
    (hseqlsc : ∀ ⦃w : ℕ → V⦄ ⦃z : V⦄ ⦃r : β⦄, z ∈ S → (∀ n, w n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (w n)) atTop (𝓝 (toWeakSpace 𝕜 V z)) →
      Tendsto (fun n ↦ E (w n)) atTop (𝓝 r) → E z ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))))
    {v : V} (huniq : ∀ w ∈ S, IsMinOn E S w → w = v) :
    v ∈ S ∧ IsMinOn E S v ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨v₀, hv₀S, -, -, -, hv₀min⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  obtain rfl := huniq v₀ hv₀S hv₀min
  refine ⟨hv₀S, hv₀min, tendsto_of_subseq_tendsto fun ns hns ↦ ?_⟩
  obtain ⟨ψ, -, hnsψ⟩ := strictMono_subseq_of_tendsto_atTop hns
  obtain ⟨w, hwS, σ, -, hlim, hwmin⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc (fun n ↦ hu (ns (ψ n)))
      (hb.subset (range_comp_subset_range _ _))
      (hminseq.comp hnsψ.tendsto_atTop)
  exact ⟨ψ ∘ σ, huniq w hwS hwmin ▸ hlim⟩

end MinimizingSequence

end TauCeti
