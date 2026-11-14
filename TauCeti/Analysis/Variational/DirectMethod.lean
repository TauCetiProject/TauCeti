/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Extr
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Variational.Semicontinuous
public import TauCeti.Analysis.Normed.Module.DoubleDual

/-!
# The direct method in the weak topology

This file proves both the topological and sequential versions of the direct method of the calculus
of variations on reflexive seminormed spaces, where reflexivity is surjectivity of the continuous
bidual inclusion `NormedSpace.inclusionInDoubleDual 𝕜 V` and completeness is not assumed separately.

* **Topological direct method** (`TauCeti.exists_isMinOn_of_weak_closed`, over any proper
  nontrivially normed field): a weakly lower semicontinuous energy taking values in a linear order
  on a nonempty weakly closed admissible set attains its minimum if its sublevels are norm bounded.
  No lower bound on the energy is assumed: compactness of one nonempty sublevel provides it. Every
  bounded sublevel and any bounded set of minimizers are weakly compact.
* **Sequential direct method** (`TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`, over real
  or complex scalars): a sequentially weakly lower semicontinuous energy bounded below on a
  sequentially weakly closed admissible set attains its minimum `sInf (E '' S)` whenever a single
  norm-bounded minimizing sequence exists, and every bounded near-minimizing sequence admits a
  subsequence converging weakly to a minimizer
  (`TauCeti.exists_subseq_tendsto_toWeakSpace_isMinOn_of_tendsto_sInf`). More generally, sequential
  weak closedness and sequential weak lower semicontinuity on a single nonempty norm-bounded
  sublevel already yield a minimizer on `S` without a lower bound on `E`
  (`TauCeti.exists_isMinOn_of_isSeqClosed_sublevel`), via the sequential-closure form of
  Eberlein–Šmulian.

Both versions remain stable under restriction to a nonempty weakly (respectively sequentially
weakly) closed subset, and identify the attained minimum value with `sInf (E '' S)` in conditionally
complete linear orders.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 1 and proof of Theorem 4.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

section Topological

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

section LinearOrder

variable {β : Type*} [LinearOrder β] {E : V → β} {S T : Set V}

/-- On a weakly closed set in a reflexive space, a bounded sublevel of a weakly lower
semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hclosed := hS.lowerSemicontinuousOn_toWeakSpace_iff.mp hE b
  simpa only [hclosed.closure_eq] using isCompact_closure_toWeakSpace hV hb

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
    image_mono (sep_subset S fun u ↦ E u ≤ b)
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

/-- Restriction of the topological direct method to a nonempty weakly closed subset `T ⊆ S`. -/
theorem exists_isMinOn_of_weak_closed_subset
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hTS : T ⊆ S) (hne : T.Nonempty) (hT : IsClosed (toWeakSpace 𝕜 V '' T))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ T, IsMinOn E T u :=
  exists_isMinOn_of_weak_closed hV hne hT (hE.mono (image_mono hTS)) (hb.mono hTS)

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

end LinearOrder

/-- In a conditionally complete linear order, the minimum attained by the topological direct method
agrees with `sInf (E '' S)`. -/
theorem exists_eq_csInf_of_weak_closed {β : Type*} [ConditionallyCompleteLinearOrder β]
    {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsClosed (toWeakSpace 𝕜 V '' S))
    (hE : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    ∃ u ∈ S, IsMinOn E S u ∧ E u = sInf (E '' S) := by
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_of_weak_closed hV hne hS hE hb
  exact ⟨u, hu, hmin, (hmin.csInf_image_eq hu).symm⟩

end Topological

section Sequential

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

section LinearOrder

variable {β : Type*} [LinearOrder β] {E : V → β} {S T : Set V}

/-- Sequential weak closedness and sequential weak lower semicontinuity on a single nonempty
norm-bounded sublevel `{u ∈ S | E u ≤ b}` suffice to attain the minimum of `E` on the entire
admissible set `S`, without assuming a lower bound on `E`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b})
    (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :
    ∃ u ∈ S, IsMinOn E S u := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hcl := isCompact_closure_toWeakSpace hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed hcl).mpr hsub
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    hclosed.closure_eq ▸ hcl
  have hlsc := (seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    hcompact).mp hE
  obtain ⟨_, ⟨u, hu, rfl⟩, hmin⟩ := hlsc.exists_isMinOn (hne.image _) hcompact
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).mp fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- On a sequentially weakly closed set in a reflexive real or complex seminormed space, every
norm-bounded sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hcl := isCompact_closure_toWeakSpace hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed hcl).mpr
      (hS.seqLowerSemicontinuousOn_toWeakSpace_iff.mp hE b)
  simpa only [hclosed.closure_eq] using hcl

/-- A single nonempty norm-bounded sublevel suffices for the sequential direct method on a
sequentially weakly closed admissible set. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isSeqClosed_sublevel hV hne hb
    (hS.seqLowerSemicontinuousOn_toWeakSpace_iff.mp hE b)
    (hE.mono (image_mono (sep_subset S fun u ↦ E u ≤ b)))

/-- On a nonempty sequentially weakly closed set in a reflexive real or complex seminormed space, a
sequentially weakly lower semicontinuous energy with bounded sublevels attains its minimum. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- Restriction of the sequential direct method to a nonempty sequentially weakly closed subset
`T ⊆ S`. -/
theorem exists_isMinOn_of_isSeqClosed_subset
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hTS : T ⊆ S) (hne : T.Nonempty) (hT : IsSeqClosed (toWeakSpace 𝕜 V '' T))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ T, IsMinOn E T u :=
  exists_isMinOn_of_isSeqClosed hV hne hT (hE.mono (image_mono hTS)) (hb.mono hTS)

/-- If the full set of minimizers of a sequentially weakly lower semicontinuous energy on a
sequentially weakly closed set in a reflexive real or complex seminormed space is norm bounded,
then that set of minimizers is weakly compact. -/
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
weakly closed set in a reflexive real or complex seminormed space, the set of minimizers is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end LinearOrder

section MinimizingSequence

variable {β : Type*} [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [ClosedIciTopology β] {E : V → β} {S : Set V}

/-- **Subsequential weak convergence of bounded near-minimizers.** In a reflexive real or complex
seminormed space, if `E` is bounded below and sequentially weakly lower semicontinuous on a
sequentially weakly closed set `S`, then every norm-bounded sequence `u` in `S` whose energies
converge to `sInf (E '' S)` admits a subsequence converging weakly to a minimizer `v ∈ S` with
`E v = sInf (E '' S)`. -/
theorem exists_subseq_tendsto_toWeakSpace_isMinOn_of_tendsto_sInf
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have hcompact := isCompact_closure_toWeakSpace hV hb
  obtain ⟨v, σ, hσ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hcompact (fun n ↦ mem_range_self n)
  have hvS : v ∈ S := isSeqClosed_image_toWeakSpace_iff.mp hS (fun n ↦ hu (σ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hE.le_of_tendsto_toWeakSpace (fun n ↦ hu (σ n)) hvS hlim (hmin.comp hσ.tendsto_atTop)
  have hminOn : IsMinOn E S v := fun x hx ↦ hEv.trans (csInf_le hbelow (mem_image_of_mem E hx))
  exact ⟨v, hvS, hminOn, (hminOn.csInf_image_eq hvS).symm, σ, hσ, hlim⟩

/-- **The sequential direct method.** In a reflexive real or complex seminormed space, an energy
bounded below and sequentially weakly lower semicontinuous on a sequentially weakly closed set `S`
attains its minimum on `S` as soon as a norm-bounded minimizing sequence exists in `S`. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, hminOn, -⟩ :=
    exists_subseq_tendsto_toWeakSpace_isMinOn_of_tendsto_sInf hV hbelow hS hE hu hb hmin
  exact ⟨v, hvS, hminOn⟩

end MinimizingSequence

end Sequential

end TauCeti
