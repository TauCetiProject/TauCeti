/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Extr
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Semicontinuity.Sequential

/-!
# Minimizing sequences, weak lower semicontinuity, and the sequential direct method

This file connects weak and sequential weak lower semicontinuity on normed spaces to minimizing
sequences and proves the sequential direct method in its literal minimizing-sequence form as well
as its sequential-sublevel form.

## Main results

* `TauCeti.exists_seq_mem_antitone_tendsto_csInf` and
  `TauCeti.exists_seq_mem_lt_csInf_add_one_div`: construction of minimizing sequences on any
  nonempty admissible set on which the energy is bounded below.
* `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_sublevel`,
  `TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_ereal_le_liminf`, and
  `TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact`:
  sublevel and `EReal`-`liminf` characterizations of weak and sequential weak lower
  semicontinuity, and their equivalence on weakly compact sets.
* `TauCeti.tendsto_subseq_toWeakSpace_isMinOn_of_bounded_minimizing_sequence` and
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`: the sequential direct method for a
  bounded minimizing sequence in a reflexive real or complex normed space, together with its
  sublevel-localized variant `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence_sublevel`.
* `TauCeti.exists_isMinOn_of_isSeqClosed` and
  `TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`: the sequential direct method and
  weak compactness of minimizers for energies taking values in any linear order, with no lower
  bound assumed.

## References

* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 1 and proof of Theorem 4.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Set Filter Bornology NormedSpace
open scoped Topology

namespace TauCeti

section MinimizingSequences

/-- On any nonempty set where an energy into a first-countable conditionally complete linear order
is bounded below, there exists an admissible sequence with antitone energies converging to the
infimum `sInf (E '' S)`. -/
theorem exists_seq_mem_antitone_tendsto_csInf {X β : Type*}
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    [FirstCountableTopology β] {E : X → β} {S : Set X}
    (hne : S.Nonempty) (hb : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ Antitone (E ∘ u) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  obtain ⟨y, hanti, htend, hy⟩ := exists_seq_tendsto_sInf (hne.image E) hb
  choose u hu hEu using hy
  exact ⟨u, hu, by simpa only [Function.comp_def, hEu] using hanti,
    by simpa only [hEu] using htend⟩

/-- On any nonempty set where a real-valued energy is bounded below, there exists a minimizing
sequence `u` in `S` satisfying the quantitative bound `E (u n) < sInf (E '' S) + 1 / (n + 1)`. -/
theorem exists_seq_mem_lt_csInf_add_one_div {X : Type*} {E : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hb : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  have hex (n : ℕ) : ∃ x ∈ S, E x < sInf (E '' S) + 1 / ((n : ℝ) + 1) := by
    have hlt : sInf (E '' S) < sInf (E '' S) + 1 / ((n : ℝ) + 1) :=
      lt_add_of_pos_right _ (by positivity)
    obtain ⟨_, ⟨x, hx, rfl⟩, hEx⟩ := exists_lt_of_csInf_lt (hne.image E) hlt
    exact ⟨x, hx, hEx⟩
  choose u hu hlt using hex
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hb (mem_image_of_mem E (hu n))) fun n ↦ (hlt n).le⟩
  simpa only [add_zero] using
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end MinimizingSequences

section WeakSemicontinuity

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Sequential weak closedness of `S` is equivalent to membership of weak limits of sequences in
`S`. -/
theorem isSeqClosed_toWeakSpace_iff {S : Set V} :
    IsSeqClosed (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S := by
  constructor
  · intro hS u v hu hlim
    exact (toWeakSpace 𝕜 V).injective.mem_set_image.mp
      (hS (fun n ↦ mem_image_of_mem _ (hu n)) hlim)
  · intro hS w y hw hlim
    choose u hu hwu using hw
    refine ⟨(toWeakSpace 𝕜 V).symm y, hS hu ?_, (toWeakSpace 𝕜 V).apply_symm_apply y⟩
    simpa only [hwu, LinearEquiv.apply_symm_apply] using hlim

/-- The weak-space image of a relative sublevel `{u ∈ S | E u ≤ b}` is the intersection of
`toWeakSpace 𝕜 V '' S` with the weak preimage of `Iic b`. -/
theorem image_toWeakSpace_sublevel {β : Type*} [Preorder β] {E : V → β} {S : Set V} (b : β) :
    toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b := by
  ext w
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage,
    mem_ofPred_eq, mem_inter_iff, mem_Iic]

/-- Weak lower semicontinuity of `E` on `S` is equivalent to weak closedness in `S` of every
relative sublevel `{u ∈ S | E u ≤ b}`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, ∃ C : Set (WeakSpace 𝕜 V), IsClosed C ∧
        toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} = (toWeakSpace 𝕜 V '' S) ∩ C := by
  simp_rw [lowerSemicontinuousOn_iff_preimage_Iic, image_toWeakSpace_sublevel]

/-- On a weakly closed set `S`, weak lower semicontinuity of `E` is equivalent to weak closedness
of every sublevel `{u ∈ S | E u ≤ b}`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_toWeakSpace_iff_sublevel]
  refine ⟨fun h b ↦ ?_, fun h b ↦ ⟨toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}, h b, ?_⟩⟩
  · obtain ⟨C, hC, heq⟩ := h b
    exact heq ▸ hS.inter hC
  · symm
    exact inter_eq_right.mpr (image_mono fun _ hx ↦ hx.1)

/-- On a sequentially weakly closed set `S`, sequential weak lower semicontinuity of `E` is
equivalent to sequential weak closedness of every sublevel `{u ∈ S | E u ≤ b}`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hS]
  refine forall_congr' fun b ↦ ?_
  rw [image_toWeakSpace_sublevel]
  rfl

/-- For a real-valued energy `E`, sequential weak lower semicontinuity on `S` is equivalent to
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` whenever `u n ∈ S` converges weakly to
`v ∈ S`, with the lower limit taken in `EReal` so that unbounded-above energy sequences are
included. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_ereal_le_liminf {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [seqLowerSemicontinuousOn_iff_ereal_le_liminf]
  constructor
  · intro h v hv u hu hlim
    simpa only [LinearEquiv.symm_apply_apply] using
      h (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hlim
  · rintro h _ ⟨v, hv, rfl⟩ w hw hlim
    choose u hu hwu using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [hwu] using hlim
    simpa only [← hwu, LinearEquiv.symm_apply_apply] using h v hv hu hlim'

/-- When a real-valued energy `E` is bounded below on `S`, sequential weak lower semicontinuity on
`S` is equivalent to the finite-limit inequality along weakly convergent sequences in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_of_tendsto_of_bddBelow
    {E : V → ℝ} {S : Set V} (hb : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ v ∈ S, ∀ ⦃u : ℕ → V⦄ ⦃r : ℝ⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r := by
  have hb' : BddBelow ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hb
  rw [seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow hb']
  constructor
  · intro h v hv u r hu hlim hEr
    simpa only [LinearEquiv.symm_apply_apply] using
      h (toWeakSpace 𝕜 V v) (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hlim
        (by simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEr)
  · rintro h _ ⟨v, hv, rfl⟩ w r hw hlim hEr
    choose u hu hwu using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [hwu] using hlim
    have hEr' : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) := by
      simpa only [Function.comp_def, ← hwu, LinearEquiv.symm_apply_apply] using hEr
    simpa only [LinearEquiv.symm_apply_apply] using h v hv hu hlim' hEr'

end WeakSemicontinuity

section SequentialDirectMethod

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- On a weakly compact subset `K` of a real or complex normed space, weak lower semicontinuity
and sequential weak lower semicontinuity agree. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact
    {β : Type*} [LinearOrder β] {E : V → β} {K : Set V}
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) ↔
      SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' K) := by
  have := sequentialSpace_toWeakSpace_of_isCompact hK
  exact lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn

/-- **Subsequential weak convergence of bounded minimizing sequences.** In a reflexive real or
complex normed space, any norm-bounded minimizing sequence in a sequentially weakly closed set `S`
for a bounded-below, sequentially weakly lower semicontinuous energy admits a subsequence
converging weakly to a minimizer of `E` on `S`. No completeness or separability assumption on `V`
is needed. -/
theorem tendsto_subseq_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) ∧
      IsMinOn E S v := by
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isBounded hreflexive hb
  have hvS : v ∈ S := hseqclosed (fun n ↦ hu (φ n)) hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hseqlsc hvS (fun n ↦ hu (φ n)) hlim (hminseq.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, φ, hφ, hlim, isMinOn_of_le_csInf hbelow hEv⟩

/-- **The sequential direct method.** In a reflexive real or complex normed space, an energy
bounded below on a sequentially weakly closed set `S` and sequentially weakly lower semicontinuous
along finite-energy limits attains its minimum on `S` as soon as one norm-bounded minimizing
sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hvS, -, -, -, hmin⟩ :=
    tendsto_subseq_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
      hreflexive hbelow hseqclosed hseqlsc hu hb hminseq
  exact ⟨v, hvS, hmin⟩

/-- Sublevel-localized sequential direct method: sequential weak closedness and sequential weak
lower semicontinuity need only hold on a single sublevel `{x ∈ S | E x ≤ b}` that eventually
contains the bounded minimizing sequence. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence_sublevel
    {β : Type*} [ConditionallyCompleteLattice β] [TopologicalSpace β]
    {E : V → β} {S : Set V} {b : β}
    (hreflexive : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      v ∈ S ∧ E v ≤ b)
    (hseqlsc : ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, v ∈ S → E v ≤ b →
      (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ᶠ n in atTop, E (u n) ≤ b)
    (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hub
  have hrange : IsBounded (range fun n ↦ u (n + N)) :=
    hb.subset (range_subset_iff.mpr fun n ↦ mem_range_self (n + N))
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isBounded hreflexive hrange
  have hsub (n : ℕ) : u (φ n + N) ∈ S ∧ E (u (φ n + N)) ≤ b :=
    ⟨hu (φ n + N), hN (φ n + N) (Nat.le_add_left N (φ n))⟩
  obtain ⟨hvS, hvb⟩ := hseqclosed hsub hlim
  have hEv : E v ≤ sInf (E '' S) :=
    hseqlsc hvS hvb hsub hlim ((tendsto_add_atTop_iff_nat N).mpr hminseq |>.comp hφ.tendsto_atTop)
  exact ⟨v, hvS, isMinOn_of_le_csInf hbelow hEv⟩

/-- On a sequentially weakly closed set in a reflexive real or complex normed space, every
norm-bounded sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
  isCompact_toWeakSpace_of_isBounded_of_isSeqClosed hV hb
    ((seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).mp hE b)

/-- A single nonempty norm-bounded, sequentially weakly closed sublevel on which the energy is
sequentially weakly lower semicontinuous suffices for existence of a global minimizer on `S`, with
no lower-bound assumption on `E`. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V} {b : β}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) :
    ∃ u ∈ S, IsMinOn E S u := by
  have hK := isCompact_toWeakSpace_of_isBounded_of_isSeqClosed hV hb hS
  have hlsc := (lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact hK).mpr
    hE
  obtain ⟨w, ⟨u, hu, rfl⟩, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hK hlsc
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).mp fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The sequential direct method from bounded sublevels.** In a reflexive real or complex normed
space, a sequentially weakly lower semicontinuous energy taking values in any linear order with
bounded sublevels on a nonempty sequentially weakly closed set attains its minimum, with no lower
bound assumed. -/
theorem exists_isMinOn_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_sublevel hV
    ((seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).mp hE (E v))
    (hE.mono (image_mono fun _ hx ↦ hx.1))
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the full set of minimizers of a sequentially weakly lower semicontinuous energy on a
sequentially weakly closed set in a reflexive space is norm bounded, then it is weakly compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
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
weakly closed set in a reflexive real or complex normed space, the set of minimizers is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    {β : Type*} [LinearOrder β] {E : V → β} {S : Set V}
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end SequentialDirectMethod

end TauCeti
