/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Topology.Semicontinuity.Sequential
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
import TauCeti.Order.Filter.Extr
import TauCeti.Topology.Semicontinuity.Basic

/-!
# The sequential direct method and weak sequential lower semicontinuity

In a real or complex normed space, weak lower semicontinuity on a weakly closed set is equivalent
to weak closedness of every relative sublevel, and sequential weak lower semicontinuity on a
sequentially weakly closed set is equivalent to sequential weak closedness of every relative
sublevel. On every relatively weakly compact subset (in particular on every weakly compact
subset), the sequential-closure form of Eberlein–Šmulian makes the induced weak topology
Fréchet–Urysohn, so sequential and topological weak lower semicontinuity coincide there.

In a reflexive normed space (where reflexivity is surjectivity of the continuous bidual
inclusion, without a separate completeness hypothesis):

* every norm-bounded sublevel of a sequentially weakly lower semicontinuous energy on a
  sequentially weakly closed set is weakly compact
  (`TauCeti.isCompact_toWeakSpace_sublevel_of_isSeqClosed`);
* an energy with a single nonempty bounded sublevel—in particular one with bounded sublevels on
  a nonempty admissible set—attains its minimum without assuming an a priori lower bound
  (`TauCeti.exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel`,
  `TauCeti.exists_isMinOn_of_isSeqClosed`), and its set of minimizers is weakly compact
  (`TauCeti.isCompact_toWeakSpace_minimizers_of_isSeqClosed`);
* a bounded minimizing sequence for an energy bounded below on a sequentially weakly closed set
  has a weakly convergent subsequence whose limit minimizes the energy
  (`TauCeti.exists_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence`,
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`), and the same holds when sequential
  closedness and lower semicontinuity are assumed only on one sublevel containing the sequence.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 1 and proof of Theorem 4.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

/-! ### Weak sequential closedness and weak lower semicontinuity -/

section WeakSemicontinuity

variable {𝕜 V β : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜]
  [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V] {E : V → β} {S : Set V}

/-- Sequential weak closedness of `toWeakSpace 𝕜 V '' S` stated directly in terms of weakly
convergent sequences in `V`. -/
theorem isSeqClosed_toWeakSpace_iff :
    IsSeqClosed (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        v ∈ S := by
  constructor
  · intro hS u v hu hlim
    exact (toWeakSpace 𝕜 V).injective.mem_set_image.1
      (hS (fun n ↦ mem_image_of_mem _ (hu n)) hlim)
  · intro h w z hw hlim
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] at hw ⊢
    exact h hw (by simpa only [LinearEquiv.apply_symm_apply] using hlim)

/-- Sequential weak lower semicontinuity of `E` on `S` stated directly in terms of weakly
convergent sequences in `V`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff [LT β] :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ y < E v, ∀ᶠ n in atTop, y < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  constructor
  · intro hE u v hu hv hlim y hy
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim y (by simpa using hy)
  · intro h w z hw hz hlim y hy
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] at hw hz
    exact h hw hz (by simpa only [LinearEquiv.apply_symm_apply] using hlim) y hy

/-- On a weakly closed set, weak lower semicontinuity into a linear order is equivalent to weak
closedness of every relative sublevel. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel [LinearOrder β]
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_iff_isClosed_sublevel hS]
  refine forall_congr' fun b ↦ ?_
  have heq : {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} =
      toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} := by
    ext w
    simp [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  rw [heq]

/-- On a sequentially weakly closed set, sequential weak lower semicontinuity into a linear order
is equivalent to sequential weak closedness of every relative sublevel. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel [LinearOrder β]
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hS]
  refine forall_congr' fun b ↦ ?_
  have heq : {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} =
      toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} := by
    ext w
    simp [(toWeakSpace 𝕜 V).image_eq_preimage_symm]
  rw [heq]

/-- Sequential weak lower semicontinuity of a real-valued energy on `S` is equivalent to the
`EReal` `liminf` inequality along every weakly convergent sequence in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_coe_le_liminf_ereal {E : V → ℝ} :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [seqLowerSemicontinuousOn_iff_coe_le_liminf_ereal]
  constructor
  · intro hE u v hu hv hlim
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
  · intro h w z hw hz hlim
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] at hw hz
    exact h hw hz (by simpa only [LinearEquiv.apply_symm_apply] using hlim)

/-- When `E '' S` is bounded below in a first-countable order topology with compact closed
intervals (such as `ℝ`), sequential weak lower semicontinuity on `S` is equivalent to the
limit-inequality condition along weakly convergent sequences whose energies converge. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_of_tendsto_of_bddBelow
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] [CompactIccSpace β]
    [FirstCountableTopology β] (hbelow : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r := by
  have hbelow' : BddBelow ((fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hbelow
  rw [seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow hbelow']
  constructor
  · intro hE u v r hu hv hlim hEr
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
        (by simpa [Function.comp_def] using hEr)
  · intro h w z r hw hz hlim hEr
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] at hw hz
    exact h hw hz (by simpa only [LinearEquiv.apply_symm_apply] using hlim) hEr

end WeakSemicontinuity

/-! ### Equivalence of sequential and topological weak lower semicontinuity on compact sets -/

section EberleinBridge

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [LinearOrder β] {E : V → β} {K : Set V}

/-- On a relatively weakly compact subset of a real or complex normed space, sequential and
topological weak lower semicontinuity into a linear order coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (hK : IsCompact (closure (toWeakSpace 𝕜 V '' K))) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := frechetUrysohnSpace_weakSpace_of_isCompact_closure hK
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

/-- On a weakly compact subset of a real or complex normed space, sequential and topological
weak lower semicontinuity into a linear order coincide. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := frechetUrysohnSpace_weakSpace_of_isCompact hK
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

end EberleinBridge

/-! ### Sequential direct method via bounded sublevels -/

section SublevelDirectMethod

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive normed space, a norm-bounded sublevel of
a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
  isCompact_weakSpace_of_isSeqClosed_of_isCompact_closure
    (isCompact_closure_toWeakSpace_of_isBounded hV hb)
    ((seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b)

/-- Local-sublevel sequential direct method: if one nonempty sublevel `{u ∈ S | E u ≤ b}` is
norm-bounded and sequentially weakly closed and `E` is sequentially weakly lower semicontinuous
on that sublevel, then `E` attains its minimum on `S`. No lower bound on `E` is assumed. -/
theorem exists_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hb : IsBounded {u ∈ S | E u ≤ b})
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :
    ∃ u ∈ S, IsMinOn E S u := by
  have hcompact : IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    isCompact_weakSpace_of_isSeqClosed_of_isCompact_closure
      (isCompact_closure_toWeakSpace_of_isBounded hV hb) hsub
  have hlsc : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact hcompact).1 hE
  obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hlsc
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- A single nonempty norm-bounded sublevel suffices for the sequential direct method on a
sequentially weakly closed admissible set in a reflexive normed space. -/
theorem exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u :=
  exists_isMinOn_of_isSeqClosed_sublevel hV hne
    ((seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b) hb
    (hE.mono (image_mono fun _ hx ↦ hx.1))

/-- **The sequential direct method with bounded sublevels.** A sequentially weakly lower
semicontinuous energy with bounded sublevels on a nonempty sequentially weakly closed set in a
reflexive normed space attains its minimum, with no a priori lower bound. -/
theorem exists_isMinOn_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the minimizer set of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive normed space is norm-bounded, then it is weakly compact. -/
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

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a
sequentially weakly closed set in a reflexive normed space, the set of minimizers is weakly
compact. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end SublevelDirectMethod

/-! ### Minimizing sequences and the sequential direct method -/

section MinimizingSequences

/-- A real-valued energy bounded below on a nonempty admissible set admits a minimizing sequence
`u n ∈ S` satisfying `E (u n) < sInf (E '' S) + 1 / (n + 1)`. -/
theorem exists_minimizing_seq {X : Type*} {E : X → ℝ} {S : Set X}
    (hne : S.Nonempty) (hbelow : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  have hex (n : ℕ) : ∃ x ∈ S, E x < sInf (E '' S) + 1 / ((n : ℝ) + 1) := by
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ :=
      Real.lt_sInf_add_pos (hne.image E) (one_div_pos.2 (Nat.cast_add_one_pos n))
    exact ⟨x, hx, hlt⟩
  choose u hu hlt using hex
  refine ⟨u, hu, hlt, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ csInf_le hbelow (mem_image_of_mem E (hu n))) (fun n ↦ (hlt n).le)⟩
  simpa only [add_zero] using
    (tendsto_const_nhds (x := sInf (E '' S))).add tendsto_one_div_add_atTop_nhds_zero_nat

/-- A real-valued energy bounded below with bounded sublevels on a nonempty admissible set admits
a bounded minimizing sequence `u n ∈ S` with `E (u n) < sInf (E '' S) + 1 / (n + 1)`. -/
theorem HasBoundedSublevelsOn.exists_isBounded_minimizing_seq {X : Type*} [Bornology X]
    {E : X → ℝ} {S : Set X} (hb : HasBoundedSublevelsOn E S)
    (hne : S.Nonempty) (hbelow : BddBelow (E '' S)) :
    ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧ IsBounded (range u) ∧
      (∀ n, E (u n) < sInf (E '' S) + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S))) := by
  obtain ⟨u, hu, hlt, hlim⟩ := exists_minimizing_seq hne hbelow
  refine ⟨u, hu, hb.isBounded_range hu ⟨sInf (E '' S) + 1, ?_⟩, hlt, hlim⟩
  rintro _ ⟨n, rfl⟩
  have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
    div_le_one_of_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n)) (Nat.cast_add_one_pos n).le
  exact (hlt n).le.trans (add_le_add_right h1 _)

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
  {E : V → β} {S : Set V}

/-- Every norm-bounded minimizing sequence for a sequentially weakly lower semicontinuous energy
bounded below on a sequentially weakly closed set in a reflexive normed space has a weakly
convergent subsequence whose limit minimizes the energy. -/
theorem exists_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  have hcomp : IsCompact (closure (toWeakSpace 𝕜 V '' range u)) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  obtain ⟨v, σ, hσ, hlim⟩ :=
    tendsto_subseq_toWeakSpace_of_isCompact_closure hcomp (fun n ↦ mem_range_self n)
  have hv : v ∈ S := (isSeqClosed_toWeakSpace_iff.1 hS) (fun n ↦ hu (σ n)) hlim
  have hbelow' : BddBelow ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hbelow
  have hsInf : sInf ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) = sInf (E '' S) := by
    simp only [image_image, LinearEquiv.symm_apply_apply]
  have hmin' : IsMinOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) (toWeakSpace 𝕜 V v) :=
    hE.isMinOn_of_tendsto_sInf hbelow' (fun n ↦ mem_image_of_mem _ (hu (σ n)))
      (mem_image_of_mem _ hv) hlim (by
        simpa only [Function.comp_def, LinearEquiv.symm_apply_apply, hsInf] using
          hmin.comp hσ.tendsto_atTop)
  refine ⟨v, hv, fun x hx ↦ ?_, σ, hσ, hlim⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin' (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The sequential direct method.** In a reflexive normed space, an energy bounded below on a
sequentially weakly closed set and sequentially weakly lower semicontinuous there attains its
minimum as soon as one norm-bounded minimizing sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hv, hminv, _⟩ :=
    exists_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence hV hbelow hS hE hu hb hmin
  exact ⟨v, hv, hminv⟩

/-- Local-sublevel version of subsequential weak convergence for bounded minimizing sequences:
sequential weak closedness and sequential weak lower semicontinuity are assumed only on a single
sublevel containing the sequence. -/
theorem exists_tendsto_toWeakSpace_isMinOn_of_isSeqClosed_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S)) {b : β}
    (hsub : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S) (hub : ∀ n, E (u n) ≤ b) (hb : IsBounded (range u))
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  set S' : Set V := {x ∈ S | E x ≤ b}
  have hbelow' : BddBelow (E '' S') := hbelow.mono (image_mono fun _ hx ↦ hx.1)
  have hu' : ∀ n, u n ∈ S' := fun n ↦ ⟨hu n, hub n⟩
  have hsInf_eq : sInf (E '' S') = sInf (E '' S) := by
    apply le_antisymm
    · exact ge_of_tendsto' hmin fun n ↦ csInf_le hbelow' (mem_image_of_mem E (hu' n))
    · exact csInf_le_csInf hbelow ⟨E (u 0), mem_image_of_mem E (hu' 0)⟩
        (image_mono fun _ hx ↦ hx.1)
  obtain ⟨v, hv, hminv, σ, hσ, hlim⟩ :=
    exists_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence hV hbelow' hsub hE hu' hb
      (hsInf_eq.symm ▸ hmin)
  exact ⟨v, hv.1, (isMinOn_sublevel_iff hv.2).1 hminv, σ, hσ, hlim⟩

/-- Every minimizing sequence of a sequentially weakly lower semicontinuous energy with bounded
sublevels on a sequentially weakly closed set in a reflexive normed space has a weakly convergent
subsequence whose limit minimizes the energy. -/
theorem exists_tendsto_toWeakSpace_isMinOn_of_hasBoundedSublevelsOn
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hmin : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (σ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) :=
  exists_tendsto_toWeakSpace_isMinOn_of_bounded_minimizing_sequence hV hbelow hS hE hu
    (hb.isBounded_range hu hmin.bddAbove_range) hmin

end MinimizingSequences

end TauCeti
