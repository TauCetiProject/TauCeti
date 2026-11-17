/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Analysis.Variational.BoundedSublevels
public import TauCeti.Order.Filter.Extr
public import TauCeti.Topology.Semicontinuity.Sequential
import Mathlib.Topology.Order.LiminfLimsup
import TauCeti.Topology.Semicontinuity.Basic

/-!
# The sequential direct method in the weak topology

This file develops sequential weak lower semicontinuity and the sequential direct method of the
calculus of variations in reflexive normed spaces over `ℝ` or `ℂ`, without completeness or
separability assumptions.

For a real or complex normed space `V`, Eberlein–Šmulian makes every relatively weakly compact set
a Fréchet–Urysohn space in the weak topology, so topological and sequential weak lower
semicontinuity agree on every relatively weakly compact subset
(`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure`).

Two forms of the sequential direct method are proved for spaces with surjective canonical bidual
map `NormedSpace.inclusionInDoubleDual 𝕜 V`:

* From a single norm-bounded minimizing sequence of a bounded-below energy on a sequentially weakly
  closed set, weak sequential compactness extracts a subsequence converging weakly to a minimizer
  attaining `sInf (E '' S)` (`TauCeti.exists_subseq_tendsto_isMinOn_of_bounded_minimizing_sequence`,
  `TauCeti.exists_isMinOn_of_bounded_minimizing_sequence`), together with a variant localized to a
  single bounded sublevel (`TauCeti.exists_subseq_tendsto_isMinOn_of_minimizing_sequence_sublevel`).
* From sequential weak closedness, sequential weak lower semicontinuity, and bounded sublevels (or
  a single nonempty bounded sublevel), every bounded sublevel is genuinely weakly compact via the
  sequential-closure form of Eberlein–Šmulian, so the energy attains its minimum with no lower
  bound assumed and for any linearly ordered codomain
  (`TauCeti.exists_isMinOn_of_isSeqClosed_toWeakSpace`). The full set of minimizers is weakly
  compact, and every near-minimizing sequence has a subsequence converging weakly to a minimizer.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2 (the direct method).
* V. Ivrii, *Partial Differential Equations*, §13.1, Theorem 1 and proof of Theorem 4.
-/

public section

open Bornology Filter NormedSpace Set Topology

namespace TauCeti

/-! ### Weak sublevels and sequential weak lower semicontinuity -/

section WeakSublevels

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]
  {β : Type*} {E : V → β} {S : Set V}

/-- The image of a relative sublevel set under `toWeakSpace` is the intersection of the weak image
of `S` with the preimage of `Iic b`. -/
theorem toWeakSpace_image_sublevel [Preorder β] (b : β) :
    toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u)) ⁻¹' Iic b := by
  ext u
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage,
    mem_ofPred_eq, mem_inter_iff, mem_Iic]

/-- A set is sequentially weakly closed if and only if weak limits of sequences in it belong to
the set. -/
theorem isSeqClosed_toWeakSpace_iff :
    IsSeqClosed (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S := by
  constructor
  · intro hS u v hu hlim
    have hv := hS (fun n ↦ mem_image_of_mem (toWeakSpace 𝕜 V) (hu n)) hlim
    rwa [(toWeakSpace 𝕜 V).injective.mem_set_image] at hv
  · intro hS w z hw hlim
    have hmem : ∀ n, (toWeakSpace 𝕜 V).symm (w n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw n
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (w n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm z))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    have hz := hS hmem hlim'
    rwa [← (toWeakSpace 𝕜 V).apply_symm_apply z, (toWeakSpace 𝕜 V).injective.mem_set_image]

/-- Characterization of sequential weak lower semicontinuity on `S` directly in terms of weakly
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
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim y
        (by simpa only [LinearEquiv.symm_apply_apply] using hy)
  · intro hE w z hw hz hlim y hy
    have hw' : ∀ n, (toWeakSpace 𝕜 V).symm (w n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw n
    have hz' : (toWeakSpace 𝕜 V).symm z ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hz
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (w n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm z))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE hw' hz' hlim' y hy

/-- A real-valued energy is sequentially weakly lower semicontinuous on `S` if and only if
`(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along every weakly convergent sequence
`u n ⇀ v` in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_coe_le_liminf {E : V → ℝ} :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [seqLowerSemicontinuousOn_iff_coe_le_liminf]
  constructor
  · intro hE u v hu hv hlim
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
  · intro hE w z hw hz hlim
    have hw' : ∀ n, (toWeakSpace 𝕜 V).symm (w n) ∈ S := fun n ↦ by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hw n
    have hz' : (toWeakSpace 𝕜 V).symm z ∈ S := by
      simpa only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage] using hz
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm (w n))) atTop
        (𝓝 (toWeakSpace 𝕜 V ((toWeakSpace 𝕜 V).symm z))) := by
      simpa only [LinearEquiv.apply_symm_apply] using hlim
    exact hE hw' hz' hlim'

/-- On a weakly closed set, weak lower semicontinuity is equivalent to weak closedness of every
relative sublevel set. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel [LinearOrder β]
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_iff_isClosed_inter_preimage_Iic hS]
  simp only [toWeakSpace_image_sublevel]

/-- On a sequentially weakly closed set, sequential weak lower semicontinuity is equivalent to
sequential weak closedness of every relative sublevel set. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel [LinearOrder β]
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_inter_preimage_Iic hS]
  simp only [toWeakSpace_image_sublevel]

end WeakSublevels

/-! ### Agreement of sequential and topological weak lower semicontinuity -/

section WeakCompactAgreement

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [LinearOrder β] {E : V → β} {K : Set V}

/-- On any relatively weakly compact subset of a real or complex normed space, sequential weak
lower semicontinuity is equivalent to topological weak lower semicontinuity. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact_closure
    (hK : IsCompact (closure (toWeakSpace 𝕜 V '' K))) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := (frechetUrysohnSpace_toWeakSpace_of_isCompact_closure hK).to_sequentialSpace
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

/-- On any weakly compact subset of a real or complex normed space, sequential weak lower
semicontinuity is equivalent to topological weak lower semicontinuity. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
        (toWeakSpace 𝕜 V '' K) := by
  have := (frechetUrysohnSpace_toWeakSpace_of_isCompact hK).to_sequentialSpace
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

end WeakCompactAgreement

/-! ### The sequential direct method from a bounded minimizing sequence -/

section BoundedMinimizingSequence

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  {E : V → β} {S T : Set V}

/-- **The sequential direct method (subsequential convergence form).** In a reflexive real or
complex normed space, every norm-bounded sequence in `T` whose energies converge to `sInf (E '' S)`
has a subsequence converging weakly to a minimizer of `E` on `S` attaining `sInf (E '' S)`,
provided `E` is bounded below on `S` and weak limits of sequences in `T` lie in `S` and satisfy
the finite-limit lower semicontinuity inequality. -/
theorem exists_subseq_tendsto_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ T) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ T) → v ∈ S →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ T)
    (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  have hK := isCompact_closure_toWeakSpace_of_isBounded hV hb
  obtain ⟨v, φ, hφ, hlim⟩ := tendsto_subseq_toWeakSpace_of_isCompact_closure hK mem_range_self
  have hv : v ∈ S := hseqclosed (fun n ↦ u (φ n)) v (fun n ↦ hu (φ n)) hlim
  have hle : E v ≤ sInf (E '' S) :=
    hseqlsc (fun n ↦ u (φ n)) v (sInf (E '' S)) (fun n ↦ hu (φ n)) hv hlim
      (hminseq.comp hφ.tendsto_atTop)
  have hmin : IsMinOn E S v := fun x hx ↦ hle.trans (csInf_le hbelow (mem_image_of_mem E hx))
  exact ⟨v, hv, hmin, hle.antisymm (csInf_le hbelow (mem_image_of_mem E hv)), φ, hφ, hlim⟩

/-- **The sequential direct method.** In a reflexive real or complex normed space, a bounded-below
energy on a sequentially weakly closed set, sequentially weakly lower semicontinuous there, attains
its infimum as soon as one norm-bounded minimizing sequence exists. -/
theorem exists_isMinOn_of_bounded_minimizing_sequence
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S) → v ∈ S →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v := by
  obtain ⟨v, hv, hmin, -⟩ :=
    exists_subseq_tendsto_isMinOn_of_bounded_minimizing_sequence hV hbelow hseqclosed hseqlsc hu
      hb hminseq
  exact ⟨v, hv, hmin⟩

/-- Sublevel-localized sequential direct method: sequential weak closedness and sequential weak
lower semicontinuity need only hold along sequences lying in a single norm-bounded sublevel
`{u ∈ S | E u ≤ b}` that contains a minimizing sequence. -/
theorem exists_subseq_tendsto_isMinOn_of_minimizing_sequence_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S)) {b : β}
    (hb : IsBounded {u ∈ S | E u ≤ b})
    (hseqclosed : ∀ (u : ℕ → V) (v : V), (∀ n, u n ∈ S ∧ E (u n) ≤ b) →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S)
    (hseqlsc : ∀ (u : ℕ → V) (v : V) (r : β), (∀ n, u n ∈ S ∧ E (u n) ≤ b) → v ∈ S →
      Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
      Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S ∧ E (u n) ≤ b)
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) :=
  exists_subseq_tendsto_isMinOn_of_bounded_minimizing_sequence
    (T := {x ∈ S | E x ≤ b}) hV hbelow hseqclosed hseqlsc hu
    (hb.subset (range_subset_iff.2 hu)) hminseq

end BoundedMinimizingSequence

/-! ### The sequential direct method from bounded sublevels -/

section SeqBoundedSublevels

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [LinearOrder β] {E : V → β} {S : Set V}

/-- On a sequentially weakly closed set in a reflexive real or complex normed space, a bounded
sublevel of a sequentially weakly lower semicontinuous energy is weakly compact. -/
theorem isCompact_toWeakSpace_sublevel_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (b : β) (hb : IsBounded {u ∈ S | E u ≤ b}) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  have hseq : IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel hS).1 hE b
  have hrel : IsCompact (closure (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b})) :=
    isCompact_closure_toWeakSpace_of_isBounded hV hb
  have hclosed : IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (isClosed_toWeakSpace_iff_isSeqClosed_of_isCompact_closure hrel).2 hseq
  simpa only [hclosed.closure_eq] using hrel

/-- A single nonempty bounded sublevel suffices for the sequential direct method on a sequentially
weakly closed set in a reflexive real or complex normed space; no lower bound on the energy or
topology on the codomain is needed. -/
theorem exists_isMinOn_of_isSeqClosed_toWeakSpace_of_isBounded_sublevel
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {b : β} (hne : {u ∈ S | E u ≤ b}.Nonempty)
    (hb : IsBounded {u ∈ S | E u ≤ b}) : ∃ u ∈ S, IsMinOn E S u := by
  have hcompact := isCompact_toWeakSpace_sublevel_of_isSeqClosed hV hS hE b hb
  have hE_lsc : LowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) :=
    (seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact hcompact).1
      (hE.mono (image_mono fun _ hx ↦ hx.1))
  obtain ⟨w, hw, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hcompact hE_lsc
  obtain ⟨u, hu, rfl⟩ := hw
  refine ⟨u, hu.1, (isMinOn_sublevel_iff hu.2).1 fun x hx ↦ ?_⟩
  simpa only [mem_ofPred_eq, LinearEquiv.symm_apply_apply] using
    hmin (mem_image_of_mem (toWeakSpace 𝕜 V) hx)

/-- **The sequential direct method from bounded sublevels.** A sequentially weakly lower
semicontinuous energy with bounded sublevels on a nonempty sequentially weakly closed set in a
reflexive real or complex normed space attains its minimum. -/
theorem exists_isMinOn_of_isSeqClosed_toWeakSpace
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hne : S.Nonempty) (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) : ∃ u ∈ S, IsMinOn E S u := by
  obtain ⟨v, hv⟩ := hne
  exact exists_isMinOn_of_isSeqClosed_toWeakSpace_of_isBounded_sublevel hV hS hE
    ⟨v, hv, le_rfl⟩ (hb.isBounded_sublevel (E v))

/-- If the set of minimizers of a sequentially weakly lower semicontinuous energy on a sequentially
weakly closed set in a reflexive real or complex normed space is bounded, then that set of
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

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive real or complex normed space, the set of minimizers is weakly
compact, including when the admissible set is empty. -/
theorem isCompact_toWeakSpace_minimizers_of_isSeqClosed
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S) :
    IsCompact (toWeakSpace 𝕜 V '' {u ∈ S | IsMinOn E S u}) :=
  isCompact_toWeakSpace_minimizers_of_isSeqClosed_of_isBounded hV hS hE hb.isBounded_minimizers

end SeqBoundedSublevels

/-! ### Subsequential weak convergence of near-minimizers -/

section NearMinimizers

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [ClosedIciTopology β]
  {E : V → β} {S : Set V}

/-- Every norm-bounded near-minimizing sequence of a bounded-below, sequentially weakly lower
semicontinuous energy on a sequentially weakly closed set in a reflexive space has a subsequence
converging weakly to a minimizer. -/
theorem exists_subseq_tendsto_isMinOn_of_isSeqClosed_of_isBounded
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hbelow : BddBelow (E '' S))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hb : IsBounded (range u))
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) :=
  exists_subseq_tendsto_isMinOn_of_bounded_minimizing_sequence hV hbelow
    (fun _ _ hseq hlim ↦ isSeqClosed_toWeakSpace_iff.1 hS hseq hlim)
    (fun _ _ _ hseq hv hlim hE_lim ↦ by
      simpa only [LinearEquiv.symm_apply_apply] using
        hE.le_of_tendsto (fun n ↦ mem_image_of_mem _ (hseq n)) (mem_image_of_mem _ hv) hlim
          (by simpa only [LinearEquiv.symm_apply_apply] using hE_lim))
    hu hb hminseq

/-- For a sequentially weakly lower semicontinuous energy with bounded sublevels on a sequentially
weakly closed set in a reflexive space, every near-minimizing sequence is automatically bounded and
has a subsequence converging weakly to a minimizer. -/
theorem exists_subseq_tendsto_isMinOn_of_hasBoundedSublevelsOn
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V))
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S))
    (hE : SeqLowerSemicontinuousOn (fun u : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm u))
      (toWeakSpace 𝕜 V '' S))
    (hb : HasBoundedSublevelsOn E S)
    {u : ℕ → V} (hu : ∀ n, u n ∈ S)
    (hminseq : Tendsto (fun n ↦ E (u n)) atTop (𝓝 (sInf (E '' S)))) :
    ∃ v ∈ S, IsMinOn E S v ∧ E v = sInf (E '' S) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
  obtain ⟨w, -, hmin⟩ := exists_isMinOn_of_isSeqClosed_toWeakSpace hV ⟨u 0, hu 0⟩ hS hE hb
  exact exists_subseq_tendsto_isMinOn_of_isSeqClosed_of_isBounded hV hmin.bddBelow hS hE hu
    (hb.isBounded_range hu hminseq.bddAbove_range) hminseq

end NearMinimizers

end TauCeti
