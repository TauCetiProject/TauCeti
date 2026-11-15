/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Semicontinuity.Sequential

/-!
# Topological and sequential weak lower semicontinuity

Following Mathlib's `WeakSpace` design, weak lower semicontinuity and weak sequential lower
semicontinuity of a functional `E : V → β` on an admissible set `S : Set V` are expressed
directly as `LowerSemicontinuousOn` and `TauCeti.SeqLowerSemicontinuousOn` of the transported
functional `w ↦ E ((toWeakSpace 𝕜 V).symm w)` on `toWeakSpace 𝕜 V '' S`, without wrapper
predicates.

This file provides the bridge between those `WeakSpace` formulations and concrete statements
on `V`:

* sublevel characterizations of topological and sequential weak lower semicontinuity in terms
  of `toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}`, and transfer to strong (ambient) lower
  semicontinuity via continuity of `toWeakSpaceCLM 𝕜 V`;
* sequence-level characterizations of `IsSeqClosed (toWeakSpace 𝕜 V '' S)` and
  `SeqLowerSemicontinuousOn` along weakly convergent sequences `u : ℕ → V` in `S`, including
  complete-lattice `liminf`, real `EReal`-valued `liminf`, and bounded-below finite-limit
  criteria;
* equivalence of topological and sequential weak lower semicontinuity on any relatively
  weakly compact set (in particular, any weakly compact set or subset thereof) in a real or
  complex normed space, deduced from the Fréchet–Urysohn property established in
  `TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §3.3.
* J. K. Hunter, *Notes on Partial Differential Equations*, §4.2.
-/

public section

open Filter Function Set Topology

namespace TauCeti

section TopologicalModule

variable {𝕜 V : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]

/-- Transporting the restricted sublevel `{u ∈ S | E u ≤ b}` to `WeakSpace 𝕜 V` gives the
intersection of `toWeakSpace 𝕜 V '' S` with the `Iic b` preimage of the transported energy. -/
theorem toWeakSpace_sublevel_eq {β : Type*} [Preorder β] (E : V → β) (S : Set V) (b : β) :
    toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b := by
  ext w
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq,
    mem_inter_iff, mem_Iic]

/-- Weak lower semicontinuity of `E` on `S` into a linear order is equivalent to relative
weak closedness of every sublevel `{u ∈ S | E u ≤ b}` in `S`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, ∃ C : Set (WeakSpace 𝕜 V), IsClosed C ∧
        toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} = (toWeakSpace 𝕜 V '' S) ∩ C := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  exact forall_congr' fun b ↦ exists_congr fun C ↦
    and_congr_right fun _ ↦ by rw [toWeakSpace_sublevel_eq]

/-- On a weakly closed set `S`, weak lower semicontinuity into a linear order is equivalent to
weak closedness of every sublevel `{u ∈ S | E u ≤ b}`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_isClosed_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} {S : Set V} (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_toWeakSpace_iff_sublevel]
  refine forall_congr' fun b ↦ ⟨?_, fun hb ↦ ⟨toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}, hb, ?_⟩⟩
  · rintro ⟨C, hC, hEq⟩
    exact hEq ▸ hS.inter hC
  · exact (inter_eq_right.2 (image_mono (sep_subset S _))).symm

/-- Global weak lower semicontinuity of `E` on `V` into a linear order is equivalent to weak
closedness of every sublevel `{u : V | E u ≤ b}`. -/
theorem lowerSemicontinuous_toWeakSpace_iff_isClosed_sublevel {β : Type*} [LinearOrder β]
    {E : V → β} :
    LowerSemicontinuous (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ↔
      ∀ b, IsClosed (toWeakSpace 𝕜 V '' {u : V | E u ≤ b}) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  refine forall_congr' fun b ↦ ?_
  have heq : toWeakSpace 𝕜 V '' {u : V | E u ≤ b} =
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b := by
    ext w
    simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage, mem_ofPred_eq, mem_Iic]
  rw [heq]

/-- Weak lower semicontinuity on `S` implies lower semicontinuity on `S` in the ambient
topology of `V`. -/
theorem lowerSemicontinuousOn_of_toWeakSpace {β : Type*} [Preorder β] {E : V → β} {S : Set V}
    (hE : LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn E S := by
  have hcomp := hE.comp (toWeakSpaceCLM 𝕜 V).continuous.continuousOn (mapsTo_image _ S)
  simpa only [Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace, LinearEquiv.symm_apply_apply]
    using hcomp

/-- A subset `S : Set V` has sequentially closed weak image if and only if the weak limit in
`V` of every sequence in `S` again belongs to `S`. -/
theorem isSeqClosed_toWeakSpace_iff {S : Set V} :
    IsSeqClosed (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) → v ∈ S := by
  constructor
  · intro hS u v hu hlim
    obtain ⟨x, hx, hxv⟩ := hS (fun n ↦ mem_image_of_mem _ (hu n)) hlim
    exact (toWeakSpace 𝕜 V).injective hxv ▸ hx
  · intro hS w z hw hlim
    choose u hu hwu using hw
    refine ⟨(toWeakSpace 𝕜 V).symm z, hS hu ?_, (toWeakSpace 𝕜 V).apply_symm_apply z⟩
    simpa only [hwu, LinearEquiv.apply_symm_apply] using hlim

/-- Sequential weak lower semicontinuity of `E` on `S`, unpacked directly in terms of
sequences `u : ℕ → V` in `S` converging weakly to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff {β : Type*} [Preorder β]
    {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, v ∈ S → (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ y < E v, ∀ᶠ n in atTop, y < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  constructor
  · intro hE u v hv hu hlim y hy
    simpa only [LinearEquiv.symm_apply_apply] using hE (mem_image_of_mem _ hv)
      (fun n ↦ mem_image_of_mem _ (hu n)) hlim y (by simpa using hy)
  · intro hE w z hz hw hlim y hy
    obtain ⟨v, hv, rfl⟩ := hz
    choose u hu hwu using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [hwu] using hlim
    have hy' : y < E v := by simpa only [LinearEquiv.symm_apply_apply] using hy
    exact (hE hv hu hlim' y hy').mono fun n hn ↦ by
      simpa only [← hwu n, LinearEquiv.symm_apply_apply] using hn

/-- Weak sequential lower semicontinuity on `S` implies sequential lower semicontinuity on `S`
in the ambient topology of `V`. -/
theorem seqLowerSemicontinuousOn_of_toWeakSpace {β : Type*} [Preorder β]
    {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn E S := by
  have hcomp := hE.comp_continuousOn (toWeakSpaceCLM 𝕜 V).continuous.continuousOn
    (mapsTo_image _ S)
  simpa only [Function.comp_def, toWeakSpaceCLM_eq_toWeakSpace, LinearEquiv.symm_apply_apply]
    using hcomp

/-- On a weakly sequentially closed set `S`, weak sequential lower semicontinuity into a
linear order is equivalent to weak sequential closedness of every sublevel
`{u ∈ S | E u ≤ b}`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_isSeqClosed_sublevel {β : Type*}
    [LinearOrder β] {E : V → β} {S : Set V} (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ b, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [seqLowerSemicontinuousOn_iff_isSeqClosed_sublevel hS]
  refine forall_congr' fun b ↦ ?_
  have heq : toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      {w ∈ toWeakSpace 𝕜 V '' S | E ((toWeakSpace 𝕜 V).symm w) ≤ b} := by
    rw [toWeakSpace_sublevel_eq]
    rfl
  rw [heq]

/-- Into a complete linear order, weak sequential lower semicontinuity on `S` is equivalent
to `E v ≤ liminf (E ∘ u) atTop` along every sequence `u` in `S` converging weakly to
`v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf {β : Type*} [CompleteLinearOrder β]
    {E : V → β} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, v ∈ S → (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        E v ≤ liminf (E ∘ u) atTop := by
  rw [seqLowerSemicontinuousOn_iff_le_liminf]
  constructor
  · intro hE u v hv hu hlim
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
      hE (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hlim
  · intro hE w z hz hw hlim
    obtain ⟨v, hv, rfl⟩ := hz
    choose u hu hwu using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [hwu] using hlim
    have hfun : ((fun x : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm x)) ∘ w) = E ∘ u := by
      ext n
      simp [← hwu n]
    simpa only [LinearEquiv.symm_apply_apply, hfun] using hE hv hu hlim'

/-- For a real-valued functional `E : V → ℝ`, weak sequential lower semicontinuity on `S` is
equivalent to `(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along every sequence
`u` in `S` converging weakly to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_coe_le_liminf {E : V → ℝ} {S : Set V} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, v ∈ S → (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [← seqLowerSemicontinuousOn_coe_ereal_iff,
    seqLowerSemicontinuousOn_toWeakSpace_iff_le_liminf (E := fun x ↦ (E x : EReal))]
  rfl

/-- If `E` is weakly sequentially lower semicontinuous on `S`, `u` is a sequence in `S`
converging weakly to `v ∈ S`, and `E ∘ u` converges to `b`, then `E v ≤ b`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace {β : Type*} [LinearOrder β]
    [TopologicalSpace β] [OrderTopology β] {E : V → β} {S : Set V}
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} {v : V} {b : β} (hv : v ∈ S) (hu : ∀ n, u n ∈ S)
    (hw : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    (hEu : Tendsto (E ∘ u) atTop (𝓝 b)) :
    E v ≤ b := by
  have hEu' : Tendsto ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ∘
      fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 b) := by
    simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEu
  simpa only [LinearEquiv.symm_apply_apply] using
    hE.le_of_tendsto (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hw hEu'

/-- When `E '' S` is bounded below and closed intervals in `β` are compact and
first-countable, weak sequential lower semicontinuity on `S` is equivalent to `E v ≤ b`
whenever `u` in `S` converges weakly to `v ∈ S` and `E ∘ u` converges to `b`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_of_tendsto_of_bddBelow {β : Type*}
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β] [CompactIccSpace β]
    [FirstCountableTopology β] {E : V → β} {S : Set V} (hbdd : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ {b : β}, v ∈ S → (∀ n, u n ∈ S) →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (E ∘ u) atTop (𝓝 b) → E v ≤ b := by
  have hbdd' : BddBelow ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ''
      (toWeakSpace 𝕜 V '' S)) := by
    simpa only [image_image, LinearEquiv.symm_apply_apply] using hbdd
  rw [seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow hbdd']
  constructor
  · intro h u v b hv hu hw hEu
    have hEu' : Tendsto ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ∘
        fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 b) := by
      simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using hEu
    simpa only [LinearEquiv.symm_apply_apply] using
      h (mem_image_of_mem _ hv) (fun n ↦ mem_image_of_mem _ (hu n)) hw hEu'
  · intro h w z b hz hw hlim hEw
    obtain ⟨v, hv, rfl⟩ := hz
    choose u hu hwu using hw
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [hwu] using hlim
    have hEu : Tendsto (E ∘ u) atTop (𝓝 b) := by
      simpa only [Function.comp_def, ← hwu, LinearEquiv.symm_apply_apply] using hEw
    simpa only [LinearEquiv.symm_apply_apply] using h hv hu hlim' hEu

end TopologicalModule

section NormedSpace

variable {𝕜 V β : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [LinearOrder β] {E : V → β}

/-- On any relatively weakly compact set `S` in a real or complex normed space, topological
and sequential weak lower semicontinuity coincide. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact_closure
    {S : Set V} (hS : IsCompact (closure (toWeakSpace 𝕜 V '' S))) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) := by
  let := frechetUrysohnSpace_toWeakSpace_of_isCompact_closure hS
  exact lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn

/-- On any weakly compact set `K` in a real or complex normed space, topological and
sequential weak lower semicontinuity coincide. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_isCompact
    {K : Set V} (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' K) ↔
      SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' K) := by
  let := frechetUrysohnSpace_toWeakSpace_of_isCompact hK
  exact lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn

/-- On any subset `S` of a weakly compact set `K` in a real or complex normed space,
topological and sequential weak lower semicontinuity coincide. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_seqLowerSemicontinuousOn_of_subset_isCompact
    {S K : Set V} (hK : IsCompact (toWeakSpace 𝕜 V '' K)) (hSK : S ⊆ K) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S) ↔
      SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) := by
  let := frechetUrysohnSpace_toWeakSpace_of_subset_isCompact hK hSK
  exact lowerSemicontinuousOn_iff_seqLowerSemicontinuousOn

end NormedSpace

end TauCeti
