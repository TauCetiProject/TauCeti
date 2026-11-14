/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian
public import TauCeti.Topology.Algebra.Module.WeakSpace
public import TauCeti.Topology.Semicontinuity.Sequences

/-!
# Weak and sequential weak lower semicontinuity on admissible sets

For an ordered-valued energy `E : V → β` on an admissible subset `S` of a topological module `V`,
weak lower semicontinuity is `LowerSemicontinuousOn` of `w ↦ E ((toWeakSpace 𝕜 V).symm w)` on
`toWeakSpace 𝕜 V '' S`, and sequential weak lower semicontinuity is
`TauCeti.SeqLowerSemicontinuousOn` of the same function on `toWeakSpace 𝕜 V '' S`.

This file provides the characterizations used in the direct method:
* Weak lower semicontinuity on `S` is equivalent to weak closedness in `S` of every relative
  sublevel `{u ∈ S | E u ≤ b}` (`TauCeti.lowerSemicontinuousOn_toWeakSpace_iff_sublevel`), and on a
  weakly closed `S` to weak closedness of every relative sublevel
  (`IsClosed.lowerSemicontinuousOn_toWeakSpace_iff`).
* Sequential weak lower semicontinuity unpacks directly to weakly convergent sequences in `S`
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff`), to sequential weak closedness of relative
  sublevels when `S` is sequentially weakly closed
  (`IsSeqClosed.seqLowerSemicontinuousOn_toWeakSpace_iff`), to the `EReal` lower-limit inequality
  for real-valued energies (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_coe_ereal_le_liminf`),
  and — when `E '' S` is bounded below and closed intervals in `β` are sequentially compact — to
  the finite-limit inequality
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_le_of_tendsto_of_bddBelow`).
* On any weakly compact subset `K` of a real or complex seminormed space, sequential weak lower
  semicontinuity and topological weak lower semicontinuity agree
  (`TauCeti.seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact`), by the
  sequential-closure form of Eberlein–Šmulian.
-/

public section

open Filter Set Topology

namespace TauCeti

section Module

variable {𝕜 V β : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V]
  {E : V → β} {S : Set V}

private theorem image_toWeakSpace_sublevel [Preorder β] (b : β) :
    toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} =
      (toWeakSpace 𝕜 V '' S) ∩
        (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ⁻¹' Iic b := by
  ext w
  simp only [(toWeakSpace 𝕜 V).image_eq_preimage_symm, mem_preimage,
    mem_ofPred_eq, mem_inter_iff, mem_Iic]

/-- Weak lower semicontinuity of `E` on `S` is equivalent to weak closedness in `S` of every
relative sublevel `{u ∈ S | E u ≤ b}`. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_sublevel [LinearOrder β] :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, ∃ C : Set (WeakSpace 𝕜 V), IsClosed C ∧
        toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b} = (toWeakSpace 𝕜 V '' S) ∩ C := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic]
  exact forall_congr' fun b ↦ by simp only [image_toWeakSpace_sublevel b]

/-- On a weakly closed set `S`, weak lower semicontinuity of `E` on `S` is equivalent to weak
closedness of every relative sublevel `{u ∈ S | E u ≤ b}`. -/
theorem _root_.IsClosed.lowerSemicontinuousOn_toWeakSpace_iff [LinearOrder β]
    (hS : IsClosed (toWeakSpace 𝕜 V '' S)) :
    LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [lowerSemicontinuousOn_toWeakSpace_iff_sublevel]
  refine forall_congr' fun b ↦ ⟨fun ⟨C, hC, hEC⟩ ↦ hEC ▸ hS.inter hC, fun hb ↦ ⟨_, hb, ?_⟩⟩
  exact (inter_eq_right.mpr (image_mono (sep_subset S fun u ↦ E u ≤ b))).symm

/-- Sequential weak lower semicontinuity of `E` on `S` expressed directly in terms of sequences in
`S` converging weakly to a point of `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff [Preorder β] :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        ∀ b < E v, ∀ᶠ n in atTop, b < E (u n) := by
  rw [seqLowerSemicontinuousOn_iff]
  constructor
  · intro hE u v hu hv hlim b hb
    have hb' : b < E ((toWeakSpace 𝕜 V).symm (toWeakSpace 𝕜 V v)) := by
      simpa only [LinearEquiv.symm_apply_apply] using hb
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim b hb'
  · intro hE w z hw hz hlim b hb
    choose u huS huw using hw
    obtain ⟨v, hvS, rfl⟩ := hz
    have hlim' : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) := by
      simpa only [huw] using hlim
    have hb' : b < E v := by simpa only [LinearEquiv.symm_apply_apply] using hb
    exact (hE huS hvS hlim' b hb').mono fun n hn ↦ by
      simpa only [← huw n, LinearEquiv.symm_apply_apply] using hn

/-- On a sequentially weakly closed set `S`, sequential weak lower semicontinuity of `E` on `S` is
equivalent to sequential weak closedness of every relative sublevel `{u ∈ S | E u ≤ b}`. -/
theorem _root_.IsSeqClosed.seqLowerSemicontinuousOn_toWeakSpace_iff [LinearOrder β]
    (hS : IsSeqClosed (toWeakSpace 𝕜 V '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ b : β, IsSeqClosed (toWeakSpace 𝕜 V '' {u ∈ S | E u ≤ b}) := by
  rw [hS.seqLowerSemicontinuousOn_iff]
  exact forall_congr' fun b ↦ by rw [image_toWeakSpace_sublevel b]; rfl

/-- Along a sequence in `S` converging weakly to `v ∈ S`, a convergent energy sequence bounds `E v`
above when `E` is sequentially weakly lower semicontinuous on `S`. -/
theorem SeqLowerSemicontinuousOn.le_of_tendsto_toWeakSpace [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β]
    (hE : SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
      (toWeakSpace 𝕜 V '' S))
    {u : ℕ → V} {v : V} {r : β} (hu : ∀ n, u n ∈ S) (hv : v ∈ S)
    (huv : Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)))
    (hEu : Tendsto (fun n ↦ E (u n)) atTop (𝓝 r)) : E v ≤ r := by
  simpa only [LinearEquiv.symm_apply_apply] using hE.le_of_tendsto
    (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) huv
    (by simpa only [LinearEquiv.symm_apply_apply] using hEu)

/-- When `E '' S` is bounded below and closed intervals in `β` are sequentially compact, sequential
weak lower semicontinuity of `E` on `S` is equivalent to the finite-limit inequality along weakly
convergent sequences in `S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_le_of_tendsto_of_bddBelow [LinearOrder β]
    [TopologicalSpace β] [ClosedIciTopology β] [CompactIccSpace β] [FirstCountableTopology β]
    (hbdd : BddBelow (E '' S)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄ ⦃r : β⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        Tendsto (fun n ↦ E (u n)) atTop (𝓝 r) → E v ≤ r := by
  have hbdd' : BddBelow
      ((fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) '' (toWeakSpace 𝕜 V '' S)) := by
    rwa [← image_comp, (by ext x; simp :
      (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w)) ∘ toWeakSpace 𝕜 V = E)]
  rw [seqLowerSemicontinuousOn_iff_le_of_tendsto_of_bddBelow hbdd']
  constructor
  · intro hfin u v r hu hv huv hEu
    simpa only [LinearEquiv.symm_apply_apply] using hfin
      (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) huv
      (by simpa only [LinearEquiv.symm_apply_apply] using hEu)
  · intro hfin w z r hw hz hwz hEw
    choose u huS huw using hw
    obtain ⟨v, hvS, rfl⟩ := hz
    simpa only [LinearEquiv.symm_apply_apply] using hfin huS hvS
      (by simpa only [huw] using hwz)
      (by simpa only [← huw, LinearEquiv.symm_apply_apply] using hEw)

/-- For a real-valued energy `E : V → ℝ`, sequential weak lower semicontinuity on `S` is equivalent
to `(E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop` along every sequence in `S`
converging weakly to `v ∈ S`. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_coe_ereal_le_liminf {E : V → ℝ} :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' S) ↔
      ∀ ⦃u : ℕ → V⦄ ⦃v : V⦄, (∀ n, u n ∈ S) → v ∈ S →
        Tendsto (fun n ↦ toWeakSpace 𝕜 V (u n)) atTop (𝓝 (toWeakSpace 𝕜 V v)) →
        (E v : EReal) ≤ liminf (fun n ↦ (E (u n) : EReal)) atTop := by
  rw [seqLowerSemicontinuousOn_iff_coe_ereal_le_liminf]
  constructor
  · intro hE u v hu hv hlim
    simpa only [LinearEquiv.symm_apply_apply] using
      hE (fun n ↦ mem_image_of_mem _ (hu n)) (mem_image_of_mem _ hv) hlim
  · intro hE w z hw hz hlim
    choose u huS huw using hw
    obtain ⟨v, hvS, rfl⟩ := hz
    have h := hE huS hvS (by simpa only [huw] using hlim)
    simpa only [← huw, LinearEquiv.symm_apply_apply] using h

end Module

section Seminormed

variable {𝕜 V β : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup V] [NormedSpace 𝕜 V] [LinearOrder β] {E : V → β} {K : Set V}

/-- On a weakly compact subset `K` of a real or complex seminormed space, sequential weak lower
semicontinuity and topological weak lower semicontinuity agree. -/
theorem seqLowerSemicontinuousOn_toWeakSpace_iff_lowerSemicontinuousOn_of_isCompact
    (hK : IsCompact (toWeakSpace 𝕜 V '' K)) :
    SeqLowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' K) ↔
      LowerSemicontinuousOn (fun w : WeakSpace 𝕜 V ↦ E ((toWeakSpace 𝕜 V).symm w))
        (toWeakSpace 𝕜 V '' K) := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  have : FrechetUrysohnSpace (toWeakSpace 𝕜 V '' K) :=
    frechetUrysohnSpace_toWeakSpace_of_isCompact hK
  exact seqLowerSemicontinuousOn_iff_lowerSemicontinuousOn

end Seminormed

end TauCeti
