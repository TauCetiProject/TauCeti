/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-!
# Analytic changes of ambient coordinates

Analytic charts and analytic submanifolds pull back along an analytic homeomorphism whose
inverse is analytic, including local changes of coordinates on their open domains. These
transport results let compatible local coordinate tests determine the image in any chart,
without a second submanifold carrier.

In particular, permuting or reindexing ambient coordinates preserves the dimension of an
analytic submanifold, as does changing a continuous linear identification with finite
coordinates. This permits analytic cells of cylindrical stacks to be transported when the
base coordinates are reordered.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ} {S : Set (Fin n → 𝕜)}
  {c : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}

/-- Pulling back an analytic chart along a local analytic change of ambient coordinates
straightens the inverse image inside the coordinate domain. -/
theorem IsAnalyticChart.preimage_openPartialHomeomorph (hc : IsAnalyticChart d S c)
    (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e e.source) (he' : AnalyticOnNhd 𝕜 e.symm e.target) :
    IsAnalyticChart d (e.source ∩ e ⁻¹' S) (e.trans c) := by
  refine ⟨?_, ?_, fun x hx ↦ ?_⟩
  · intro x hx
    simpa only [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.symm_symm] using
      (hc.analyticOnNhd _ hx.2).comp (he x hx.1)
  · intro y hy
    simpa only [OpenPartialHomeomorph.coe_trans_symm] using
      (he' _ hy.2).comp (hc.analyticOnNhd_symm _ hy.1)
  · have hx' : x ∈ e.source := hx.1
    simpa only [OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_symm,
      mem_ofPred_eq, mem_inter_iff, mem_preimage, hx', true_and] using hc.isImage hx.2

/-- A local analytic coordinate change pulls a submanifold back to a submanifold in its
source, provided that this inverse image is nonempty. -/
theorem IsAnalyticSubmanifold.preimage_openPartialHomeomorph (hS : IsAnalyticSubmanifold d S)
    (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e e.source) (he' : AnalyticOnNhd 𝕜 e.symm e.target)
    (hne : (e.source ∩ e ⁻¹' S).Nonempty) :
    IsAnalyticSubmanifold d (e.source ∩ e ⁻¹' S) := by
  refine ⟨hne, hS.le, fun x hx ↦ ?_⟩
  obtain ⟨c, hxc, hc⟩ := hS.exists_isAnalyticChart (e x) hx.2
  exact ⟨e.trans c, ⟨hx.1, hxc⟩, hc.preimage_openPartialHomeomorph e he he'⟩

/-- Pulling back an analytic chart along an analytic change of ambient coordinates gives an
analytic chart of the inverse image. -/
theorem IsAnalyticChart.preimage (hc : IsAnalyticChart d S c)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticChart d (e ⁻¹' S) (e.toOpenPartialHomeomorph.trans c) := by
  simpa only [Homeomorph.toOpenPartialHomeomorph_source, univ_inter,
    Homeomorph.toOpenPartialHomeomorph_apply] using
    hc.preimage_openPartialHomeomorph e.toOpenPartialHomeomorph he he'

/-- An analytic change of ambient coordinates preserves analytic submanifolds and their
dimension. The inverse must also be analytic. -/
theorem IsAnalyticSubmanifold.preimage (hS : IsAnalyticSubmanifold d S)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticSubmanifold d (e ⁻¹' S) := by
  have hne : (e.toOpenPartialHomeomorph.source ∩ e.toOpenPartialHomeomorph ⁻¹' S).Nonempty := by
    obtain ⟨y, hy⟩ := hS.nonempty
    exact ⟨e.symm y, mem_univ _, by simpa only [mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_apply, e.apply_symm_apply] using hy⟩
  simpa only [Homeomorph.toOpenPartialHomeomorph_source, univ_inter,
    Homeomorph.toOpenPartialHomeomorph_apply] using
    hS.preimage_openPartialHomeomorph e.toOpenPartialHomeomorph he he' hne

/-- Reindexing the ambient coordinates along a bijection `Fin n ≃ Fin n'` preserves analytic
submanifolds and their dimension. For `n' = n` this is a permutation of the coordinates. -/
theorem IsAnalyticSubmanifold.preimage_comp_equiv {n' : ℕ} (hS : IsAnalyticSubmanifold d S)
    (e : Fin n ≃ Fin n') : IsAnalyticSubmanifold d ((fun x : Fin n' → 𝕜 ↦ x ∘ e) ⁻¹' S) := by
  obtain rfl : n = n' := by simpa using Fintype.card_congr e
  -- Precomposition with a permutation of coordinates is a continuous linear equivalence.
  let L := (ContinuousLinearEquiv.piCongrLeft 𝕜 (fun _ : Fin n ↦ 𝕜) e).symm
  exact hS.preimage L.toHomeomorph (fun y _ ↦ L.analyticAt y) (fun y _ ↦ L.symm.analyticAt y)

/-- A local analytic coordinate change sends the part of a submanifold in its source to a
submanifold of the same dimension, if that part is nonempty. -/
theorem IsAnalyticSubmanifold.image_openPartialHomeomorph (hS : IsAnalyticSubmanifold d S)
    (e : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e e.source) (he' : AnalyticOnNhd 𝕜 e.symm e.target)
    (hne : (e.source ∩ S).Nonempty) :
    IsAnalyticSubmanifold d (e '' (e.source ∩ S)) := by
  rw [e.image_source_inter_eq']
  exact hS.preimage_openPartialHomeomorph e.symm he' he <| by
    obtain ⟨x, hx, hxS⟩ := hne
    exact ⟨e x, e.map_source hx, by simpa only [mem_preimage, e.left_inv hx] using hxS⟩

/-- To test the coordinate image in a fixed chart, it suffices to have a native
submanifold image in a compatible chart near each point. Compatibility is analyticity of
the coordinate change and its inverse on their open domains. -/
theorem _root_.OpenPartialHomeomorph.isAnalyticSubmanifold_image_source_inter_of_locally
    {X : Type*} [TopologicalSpace X] {T : Set X}
    (e : OpenPartialHomeomorph X (Fin n → 𝕜)) (hne : (e.source ∩ T).Nonempty)
    (h : ∀ x ∈ e.source ∩ T, ∃ c : OpenPartialHomeomorph X (Fin n → 𝕜),
      x ∈ c.source ∧ IsAnalyticSubmanifold d (c '' (c.source ∩ T)) ∧
        AnalyticOnNhd 𝕜 (e.symm.trans c) (e.symm.trans c).source ∧
        AnalyticOnNhd 𝕜 (e.symm.trans c).symm (e.symm.trans c).target) :
    IsAnalyticSubmanifold d (e '' (e.source ∩ T)) := by
  refine isAnalyticSubmanifold_of_locally_isAnalyticSubmanifold (hne.image e) ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hxc, hc, htrans, htrans'⟩ := h x hx
  let a := e.symm.trans c
  have hxU : e x ∈ a.source := by
    simp only [a, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage, e.left_inv hx.1]
    exact ⟨e.map_source hx.1, hxc⟩
  have heq : a.source ∩ a ⁻¹' (c '' (c.source ∩ T)) =
      (e '' (e.source ∩ T)) ∩ a.source := by
    rw [c.image_source_inter_eq', e.image_source_inter_eq']
    ext z
    by_cases hz : z ∈ a.source
    · have hze : z ∈ e.target := hz.1
      have hzc : e.symm z ∈ c.source := hz.2
      simp only [mem_inter_iff, mem_preimage, hz, true_and, and_true,
        a, OpenPartialHomeomorph.trans_apply, c.left_inv hzc, hze,
        c.map_source hzc]
    · simp only [mem_inter_iff, hz, false_and, and_false]
  refine ⟨a.source, a.open_source, hxU, ?_⟩
  rw [← heq]
  exact hc.preimage_openPartialHomeomorph a htrans htrans' <| by
    refine ⟨e x, hxU, ?_⟩
    exact ⟨x, ⟨hxc, hx.2⟩, by simp only [a, OpenPartialHomeomorph.trans_apply,
      e.left_inv hx.1]⟩

/-- Changing a continuous linear identification with finite coordinates does not change
whether a set is an analytic submanifold, nor its dimension. -/
theorem _root_.ContinuousLinearEquiv.isAnalyticSubmanifold_image_iff_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {T : Set E}
    (L L' : E ≃L[𝕜] (Fin n → 𝕜)) :
    IsAnalyticSubmanifold d (L '' T) ↔ IsAnalyticSubmanifold d (L' '' T) := by
  have transport (A B : E ≃L[𝕜] (Fin n → 𝕜))
      (h : IsAnalyticSubmanifold d (A '' T)) : IsAnalyticSubmanifold d (B '' T) := by
    let C := A.symm.trans B
    have himage : B '' T = C '' (A '' T) := by
      simp only [image_image, C, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.symm_apply_apply]
    rw [himage, ContinuousLinearEquiv.image_eq_preimage_symm]
    exact h.preimage C.symm.toHomeomorph (fun x _ ↦ C.symm.analyticAt x)
      (fun x _ ↦ C.analyticAt x)
  exact ⟨transport L L', transport L' L⟩

end TauCeti
