/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Analytic changes of ambient coordinates

Analytic charts and analytic submanifolds pull back along an analytic homeomorphism whose
inverse is analytic. In particular, permuting ambient coordinates preserves the dimension of
an analytic submanifold. This permits analytic cells of cylindrical stacks to be transported
when the base coordinates are reordered.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ} {S : Set (Fin n → 𝕜)}
  {c : OpenPartialHomeomorph (Fin n → 𝕜) (Fin n → 𝕜)}

/-- Pulling back an analytic chart along an analytic change of ambient coordinates gives an
analytic chart of the inverse image. -/
theorem IsAnalyticChart.preimage (hc : IsAnalyticChart d S c)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticChart d (e ⁻¹' S) (e.toOpenPartialHomeomorph.trans c) := by
  -- Composition pulls the chart source back along e and sends x to c (e x).
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    simpa only [OpenPartialHomeomorph.coe_trans] using
      (hc.analyticOnNhd _ hx.2).comp (he x (mem_univ _))
  · intro y hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    simpa only [OpenPartialHomeomorph.coe_trans_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply] using
      (he' _ (mem_univ _)).comp (hc.analyticOnNhd_symm _ hy.1)
  · intro x hx
    rw [OpenPartialHomeomorph.trans_source] at hx
    simpa only [OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, mem_preimage] using hc.isImage hx.2

/-- An analytic change of ambient coordinates preserves analytic submanifolds and their
dimension. The inverse must also be analytic. -/
theorem IsAnalyticSubmanifold.preimage (hS : IsAnalyticSubmanifold d S)
    (e : (Fin n → 𝕜) ≃ₜ (Fin n → 𝕜))
    (he : AnalyticOnNhd 𝕜 e univ) (he' : AnalyticOnNhd 𝕜 e.symm univ) :
    IsAnalyticSubmanifold d (e ⁻¹' S) := by
  refine ⟨?_, hS.le, fun x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hS.nonempty
    exact ⟨e.symm y, by simpa using hy⟩
  · obtain ⟨c, hxc, hc⟩ := hS.exists_isAnalyticChart (e x) hx
    refine ⟨e.toOpenPartialHomeomorph.trans c, ?_, hc.preimage e he he'⟩
    -- The homeomorphism has full source, so the composite source is e ⁻¹' c.source.
    simpa only [OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_apply,
      univ_inter, mem_preimage] using hxc

end TauCeti
