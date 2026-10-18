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
  refine ⟨fun x hx ↦ (hc.analyticOnNhd _ hx.2).comp (he x (mem_univ _)),
    fun y hy ↦ (he' _ (mem_univ _)).comp (hc.analyticOnNhd_symm _ hy.1), ?_⟩
  intro x hx
  exact hc.isImage hx.2

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
    exact ⟨e.toOpenPartialHomeomorph.trans c, ⟨mem_univ _, hxc⟩,
      hc.preimage e he he'⟩

end TauCeti
