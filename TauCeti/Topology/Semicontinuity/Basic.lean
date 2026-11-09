/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of suprema over neighbourhoods

A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s`, for an arbitrary `G : Set X → β` with values in a
complete linear order, is lower semicontinuous (`TauCeti.lowerSemicontinuous_iSup_nhds`): a strict
lower bound witnessed by a neighbourhood of `x` is witnessed by the same set at every point of its
interior. Lower envelopes and lower and upper Γ-limits are of this form.

For a lower semicontinuous `f` and a continuous `g` with values in a densely ordered linear
order, the set `{f ≤ g}` is closed (`LowerSemicontinuous.isClosed_setOf_le`). Sublevel sets of
lower semicontinuous functionals with a moving level, such as `{u | Φ(u) ≤ t - L(u)}` for a
continuous `L`, are of this form.
-/

public section

open Topology

namespace TauCeti

variable {X β : Type*} [TopologicalSpace X] [CompleteLinearOrder β]

/-- A function of the form `x ↦ ⨆ s ∈ 𝓝 x, G s` is lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_nhds (G : Set X → β) :
    LowerSemicontinuous fun x ↦ ⨆ s ∈ 𝓝 x, G s := by
  intro x c hc
  obtain ⟨s, hcs⟩ := lt_iSup_iff.1 hc
  obtain ⟨hs, hcs⟩ := lt_iSup_iff.1 hcs
  filter_upwards [eventually_mem_nhds_iff.2 hs] with y hy
  exact hcs.trans_le (le_iSup₂_of_le s hy le_rfl)

/-- If `f` is lower semicontinuous and `g` is continuous, with values in a densely ordered linear
order, then the set `{x | f x ≤ g x}` is closed. -/
theorem _root_.LowerSemicontinuous.isClosed_setOf_le {γ : Type*} [LinearOrder γ]
    [TopologicalSpace γ] [OrderTopology γ] [DenselyOrdered γ] {f g : X → γ}
    (hf : LowerSemicontinuous f) (hg : Continuous g) : IsClosed {x | f x ≤ g x} := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun x hx ↦ ?_)
  obtain ⟨r, hgr, hrf⟩ := exists_between (not_le.1 (show ¬f x ≤ g x from hx))
  exact ⟨{y | g y < r} ∩ f ⁻¹' Set.Ioi r,
    fun y hy ↦ show ¬f y ≤ g y from not_le.2 (hy.1.trans hy.2),
    (isOpen_lt hg continuous_const).inter (hf.isOpen_preimage r), hgr, hrf⟩

end TauCeti
