/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod

/-!
# Charts straightening the labelled faces of a corner domain

Let `ρ : ι → M → ℝ` be finitely many functions on a space `M`, continuous at a point `x` of the
corner domain `{y | ∀ i, 0 ≤ ρ i y}`, and let `s` be a set of labels active at `x`. The labelled
face of `s` is `{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}`.

Suppose a chart `χ` centred at `x` reads the labels active at `x` as the coordinates of a
continuous linear map `q`. Then near `0`, the inverse of `χ` maps the cone on which `q` is
nonnegative, inside the kernel of the coordinates labelled by `s`, into the face of `s`
(`OpenPartialHomeomorph.tendsto_symm_nhdsWithin_face`). The labels inactive at `x` stay positive
near `x` and do not constrain the face there. So a germ condition on the face pulls back along
the chart to a germ condition on a cone in a linear subspace, where linear algebra applies.
-/

public section

open Set Filter Topology

namespace OpenPartialHomeomorph

variable {E M ι : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [TopologicalSpace M] [Finite ι]

/-- Near `x`, the inverse of a chart centred at `x` in which the defining functions active at `x`
are the coordinates `q` maps the cone of `ker qs` on which `q` is nonnegative into the face of
`s`. Here `qs` collects the coordinates labelled by `s`, and the inactive defining functions stay
positive near `x`. -/
theorem tendsto_symm_nhdsWithin_face (χ : OpenPartialHomeomorph M E) {x : M}
    (hxχ : x ∈ χ.source) (hχx : χ x = 0) {ρ : ι → M → ℝ} (hρ : ∀ i, ContinuousAt (ρ i) x)
    {s : Set ι} (hxD : ∀ i, 0 ≤ ρ i x) (hxs : ∀ i ∈ s, ρ i x = 0)
    {q : E →L[ℝ] {i // ρ i x = 0} → ℝ}
    (hρχ : ∀ v ∈ χ.target, ∀ a : {i // ρ i x = 0}, ρ a (χ.symm v) = q v a) :
    Tendsto (fun v : (ContinuousLinearMap.pi fun a : {a : {i // ρ i x = 0} | (a : ι) ∈ s} ↦
        (ContinuousLinearMap.proj (a : {i // ρ i x = 0})).comp q).ker ↦ χ.symm (v : E))
      (𝓝[{v | ∀ a, 0 ≤ q v a}] 0) (𝓝[{y | (∀ i, 0 ≤ ρ i y) ∧ ∀ i ∈ s, ρ i y = 0}] x) := by
  have h0χ : (0 : E) ∈ χ.target := hχx ▸ χ.map_source hxχ
  have hval := continuous_subtypeVal.tendsto (0 : (ContinuousLinearMap.pi fun a :
    {a : {i // ρ i x = 0} | (a : ι) ∈ s} ↦ (ContinuousLinearMap.proj (a : {i // ρ i x = 0})).comp
      q).ker)
  have hT := (χ.continuousAt_symm h0χ).tendsto.comp hval
  rw [Function.comp_def, ← hχx, χ.left_inv hxχ] at hT
  have hinact : ∀ᶠ y in 𝓝 x, ∀ i, ρ i x ≠ 0 → 0 < ρ i y := eventually_all.mpr fun i ↦ by
    by_cases hi : ρ i x = 0
    · exact Eventually.of_forall fun _ h ↦ (h hi).elim
    · filter_upwards [continuousAt_const.eventually_lt (hρ i) ((hxD i).lt_of_ne' hi)]
        with y hy _ using hy
  refine tendsto_nhdsWithin_iff.mpr ⟨hT.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (hval.eventually (χ.open_target.mem_nhds h0χ)),
    nhdsWithin_le_nhds (hT.eventually hinact), self_mem_nhdsWithin] with v hvt hvpos hvS
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_⟩
  · by_cases hi : ρ i x = 0
    · exact (hρχ v hvt ⟨i, hi⟩).symm ▸ hvS ⟨i, hi⟩
    · exact (hvpos i hi).le
  · rw [hρχ v hvt ⟨i, hxs i hi⟩]
    exact ContinuousLinearMap.mem_ker_pi_proj_comp.mp v.property ⟨i, hxs i hi⟩ hi

end OpenPartialHomeomorph
