/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.UrysohnsLemma

/-!
# Neighbourhood compression in a topological cylinder

Over a normal space `X`, any open neighbourhood `W ⊆ X × I` of `(s ×ˢ univ) ∪ (univ ×ˢ {0})` for a
closed set `s ⊆ X` receives a fibrewise continuous self-map of `X × I` fixing
`(s ×ˢ univ) ∪ (univ ×ˢ {0})` (`TauCeti.exists_continuousMap_cylinder_compression`). The map acts as
`(x, t) ↦ (x, ρ x * t)` for a Urysohn cutoff `ρ` supported in the tube neighbourhood
`{x | {x} ×ˢ univ ⊆ W}`.
-/

public section

open Set
open scoped unitInterval

namespace TauCeti

/-- Given a closed set `s ⊆ X` and an open neighbourhood `W ⊆ X × I` of
`(s ×ˢ univ) ∪ (univ ×ˢ {0})` over a normal base `X`, a Urysohn cutoff on the tube neighbourhood
`{x | {x} ×ˢ univ ⊆ W}` maps `X × I` continuously into `W` via `(x, t) ↦ (x, ρ x * t)`, fixing
`X × {0}` and `s × I`. -/
theorem exists_continuousMap_cylinder_compression {X : Type*} [TopologicalSpace X]
    [NormalSpace X] {s : Set X} (hs : IsClosed s) {W : Set (X × I)} (hW : IsOpen W)
    (hsW : s ×ˢ (univ : Set I) ⊆ W) (h0W : (univ : Set X) ×ˢ {(0 : I)} ⊆ W) :
    ∃ r : C(X × I, X × I), (∀ q, (r q).1 = q.1) ∧ (∀ q, r q ∈ W) ∧
      (∀ x, r (x, 0) = (x, 0)) ∧ ∀ x ∈ s, ∀ t : I, r (x, t) = (x, t) := by
  let U : Set X := {x | ({x} : Set X) ×ˢ (univ : Set I) ⊆ W}
  have hU : IsOpen U := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨u, v, huo, _, hxu, htv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton isCompact_univ hW hx
    exact ⟨u, fun y hy _ ⟨rfl, _⟩ ↦ huv ⟨hy, htv (mem_univ _)⟩, huo, hxu (mem_singleton x)⟩
  have hsU : s ⊆ U := fun x hx _ ⟨hy, ht⟩ ↦ hsW ⟨hy.symm ▸ hx, ht⟩
  obtain ⟨ρ, hρ₀, hρ₁, hρI⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl hs
    (disjoint_compl_left_iff_subset.2 hsU)
  refine ⟨⟨fun q ↦ (q.1, ⟨ρ q.1 * q.2.val, unitInterval.mul_mem (hρI q.1) q.2.property⟩),
      continuous_fst.prodMk
        (((ρ.continuous.comp continuous_fst).mul
          (continuous_subtypeVal.comp continuous_snd)).subtype_mk _)⟩,
    fun _ ↦ rfl, fun q ↦ ?_, fun x ↦ Prod.ext rfl (Subtype.ext (mul_zero _)),
    fun x hx t ↦ Prod.ext rfl (Subtype.ext (by simp [hρ₁ hx]))⟩
  by_cases hq : q.1 ∈ U
  · exact hq ⟨mem_singleton _, mem_univ _⟩
  · have h0 : ρ q.1 = 0 := hρ₀ hq
    have hq0 :
        (q.1, (⟨ρ q.1 * q.2.val, unitInterval.mul_mem (hρI q.1) q.2.property⟩ : I)) = (q.1, 0) :=
      Prod.ext rfl (Subtype.ext (by simp [h0]))
    simpa only [ContinuousMap.coe_mk, hq0] using h0W ⟨mem_univ _, mem_singleton _⟩

end TauCeti
