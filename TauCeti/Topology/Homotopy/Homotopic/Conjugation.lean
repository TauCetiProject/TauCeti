/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

/-!
# Pointed homotopies between inner automorphisms of topological groups

In a topological group `G`, a path `γ` from `w₁` to `w₂` yields the homotopy
`(t, x) ↦ γ t * x * (γ t)⁻¹` from `MulAut.conj w₁` to `MulAut.conj w₂` relative to `{(1 : G)}`.
Specializing to `w₁ = 1` shows that inner conjugation by any element joined to `1` — and hence by
every element when `G` is path-connected — is homotopic relative to `{(1 : G)}` to `id`.

## Main results

* `Joined.homotopicRel_conj`, `Joined.homotopicRel_id_conj`: pointed homotopies between inner
  conjugations along paths.
* `TauCeti.homotopicRel_conj`, `TauCeti.homotopicRel_id_conj`: path-connected specializations.
-/

public section

open scoped unitInterval

namespace Joined

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- Given `Joined w₁ w₂` in a topological group `G`, `MulAut.conj w₁` is homotopic relative to
`{(1 : G)}` to `MulAut.conj w₂`. -/
theorem homotopicRel_conj {w₁ w₂ : G} (hw : Joined w₁ w₂) :
    (⟨MulAut.conj w₁, IsTopologicalGroup.continuous_conj w₁⟩ : C(G, G)).HomotopicRel
      ⟨MulAut.conj w₂, IsTopologicalGroup.continuous_conj w₂⟩ {(1 : G)} := by
  obtain ⟨γ⟩ := hw
  -- `ContinuousMap.coe_mk` does not rewrite at `implicit` transparency here because
  -- `IsTopologicalGroup.continuous_conj w` unfolds `MulAut.conj w`.
  exact ⟨{
    toFun := fun tx : I × G ↦ γ tx.1 * tx.2 * (γ tx.1)⁻¹
    continuous_toFun := by fun_prop
    map_zero_left := fun x ↦ by
      simp only [Path.source]
      exact (MulAut.conj_apply w₁ x).symm
    map_one_left := fun x ↦ by
      simp only [Path.target]
      exact (MulAut.conj_apply w₂ x).symm
    prop' := fun t x hx ↦ by
      rw [Set.mem_singleton_iff.mp hx, ContinuousMap.coe_mk, mul_one, mul_inv_cancel]
      exact (MulAut.conj w₁).map_one.symm }⟩

/-- **Inner conjugation by an element in the identity path component is pointed-homotopic to the
identity.** -/
theorem homotopicRel_id_conj {w : G} (hw : Joined (1 : G) w) :
    (ContinuousMap.id G).HomotopicRel
      ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ {(1 : G)} := by
  have hid : (⟨MulAut.conj (1 : G), IsTopologicalGroup.continuous_conj (1 : G)⟩ : C(G, G)) =
      ContinuousMap.id G := ContinuousMap.ext fun _ ↦ by simp
  exact hid ▸ hw.homotopicRel_conj

end Joined

namespace TauCeti

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [PathConnectedSpace G]

/-- In a path-connected topological group, any two inner automorphisms are homotopic relative to
`{(1 : G)}`. -/
theorem homotopicRel_conj (w₁ w₂ : G) :
    (⟨MulAut.conj w₁, IsTopologicalGroup.continuous_conj w₁⟩ : C(G, G)).HomotopicRel
      ⟨MulAut.conj w₂, IsTopologicalGroup.continuous_conj w₂⟩ {(1 : G)} :=
  (PathConnectedSpace.joined w₁ w₂).homotopicRel_conj

/-- In a path-connected topological group, every inner automorphism is homotopic relative to
`{(1 : G)}` to the identity map. -/
theorem homotopicRel_id_conj (w : G) :
    (ContinuousMap.id G).HomotopicRel
      ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ {(1 : G)} :=
  (PathConnectedSpace.joined 1 w).homotopicRel_id_conj

end TauCeti
