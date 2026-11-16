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
`(t, x) ↦ γ t * x * (γ t)⁻¹` from `MulAut.conj w₁` to `MulAut.conj w₂`, which fixes `1` at every
time `t`. Specializing to `w₁ = 1` shows that inner conjugation by any element joined to `1` — and
hence by every element when `G` is path-connected — is homotopic relative to `{(1 : G)}` to the
identity map.

## Main results

* `Joined.homotopicRel_conj`: if `Joined w₁ w₂`, then `MulAut.conj w₁` and `MulAut.conj w₂` are
  homotopic relative to `{(1 : G)}`.
* `Joined.homotopicRel_id_conj`: if `Joined (1 : G) w`, then `ContinuousMap.id G` and
  `MulAut.conj w` are homotopic relative to `{(1 : G)}`.
* `TauCeti.homotopicRel_conj`, `TauCeti.homotopicRel_id_conj`: path-connected specializations.
-/

public section

open scoped unitInterval

namespace Joined

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

private theorem coe_mk_conj_apply (w x : G) :
    (⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ : C(G, G)) x = w * x * w⁻¹ :=
  (congrFun (ContinuousMap.coe_mk (MulAut.conj w) (IsTopologicalGroup.continuous_conj w)) x).trans
    (MulAut.conj_apply w x)

/-- Given `Joined w₁ w₂` in a topological group `G`, `MulAut.conj w₁` is homotopic relative to
`{(1 : G)}` to `MulAut.conj w₂`. -/
theorem homotopicRel_conj {w₁ w₂ : G} (hw : Joined w₁ w₂) :
    (⟨MulAut.conj w₁, IsTopologicalGroup.continuous_conj w₁⟩ : C(G, G)).HomotopicRel
      ⟨MulAut.conj w₂, IsTopologicalGroup.continuous_conj w₂⟩ {(1 : G)} := by
  obtain ⟨γ⟩ := hw
  refine ⟨{ toFun := fun tx : I × G ↦ γ tx.1 * tx.2 * (γ tx.1)⁻¹
            continuous_toFun := by fun_prop
            map_zero_left := fun x ↦ by simp [coe_mk_conj_apply]
            map_one_left := fun x ↦ by simp [coe_mk_conj_apply]
            prop' := fun t x hx ↦ by
              rw [Set.mem_singleton_iff.mp hx]
              simp [coe_mk_conj_apply] }⟩

/-- **Inner conjugation by an element in the identity path component is pointed-homotopic to the
identity.** Given `Joined (1 : G) w` in a topological group `G`, `ContinuousMap.id G` is homotopic
relative to `{(1 : G)}` to `MulAut.conj w`. -/
theorem homotopicRel_id_conj {w : G} (hw : Joined (1 : G) w) :
    (ContinuousMap.id G).HomotopicRel
      ⟨MulAut.conj w, IsTopologicalGroup.continuous_conj w⟩ {(1 : G)} := by
  have hid :
      (⟨MulAut.conj (1 : G), IsTopologicalGroup.continuous_conj (1 : G)⟩ : C(G, G)) =
        ContinuousMap.id G := by
    ext x
    simp
  rw [← hid]
  exact hw.homotopicRel_conj

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
