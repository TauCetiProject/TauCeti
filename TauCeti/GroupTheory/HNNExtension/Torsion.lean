/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.HNNExtension
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Torsion
import TauCeti.GroupTheory.GraphOfGroups.OneEdge

/-!
# HNN extensions of torsion-free groups are torsion-free

The HNN extension `⟨G, t | t a t⁻¹ = φ a⟩` of a group `G` along an isomorphism `φ : A ≃* B` of two
subgroups is the fundamental group of the loop of groups with vertex group `G` and edge maps the
inclusion of `A` and `a ↦ φ a` (`TauCeti.GraphOfGroups.π₁Tree.equivHNNExtensionOfMulEquiv`).
The fundamental group of a graph of torsion-free groups is torsion-free
(`TauCeti.GraphOfGroups.π₁Tree.isMulTorsionFree`), since its elements of finite order are
conjugate into vertex groups, so an HNN extension of a torsion-free group is torsion-free.

## Main results

* `HNNExtension.instIsMulTorsionFree`: an HNN extension of a torsion-free group is torsion-free.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12 (the Bass–Serre tree and its vertex
  stabilizers).
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Chapter IV, Theorem 2.4 (elements of
  finite order of an HNN extension are conjugate into the base group).
-/

public section

namespace HNNExtension

open TauCeti GraphOfGroups

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

/-- **HNN extensions of torsion-free groups are torsion-free.** The HNN extension
`⟨G, t | t a t⁻¹ = φ a⟩` of a torsion-free group `G` along an isomorphism `φ : A ≃* B` of two
subgroups is torsion-free. -/
instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree (HNNExtension G A B φ) := by
  let 𝔸 := loop A.subtype (B.subtype.comp (φ : A →* B)) A.subtype_injective
    (B.subtype_injective.comp φ.injective)
  have : ∀ b, IsMulTorsionFree (𝔸.vertexGroup b) := fun _ ↦ inferInstanceAs (IsMulTorsionFree G)
  have h := π₁Tree.isMulTorsionFree (𝔸 := 𝔸) (SerreGraph.roseTree Unit)
  rw [SerreGraph.roseTree_darts] at h
  exact (π₁Tree.equivHNNExtensionOfMulEquiv φ).symm.injective.isMulTorsionFree
    (π₁Tree.equivHNNExtensionOfMulEquiv φ).symm.toMonoidHom

end HNNExtension
