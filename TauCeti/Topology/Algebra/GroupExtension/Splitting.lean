/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupExtension.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous splittings of group extensions

Let `1 → N → E → G → 1` be an extension of groups with `E` and `G` topological. A continuous
homomorphism `σ : G →ₜ* E` whose composite with the projection is the identity of `G` gives a
continuous splitting (`GroupExtension.exists_splitting_continuous_of_comp_eq_id`). The right-inverse
equation is an equality of monoid homomorphisms, so continuity of the projection is not required.
Universal properties of topological groups produce continuous homomorphisms `G →ₜ* E`; this lemma
packages such a right inverse as a splitting while retaining its values.

## Main results

* `GroupExtension.exists_splitting_continuous_of_comp_eq_id`: a continuous homomorphic right
  inverse of the projection is a continuous splitting.
-/

public section

namespace TauCeti

variable {N E G : Type*} [Group N] [Group E] [TopologicalSpace E] [Group G] [TopologicalSpace G]
  (S : GroupExtension N E G)

/-- **A continuous homomorphic right inverse of the projection splits the extension
continuously.** If the underlying homomorphism of `σ : G →ₜ* E` composed with the projection of
`1 → N → E → G → 1` is the identity of `G`, then `σ` is a continuous splitting of the extension.
No continuity assumption on the projection is needed. -/
theorem _root_.GroupExtension.exists_splitting_continuous_of_comp_eq_id
    (σ : G →ₜ* E) (hσ : S.rightHom.comp σ.toMonoidHom = MonoidHom.id G) :
    ∃ s : S.Splitting, Continuous ⇑s ∧ ∀ g, s g = σ g :=
  ⟨.mk σ.toMonoidHom fun g ↦ DFunLike.congr_fun hσ g, σ.continuous, fun _ ↦ rfl⟩

end TauCeti
