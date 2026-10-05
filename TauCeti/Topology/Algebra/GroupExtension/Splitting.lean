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

Let `1 → N → E → G → 1` be an extension of groups with `E` and `G` topological and continuous
projection. A continuous homomorphism `σ : G →ₜ* E` whose composite with the projection, bundled as
a continuous homomorphism, is the identity of `G` is a splitting of the extension, and a continuous
one (`GroupExtension.exists_splitting_continuous_of_comp_eq_id`). Universal properties of
topological groups produce continuous homomorphisms `G →ₜ* E` and characterize them by an equality
of continuous homomorphisms out of `G`; this lemma turns such an equality into a continuous
splitting.

## Main results

* `GroupExtension.exists_splitting_continuous_of_comp_eq_id`: a continuous homomorphic right
  inverse of the projection is a continuous splitting.
-/

public section

namespace TauCeti

variable {N E G : Type*} [Group N] [Group E] [TopologicalSpace E] [Group G] [TopologicalSpace G]
  (S : GroupExtension N E G)

/-- **A continuous homomorphic right inverse of the projection splits the extension
continuously.** If `σ : G →ₜ* E` composed with the projection of `1 → N → E → G → 1`, bundled with
its continuity, is the identity of `G`, then `σ` is a continuous splitting of the extension. -/
theorem _root_.GroupExtension.exists_splitting_continuous_of_comp_eq_id
    (hrh : Continuous S.rightHom) (σ : G →ₜ* E)
    (hσ : (⟨S.rightHom, hrh⟩ : E →ₜ* G).comp σ = ContinuousMonoidHom.id G) :
    ∃ s : S.Splitting, Continuous ⇑s ∧ ∀ g, s g = σ g :=
  ⟨.mk σ.toMonoidHom fun g ↦ DFunLike.congr_fun hσ g, σ.continuous, fun _ ↦ rfl⟩

end TauCeti
