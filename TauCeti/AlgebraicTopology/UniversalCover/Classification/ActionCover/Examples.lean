/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic

/-!
# The associated cover of the regular action

The left regular action of the fundamental group gives back the universal cover. The
comparison sends `⟦u, g⟧` to `g⁻¹ • u`, and its inverse sends `u` to `⟦u, 1⟧`. It commutes
with the projections to the base, so this identifies the covers, not just their total spaces.
The fundamental group carries the discrete topology as a label set.

The construction uses `TauCeti.BalancedProduct.homeomorphSelf`, without any freeness or
covering assumption. In particular, the comparison exists for the based-path space even
when the base does not satisfy the hypotheses for a universal covering map.

## References

* A. Hatcher, *Algebraic Topology*, §1.3 (coverings associated to fundamental-group actions).
-/

public section
noncomputable section

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] (x₀ : X)
  [TopologicalSpace (FundamentalGroup X x₀)] [DiscreteTopology (FundamentalGroup X x₀)]

local instance : ContinuousSMul (FundamentalGroup X x₀) (UniversalCover x₀) :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

/-- The associated cover of the left regular fundamental-group action is the universal
cover, by sending `⟦u, g⟧` to `g⁻¹ • u`. -/
def actionCoverRegularHomeomorph :
    ActionCover x₀ (FundamentalGroup X x₀) ≃ₜ UniversalCover x₀ :=
  BalancedProduct.homeomorphSelf

/-- The regular-action comparison applies the inverse label to the universal-cover point. -/
@[simp]
theorem actionCoverRegularHomeomorph_mk (u : UniversalCover x₀)
    (g : FundamentalGroup X x₀) :
    actionCoverRegularHomeomorph x₀ (BalancedProduct.mk (FundamentalGroup X x₀) u g) =
      g⁻¹ • u := by
  rw [actionCoverRegularHomeomorph, BalancedProduct.homeomorphSelf_mk]

/-- The inverse regular-action comparison attaches the identity label. -/
@[simp]
theorem actionCoverRegularHomeomorph_symm_apply (u : UniversalCover x₀) :
    (actionCoverRegularHomeomorph x₀).symm u =
      BalancedProduct.mk (FundamentalGroup X x₀) u 1 := by
  rw [actionCoverRegularHomeomorph, BalancedProduct.homeomorphSelf_symm_apply]

/-- The regular-action comparison is over the base space. -/
@[simp]
theorem proj_actionCoverRegularHomeomorph
    (z : ActionCover x₀ (FundamentalGroup X x₀)) :
    proj (actionCoverRegularHomeomorph x₀ z) =
      actionCoverProj x₀ (FundamentalGroup X x₀) z := by
  induction z using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨u, g⟩
    simp only [actionCoverRegularHomeomorph_mk, proj_smul, actionCoverProj_mk]

end TauCeti.UniversalCover
