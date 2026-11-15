/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic

/-!
# Examples of covers attached to fundamental-group sets

The left regular action of the fundamental group gives back the universal cover. The
comparison sends `⟦u, g⟧` to `g⁻¹ • u`, and its inverse sends `u` to `⟦u, 1⟧`. It commutes
with the projections to the base, so this identifies the covers, not just their total spaces.
The fundamental group carries the discrete topology as a label set.

The balanced-product construction also applies to arbitrary actions, including an action on a
one-point set. In that case its projection is a homeomorphism onto the base, so the construction
recovers the trivial one-sheeted cover. This needs only that the base is path connected and
locally path connected.

The construction for the regular action uses `TauCeti.BalancedProduct.homeomorphSelf`, without
any freeness or covering assumption. In particular, the comparison exists for the based-path
space even when the base does not satisfy the hypotheses for a universal covering map.

## References

* A. Hatcher, *Algebraic Topology*, §1.3 (coverings associated to fundamental-group actions).
-/

public section
noncomputable section

universe u

namespace TauCeti.UniversalCover

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

section RegularAction

variable [TopologicalSpace (FundamentalGroup X x₀)]
  [DiscreteTopology (FundamentalGroup X x₀)]

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

end RegularAction

section Subsingleton

variable (A : Type u) [MulAction (FundamentalGroup X x₀) A]

/-- The projection of the cover attached to a subsingleton action is injective. -/
theorem actionCoverProj_injective [Subsingleton A] :
    Function.Injective (actionCoverProj x₀ A) := by
  intro z w hzw
  induction z using Quotient.inductionOn with
  | h p =>
    induction w using Quotient.inductionOn with
    | h q =>
      rcases p with ⟨e, a⟩
      rcases q with ⟨e', a'⟩
      simp only [actionCoverProj_mk] at hzw
      obtain ⟨g, hg⟩ := proj_eq_iff_mem_orbit.mp hzw
      exact Quotient.sound ⟨g, Prod.ext hg (Subsingleton.elim _ _)⟩

variable [TopologicalSpace A] [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [Subsingleton A] [Nonempty A]

/-- The cover attached to an action on a one-point set is homeomorphic to its base by its
projection. -/
def actionCoverHomeomorphOfSubsingleton : ActionCover x₀ A ≃ₜ X :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (actionCoverProj x₀ A)
      ⟨actionCoverProj_injective x₀ A, actionCoverProj_surjective x₀ A⟩)
    (continuous_actionCoverProj x₀ A) (isOpenMap_actionCoverProj x₀ A)

/-- The one-point-cover homeomorphism is the projection of the associated cover. -/
@[simp]
theorem actionCoverHomeomorphOfSubsingleton_apply (z : ActionCover x₀ A) :
    actionCoverHomeomorphOfSubsingleton x₀ A z = actionCoverProj x₀ A z :=
  (rfl)

/-- The inverse one-point-cover homeomorphism sends an endpoint to the class of any lift with
that endpoint, paired with any label. -/
theorem actionCoverHomeomorphOfSubsingleton_symm_apply_proj (e : UniversalCover x₀) (a : A) :
    (actionCoverHomeomorphOfSubsingleton x₀ A).symm (proj e) =
      BalancedProduct.mk (FundamentalGroup X x₀) e a := by
  rw [Homeomorph.symm_apply_eq, actionCoverHomeomorphOfSubsingleton_apply, actionCoverProj_mk]

end Subsingleton

end TauCeti.UniversalCover
