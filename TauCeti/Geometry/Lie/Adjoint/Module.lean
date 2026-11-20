/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Smooth
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Algebra.Lie.InvariantForm
import TauCeti.Geometry.Lie.Adjoint.InvariantForm

/-!
# The Lie algebra of a Lie group as a module for the adjoint action

A real Lie group `G` acts on its Lie algebra `𝔤 = GroupLieAlgebra I G` by the adjoint action
`Ad_g = d(x ↦ g x g⁻¹)₁` (`TauCeti.Lie.adjointContinuousLinearMap`). This file packages that
action as an instance on the type synonym `TauCeti.Lie.AdjointModule I G` of `𝔤`, so that `𝔤`
can be used as the model fibre of associated bundles, such as the adjoint bundle `P ×_G 𝔤` of a
principal `G`-bundle. The synonym keeps the action off the tangent space `GroupLieAlgebra I G`,
on which other groups act in other ways.

The synonym carries the normed space structure and the Lie bracket of `𝔤`, and the continuous
linear equivalence `TauCeti.Lie.AdjointModule.of` identifies it with `𝔤`. The action is a
smooth linear action by Lie algebra automorphisms:

* `g • of X = of (Ad_g X)` (`TauCeti.Lie.AdjointModule.smul_of`);
* the action is jointly smooth (`TauCeti.Lie.AdjointModule.instContMDiffSMul`);
* `g • ⁅X, Y⁆ = ⁅g • X, g • Y⁆` (`TauCeti.Lie.AdjointModule.smul_lie`), and a bilinear form
  invariant under the action is invariant under the bracket
  (`TauCeti.Lie.AdjointModule.lieInvariant_of_smul_invariant`);
* a commutative Lie group acts trivially (`TauCeti.Lie.AdjointModule.smul_eq_self`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter I, §4.
-/

public section

noncomputable section

namespace TauCeti.Lie

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (I G) in
/-- The Lie algebra `GroupLieAlgebra I G` of `G`, regarded as a `G`-module through the adjoint
action `g • X = Ad_g X` (`TauCeti.Lie.AdjointModule.smul_of`). This is a type synonym; the
identification with the Lie algebra is `TauCeti.Lie.AdjointModule.of`. -/
def AdjointModule : Type _ :=
  GroupLieAlgebra I G

namespace AdjointModule

/-! ### The normed space and the Lie algebra structure -/

/-- The norm of the adjoint module is the norm of the model space of `G`. -/
instance instNormedAddCommGroup : NormedAddCommGroup (AdjointModule I G) :=
  inferInstanceAs (NormedAddCommGroup E)

instance instNormedSpace : NormedSpace ℝ (AdjointModule I G) :=
  inferInstanceAs (NormedSpace ℝ E)

instance instFiniteDimensional [FiniteDimensional ℝ E] : FiniteDimensional ℝ (AdjointModule I G) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The identification of the Lie algebra of `G` with its adjoint module. -/
def of : GroupLieAlgebra I G ≃L[ℝ] AdjointModule I G :=
  -- The adjoint module is a type synonym of the Lie algebra, with the same linear structure.
  ContinuousLinearEquiv.refl ℝ E

variable [LieGroup I ∞ G]

section Lie

variable [CompleteSpace E]

/-- The adjoint module carries the Lie bracket of the Lie algebra of `G`. -/
instance instLieRing : LieRing (AdjointModule I G) :=
  inferInstanceAs (LieRing (GroupLieAlgebra I G))

instance instLieAlgebra : LieAlgebra ℝ (AdjointModule I G) :=
  inferInstanceAs (LieAlgebra ℝ (GroupLieAlgebra I G))

/-- The identification with the adjoint module preserves the Lie bracket. -/
@[simp]
theorem of_lie (X Y : GroupLieAlgebra I G) : of ⁅X, Y⁆ = ⁅of X, of Y⁆ :=
  -- Both brackets are the bracket of `GroupLieAlgebra I G`, read through the type synonym.
  (rfl)

/-- The inverse identification preserves the Lie bracket. -/
@[simp]
theorem of_symm_lie (X Y : AdjointModule I G) : of.symm ⁅X, Y⁆ = ⁅of.symm X, of.symm Y⁆ :=
  -- Both brackets are the bracket of `GroupLieAlgebra I G`, read through the type synonym.
  (rfl)

end Lie

/-! ### The adjoint action -/

/-- The adjoint action of `G` on its Lie algebra, `g • of X = of (Ad_g X)`. -/
instance instSMul : SMul G (AdjointModule I G) where
  smul g X := of (adjointContinuousLinearMap (I := I) g (of.symm X))

/-- The action on the adjoint module is the adjoint action on the Lie algebra. -/
@[simp]
theorem smul_of (g : G) (X : GroupLieAlgebra I G) :
    g • of X = of (adjointContinuousLinearMap (I := I) g X) := by
  -- Unfold the action, which is defined by transporting `Ad_g` through `of`.
  change of (adjointContinuousLinearMap (I := I) g (of.symm (of X))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- Reading the action back in the Lie algebra gives the adjoint action. -/
@[simp]
theorem of_symm_smul (g : G) (X : AdjointModule I G) :
    of.symm (g • X) = adjointContinuousLinearMap (I := I) g (of.symm X) := by
  obtain ⟨X, rfl⟩ := of.surjective X
  rw [smul_of, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The adjoint action is a linear action of `G` on its Lie algebra. -/
instance instDistribMulAction : DistribMulAction G (AdjointModule I G) where
  one_smul X := by
    obtain ⟨X, rfl⟩ := of.surjective X
    rw [smul_of, adjointContinuousLinearMap_one, ContinuousLinearMap.id_apply]
  mul_smul g h X := by
    obtain ⟨X, rfl⟩ := of.surjective X
    rw [smul_of, smul_of, smul_of, adjointContinuousLinearMap_mul, ContinuousLinearMap.comp_apply]
  smul_zero g := by
    rw [← map_zero (of (I := I) (G := G)), smul_of, map_zero, map_zero]
  smul_add g X Y := by
    obtain ⟨X, rfl⟩ := of.surjective X
    obtain ⟨Y, rfl⟩ := of.surjective Y
    rw [← map_add, smul_of, smul_of, smul_of, map_add, map_add]

instance instSMulCommClass : SMulCommClass G ℝ (AdjointModule I G) where
  smul_comm g c X := by
    obtain ⟨X, rfl⟩ := of.surjective X
    rw [← map_smul, smul_of, smul_of, map_smul, map_smul]

/-- The adjoint module is the model space of `G`, as a normed space. -/
private def modelEquiv : E ≃L[ℝ] AdjointModule I G :=
  ContinuousLinearEquiv.refl ℝ E

/-- The adjoint action is jointly smooth. -/
instance instContMDiffSMul :
    ContMDiffSMul I 𝓘(ℝ, AdjointModule I G) ∞ G (AdjointModule I G) where
  contMDiff_smul := by
    -- In the model space, the action applies the smoothly varying operator `Ad_g`.
    have h := (modelEquiv (I := I) (G := G)).contDiff.contMDiff.comp
      (((contMDiff_adjointContinuousLinearMap (I := I) (G := G)).comp contMDiff_fst).clm_apply
        ((modelEquiv (I := I) (G := G)).symm.contDiff.contMDiff.comp contMDiff_snd))
    -- Both sides are `Ad_g X`, read through the type synonyms of the model space.
    exact h.congr fun _ ↦ rfl

instance instContinuousSMul : ContinuousSMul G (AdjointModule I G) where
  continuous_smul := (ContMDiffSMul.contMDiff_smul (I := I)
    (I' := 𝓘(ℝ, AdjointModule I G)) (n := ∞)).continuous

/-- **The adjoint action is an action by Lie algebra automorphisms.** -/
@[simp]
theorem smul_lie [CompleteSpace E] (g : G) (X Y : AdjointModule I G) :
    g • ⁅X, Y⁆ = ⁅g • X, g • Y⁆ := by
  obtain ⟨X, rfl⟩ := of.surjective X
  obtain ⟨Y, rfl⟩ := of.surjective Y
  rw [← of_lie, smul_of, smul_of, smul_of, adjointContinuousLinearMap_lie, of_lie]

/-- **`Ad`-invariant bilinear forms are `ad`-invariant**: a bilinear form on the adjoint module
invariant under the action of `G` satisfies `β ⁅X, Y⁆ Z = -β Y ⁅X, Z⁆`. This is
`TauCeti.Lie.lieInvariant_of_adjoint_invariant`, read through the type synonym. -/
theorem lieInvariant_of_smul_invariant [CompleteSpace E] [FiniteDimensional ℝ E]
    {β : AdjointModule I G →L[ℝ] AdjointModule I G →L[ℝ] ℝ}
    (hβ : ∀ (g : G) (X Y : AdjointModule I G), β (g • X) (g • Y) = β X Y) :
    β.toBilinForm.lieInvariant (AdjointModule I G) :=
  -- The adjoint module has the topology, linear structure and bracket of `GroupLieAlgebra I G`,
  -- and its action is the adjoint action, so `β` is an `Ad`-invariant form on the Lie algebra.
  lieInvariant_of_adjoint_invariant (I := I) (G := G) (b := β) fun g Y Z ↦ hβ g Y Z

/-- A commutative Lie group acts trivially on its Lie algebra. -/
@[simp]
theorem smul_eq_self [IsMulCommutative G] (g : G) (X : AdjointModule I G) : g • X = X := by
  obtain ⟨X, rfl⟩ := of.surjective X
  rw [smul_of, adjointContinuousLinearMap_eq_id, ContinuousLinearMap.id_apply]

end AdjointModule

end TauCeti.Lie
