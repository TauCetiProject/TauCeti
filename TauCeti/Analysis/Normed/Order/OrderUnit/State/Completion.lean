/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.OrderUnit.Completion
public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic

/-!
# Extension of order-unit states to the norm completion

Every state on an order-unit space `(E, e)` extends uniquely to a state on the norm completion
`UniformSpace.Completion E`, inducing a weak-star homeomorphism
`TauCeti.IsOrderUnitNorm.completionStateSpaceHomeomorph` that preserves convex combinations.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.existsUnique_state_extension_completion`: every state on `E` extends
  uniquely to a state on `UniformSpace.Completion E`.
* `TauCeti.IsOrderUnitNorm.completionStateSpaceHomeomorph`: weak-star homeomorphism between
  the state space of `UniformSpace.Completion E` and `TauCeti.OrderUnit.stateSpace e`.
* `TauCeti.IsOrderUnitNorm.completionStateSpaceHomeomorph_apply`,
  `completionStateSpaceHomeomorph_symm_apply`, `completionStateSpaceHomeomorph_symm_val`,
  `completionStateSpaceHomeomorph_convexCombo`,
  `completionStateSpaceHomeomorph_symm_convexCombo`: evaluation, inverse characterization, and
  preservation of convex combinations.

## References

* Marc A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, Section 1.
* Richard V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set WeakDual

namespace TauCeti

section CompletionStates

open OrderUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- **Unique extension of states to the norm completion.** Every state on an order-unit space `E`
extends uniquely to a state on `UniformSpace.Completion E`. -/
theorem IsOrderUnitNorm.existsUnique_state_extension_completion {φ : WeakDual ℝ E}
    (hφ : φ ∈ stateSpace e) :
    ∃! ψ ∈ @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E),
      (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ = φ := by
  let : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  have : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  obtain ⟨ψ, hψmem, hψeq⟩ := he.surjOn_pullbackFunctional_stateSpace he.isOrderUnitNorm_completion
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℝ) (E := E)) rfl hφ
  refine ⟨ψ, ⟨hψmem, hψeq⟩, fun ψ' ⟨_, hψ'eq⟩ => DFunLike.ext _ _ ?_⟩
  have hagree : ∀ a : E, ψ' (a : UniformSpace.Completion E) = ψ (a : UniformSpace.Completion E) :=
    fun a => by
      have h1 := DFunLike.congr_fun hψ'eq a
      have h2 := DFunLike.congr_fun hψeq a
      simpa [ContinuousLinearMap.pullbackFunctional_apply, UniformSpace.Completion.coe_toComplL]
        using h1.trans h2.symm
  exact congrFun (UniformSpace.Completion.denseRange_coe.equalizer
    (toStrongDual ψ').continuous (toStrongDual ψ).continuous (funext hagree))

/-- Restriction along `E → UniformSpace.Completion E` induces a weak-star homeomorphism between the
state space of the completion and `stateSpace e`. -/
noncomputable def IsOrderUnitNorm.completionStateSpaceHomeomorph :
    @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E) ≃ₜ stateSpace e := by
  letI : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  haveI : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  have hcompl := he.isOrderUnitNorm_completion
  haveI : CompactSpace (stateSpace (e : UniformSpace.Completion E)) :=
    hcompl.compactSpace_stateSpace
  let T := UniformSpace.Completion.toComplL (S := ℝ) (α := E)
  have hTmono : Monotone T := fun a b hab => he.completion_coe_le_coe_iff.mpr hab
  have hmaps : MapsTo T.pullbackFunctional
      (stateSpace (e : UniformSpace.Completion E)) (stateSpace e) :=
    T.mapsTo_pullbackFunctional_stateSpace hTmono rfl
  let f : stateSpace (e : UniformSpace.Completion E) → stateSpace e :=
    fun ψ => ⟨T.pullbackFunctional ψ.val, hmaps ψ.property⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun ψ₁ ψ₂ h => ?_, fun φ => ?_⟩
    · obtain ⟨_, _, huniq⟩ := he.existsUnique_state_extension_completion (f ψ₂).property
      have h1 : ψ₁.val = _ := huniq ψ₁.val ⟨ψ₁.property, congrArg Subtype.val h⟩
      have h2 : ψ₂.val = _ := huniq ψ₂.val ⟨ψ₂.property, rfl⟩
      exact Subtype.ext (h1.trans h2.symm)
    · obtain ⟨ψ, ⟨hψmem, hψeq⟩, _⟩ := he.existsUnique_state_extension_completion φ.property
      exact ⟨⟨ψ, hψmem⟩, Subtype.ext hψeq⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
    ((T.pullbackFunctional.continuous.comp continuous_subtypeVal).subtype_mk _)

/-- Evaluating `completionStateSpaceHomeomorph` restricts a completion state to `E`. -/
@[simp]
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_apply
    (ψ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)) (a : E) :
    (he.completionStateSpaceHomeomorph ψ).val a = ψ.val (a : UniformSpace.Completion E) := by
  change (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ.val a = _
  simp

/-- Evaluating the inverse of `completionStateSpaceHomeomorph` on a coerced element recovers the
original state. -/
@[simp]
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_symm_apply
    (φ : stateSpace e) (a : E) :
    (he.completionStateSpaceHomeomorph.symm φ).val (a : UniformSpace.Completion E) = φ.val a := by
  rw [← he.completionStateSpaceHomeomorph_apply,
    he.completionStateSpaceHomeomorph.apply_symm_apply]

/-- The inverse of `completionStateSpaceHomeomorph` has underlying functional
`StrongDual.toWeakDual ((toStrongDual φ.val).fromCompletion)`. -/
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_symm_val (φ : stateSpace e) :
    (he.completionStateSpaceHomeomorph.symm φ).val =
      StrongDual.toWeakDual ((toStrongDual φ.val).fromCompletion) :=
  DFunLike.ext _ _ fun x => congrFun (UniformSpace.Completion.denseRange_coe.equalizer
    (toStrongDual (he.completionStateSpaceHomeomorph.symm φ).val).continuous
    (toStrongDual φ.val).fromCompletion.continuous
    (funext fun a => (he.completionStateSpaceHomeomorph_symm_apply φ a).trans
      ((toStrongDual φ.val).fromCompletion_apply_coe a).symm)) x

/-- `completionStateSpaceHomeomorph` preserves convex combinations of states. -/
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_convexCombo
    {ψ₁ ψ₂ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)}
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    he.completionStateSpaceHomeomorph
        ⟨s • ψ₁.val + t • ψ₂.val,
          @convex_stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
            (e : UniformSpace.Completion E) ψ₁.val ψ₁.property ψ₂.val ψ₂.property
            s t hs ht hst⟩ =
      ⟨s • (he.completionStateSpaceHomeomorph ψ₁).val +
          t • (he.completionStateSpaceHomeomorph ψ₂).val,
        convex_stateSpace (he.completionStateSpaceHomeomorph ψ₁).property
          (he.completionStateSpaceHomeomorph ψ₂).property hs ht hst⟩ := by
  refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
  simp

/-- The inverse of `completionStateSpaceHomeomorph` preserves convex combinations of states. -/
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_symm_convexCombo
    {φ₁ φ₂ : stateSpace e} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) :
    he.completionStateSpaceHomeomorph.symm
        ⟨s • φ₁.val + t • φ₂.val, convex_stateSpace φ₁.property φ₂.property hs ht hst⟩ =
      ⟨s • (he.completionStateSpaceHomeomorph.symm φ₁).val +
          t • (he.completionStateSpaceHomeomorph.symm φ₂).val,
        @convex_stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
          (e : UniformSpace.Completion E) (he.completionStateSpaceHomeomorph.symm φ₁).val
          (he.completionStateSpaceHomeomorph.symm φ₁).property
          (he.completionStateSpaceHomeomorph.symm φ₂).val
          (he.completionStateSpaceHomeomorph.symm φ₂).property s t hs ht hst⟩ := by
  apply he.completionStateSpaceHomeomorph.injective
  rw [he.completionStateSpaceHomeomorph.apply_symm_apply,
    he.completionStateSpaceHomeomorph_convexCombo hs ht hst]
  simp

end CompletionStates

end TauCeti
