/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Order.OrderUnit.Completion
public import TauCeti.Analysis.Normed.Order.OrderUnit.State.Basic
import TauCeti.Analysis.Normed.Operator.Completion

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
* `TauCeti.IsOrderUnitNorm.completionStateSpaceHomeomorph_val`,
  `completionStateSpaceHomeomorph_apply`,
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
  let ψ : WeakDual ℝ (UniformSpace.Completion E) :=
    StrongDual.toWeakDual ((toStrongDual φ).fromCompletion)
  have hψmem : ψ ∈ stateSpace (e : UniformSpace.Completion E) := by
    refine he.isOrderUnitNorm_completion.mem_stateSpace_iff_norm_eq_one_and_apply_eq_one.mpr
      ⟨?_, ?_⟩
    · simpa [ψ] using
        ((toStrongDual φ).norm_fromCompletion).trans (he.norm_toStrongDual_of_mem_stateSpace hφ)
    · simpa [ψ] using ((toStrongDual φ).fromCompletion_apply_coe e).trans
        (apply_eq_one_of_mem_stateSpace hφ)
  have hψeq : (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ = φ := by
    refine DFunLike.ext _ _ fun a => ?_
    simp [ψ, ContinuousLinearMap.pullbackFunctional_apply, UniformSpace.Completion.coe_toComplL]
  refine ⟨ψ, ⟨hψmem, hψeq⟩, fun ψ' ⟨_, hψ'eq⟩ => ?_⟩
  have huniq : (toStrongDual φ).fromCompletion = toStrongDual ψ' :=
    (toStrongDual φ).fromCompletion_unique (toStrongDual ψ') fun a => by
      have h := DFunLike.congr_fun hψ'eq a
      simpa [ContinuousLinearMap.pullbackFunctional_apply, UniformSpace.Completion.coe_toComplL]
        using h.symm
  exact DFunLike.ext _ _ fun x => by
    simpa [ψ] using (DFunLike.congr_fun huniq x).symm

private theorem IsOrderUnitNorm.mapsTo_pullbackFunctional_completion_stateSpace :
    MapsTo (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional
      (@stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
        (e : UniformSpace.Completion E)) (stateSpace e) :=
  letI : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).mapsTo_pullbackFunctional_stateSpace
    (fun _ _ hab => he.completion_coe_le_coe_iff.mpr hab) rfl

private noncomputable def IsOrderUnitNorm.completionStateFun :
    @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E) → stateSpace e :=
  fun ψ => ⟨(UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ.val,
    he.mapsTo_pullbackFunctional_completion_stateSpace ψ.property⟩

private noncomputable def IsOrderUnitNorm.completionStateEquiv :
    @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E) ≃ stateSpace e :=
  have hbij : Function.Bijective he.completionStateFun := by
    refine ⟨fun ψ₁ ψ₂ h => ?_, fun φ => ?_⟩
    · obtain ⟨_, _, huniq⟩ :=
        he.existsUnique_state_extension_completion (he.completionStateFun ψ₂).property
      have h1 : ψ₁.val = _ := huniq ψ₁.val ⟨ψ₁.property, congrArg Subtype.val h⟩
      have h2 : ψ₂.val = _ := huniq ψ₂.val ⟨ψ₂.property, rfl⟩
      exact Subtype.ext (h1.trans h2.symm)
    · obtain ⟨ψ, ⟨hψmem, hψeq⟩, _⟩ := he.existsUnique_state_extension_completion φ.property
      exact ⟨⟨ψ, hψmem⟩, Subtype.ext hψeq⟩
  Equiv.ofBijective he.completionStateFun hbij

private theorem IsOrderUnitNorm.completionStateEquiv_val
    (ψ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)) :
    (he.completionStateEquiv ψ).val =
      (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ.val :=
  rfl

private theorem IsOrderUnitNorm.continuous_completionStateEquiv :
    Continuous he.completionStateEquiv :=
  ((UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional.continuous.comp
    continuous_subtypeVal).subtype_mk _

/-- Restriction along `E → UniformSpace.Completion E` induces a weak-star homeomorphism between the
state space of the completion and `stateSpace e`. -/
noncomputable def IsOrderUnitNorm.completionStateSpaceHomeomorph :
    @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E) ≃ₜ stateSpace e :=
  letI : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  letI : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  letI : CompactSpace (stateSpace (e : UniformSpace.Completion E)) :=
    he.isOrderUnitNorm_completion.compactSpace_stateSpace
  Continuous.homeoOfEquivCompactToT2 he.continuous_completionStateEquiv

/-- The underlying functional of `completionStateSpaceHomeomorph ψ` is the pullback along
`UniformSpace.Completion.toComplL`. -/
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_val
    (ψ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)) :
    (he.completionStateSpaceHomeomorph ψ).val =
      (UniformSpace.Completion.toComplL (S := ℝ) (α := E)).pullbackFunctional ψ.val := by
  let : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  let : IsOrderedAddMonoid (UniformSpace.Completion E) := he.completionIsOrderedAddMonoid
  let : CompactSpace (stateSpace (e : UniformSpace.Completion E)) :=
    he.isOrderUnitNorm_completion.compactSpace_stateSpace
  rw [completionStateSpaceHomeomorph, ← Homeomorph.coe_toEquiv,
    Continuous.toEquiv_homeoOfEquivCompactToT2, he.completionStateEquiv_val]

/-- Evaluating `completionStateSpaceHomeomorph` restricts a completion state to `E`. -/
@[simp]
theorem IsOrderUnitNorm.completionStateSpaceHomeomorph_apply
    (ψ : @stateSpace (UniformSpace.Completion E) _ _ _ he.completionPartialOrder.toPreorder
      (e : UniformSpace.Completion E)) (a : E) :
    (he.completionStateSpaceHomeomorph ψ).val a = ψ.val (a : UniformSpace.Completion E) := by
  rw [he.completionStateSpaceHomeomorph_val, ContinuousLinearMap.pullbackFunctional_apply,
    UniformSpace.Completion.coe_toComplL]

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
      StrongDual.toWeakDual ((toStrongDual φ.val).fromCompletion) := by
  have huniq : (toStrongDual φ.val).fromCompletion =
      toStrongDual (he.completionStateSpaceHomeomorph.symm φ).val :=
    (toStrongDual φ.val).fromCompletion_unique _ fun a =>
      (he.completionStateSpaceHomeomorph_symm_apply φ a).symm
  exact DFunLike.ext _ _ fun x => (DFunLike.congr_fun huniq x).symm

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
