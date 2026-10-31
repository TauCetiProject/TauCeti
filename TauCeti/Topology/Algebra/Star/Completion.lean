/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Star
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Star operations on completions

A star operation extends to the completion through `UniformSpace.Completion.map`, and the
extension is continuous. An additive, continuous star operation on a uniform additive group is
uniformly continuous, `TauCeti.uniformContinuous_star`, so its extension agrees with it on the
image of the group, `UniformSpace.Completion.coe_star`. The star monoid and star module laws then
pass to the completion. No ring structure is involved; the star ring structure on completions of
nonunital rings is `UniformSpace.Completion.instStarRing` in
`TauCeti.Topology.Algebra.UniformRing`.

## Main results

* `TauCeti.uniformContinuous_star`: an additive, continuous star operation on a uniform additive
  group is uniformly continuous.
* `UniformSpace.Completion.instStar` and `UniformSpace.Completion.instContinuousStar`: the
  continuous star operation on the completion.
* `UniformSpace.Completion.coe_star`: the inclusion into the completion commutes with star.
* `UniformSpace.Completion.instStarAddMonoid` and `UniformSpace.Completion.instStarModule`: the
  star additive monoid and star module laws pass to the completion.
-/

public section

noncomputable section

/-- An additive, continuous star operation on a uniform additive group is uniformly continuous. -/
theorem TauCeti.uniformContinuous_star {α : Type*} [UniformSpace α] [AddGroup α]
    [IsUniformAddGroup α] [StarAddMonoid α] [ContinuousStar α] :
    UniformContinuous (star : α → α) :=
  uniformContinuous_addMonoidHom_of_continuous (f := (starAddEquiv : α ≃+ α).toAddMonoidHom)
    continuous_star

namespace UniformSpace.Completion

variable {α : Type*} [UniformSpace α]

/-- The star operation on the completion: the completion of the star operation of `α`. -/
instance instStar [Star α] : Star (Completion α) :=
  ⟨Completion.map star⟩

/-- The extended star operation is continuous, whatever the star operation of `α`. -/
instance instContinuousStar [Star α] : ContinuousStar (Completion α) :=
  ⟨Completion.continuous_map⟩

variable [AddGroup α] [IsUniformAddGroup α] [StarAddMonoid α] [ContinuousStar α]

/-- The inclusion into the completion commutes with an additive, continuous star operation. -/
@[simp, norm_cast]
theorem coe_star (a : α) : ((star a : α) : Completion α) = star (a : Completion α) :=
  (map_coe TauCeti.uniformContinuous_star a).symm

/-- The completion of a uniform additive group with an additive, continuous star operation is a
star additive monoid. -/
instance instStarAddMonoid : StarAddMonoid (Completion α) where
  star_involutive a :=
    Completion.induction_on a (isClosed_eq (by fun_prop) continuous_id)
      fun a => by rw [← coe_star, ← coe_star, star_star]
  star_add a b :=
    Completion.induction_on₂ a b (isClosed_eq (by fun_prop) (by fun_prop))
      fun a b => by rw [← coe_add, ← coe_star, ← coe_star, ← coe_star, ← coe_add, star_add]

/-- A star module structure on `α` passes to the completion. -/
instance instStarModule {R : Type*} [Monoid R] [Star R] [DistribMulAction R α]
    [UniformContinuousConstSMul R α] [StarModule R α] : StarModule R (Completion α) where
  star_smul r a :=
    Completion.induction_on a (isClosed_eq (by fun_prop) (by fun_prop))
      fun a => by rw [← coe_smul, ← coe_star, ← coe_star, ← coe_smul, star_smul]

end UniformSpace.Completion
