/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Adding a constant parameter to a bounded continuous function

The map `(p, f) ↦ (t ↦ (p, f t))` is continuous linear for the sup norms. It lets
superposition operators on a product space express joint dependence on a parameter and a
bounded continuous function, without placing a norm on an unbounded parameterized family.
-/

public section

namespace BoundedContinuousFunction

variable (𝕜 α E X : Type*) [NontriviallyNormedField 𝕜] [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Adjoin a constant parameter to a bounded continuous function, as a continuous linear map. -/
noncomputable def parameterLift : E × (α →ᵇ X) →L[𝕜] (α →ᵇ (E × X)) :=
  LinearMap.mkContinuous
    { toFun := fun p ↦ ofNormedAddCommGroup (fun t ↦ (p.1, p.2 t))
        (continuous_const.prodMk p.2.continuous) ‖p‖ fun t ↦ by
          exact max_le_max le_rfl (p.2.norm_coe_le_norm t)
      map_add' := fun _ _ ↦ by ext t <;> rfl
      map_smul' := fun _ _ ↦ by ext t <;> rfl }
    1 fun p ↦ (norm_ofNormedAddCommGroup_le _ (norm_nonneg p)
      (fun t ↦ max_le_max le_rfl (p.2.norm_coe_le_norm t))).trans_eq (one_mul ‖p‖).symm

/-- The parameter lift is pointwise pairing with the constant parameter. -/
@[simp]
theorem parameterLift_apply (p : E × (α →ᵇ X)) (t : α) :
    parameterLift 𝕜 α E X p t = (p.1, p.2 t) :=
  (rfl)

end BoundedContinuousFunction
