/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopyClass

/-!
# The ambient homeomorphism action on ambient-isotopy classes

The geometric-topology roadmap uses ambient-isotopy classes as the point-set quotient layer
underlying later smooth and PL knot presentations. This file packages the already-defined
postcomposition by ambient homeomorphisms as a genuine group action of `Y ≃ₜ Y` on
`AmbientIsotopyClass X Y`.

The action is deliberately point-set topological: smooth and PL presentations can map to this
quotient and then use the ambient homeomorphism action, while stronger differentiable actions are
added only when their smooth or PL prerequisites are available.

## Main results

* `TauCeti.AmbientIsotopyClass.instMulAction`: the action of the ambient homeomorphism group.
* `TauCeti.AmbientIsotopyClass.smul_mk`: the representative formula for the action.
* `TauCeti.AmbientIsotopyClass.postcompHomeomorph_eq_smul`: the old postcomposition map is the
  scalar action.
-/

public section

namespace TauCeti

open ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace AmbientIsotopyClass

/-- The ambient homeomorphism group acts on ambient-isotopy classes by postcomposition. -/
instance instSMul : SMul (Y ≃ₜ Y) (AmbientIsotopyClass X Y) where
  smul h x := postcompHomeomorph h x

/-- The action of an ambient homeomorphism on an ambient-isotopy class is postcomposition. -/
@[simp]
theorem smul_def (h : Y ≃ₜ Y) (x : AmbientIsotopyClass X Y) :
    h • x = postcompHomeomorph h x :=
  rfl

private theorem one_eq_homeomorph_refl : (1 : Y ≃ₜ Y) = Homeomorph.refl Y := by
  ext y
  simp

/-- Ambient homeomorphisms act on ambient-isotopy classes by postcomposition. -/
instance instMulAction : MulAction (Y ≃ₜ Y) (AmbientIsotopyClass X Y) where
  one_smul x := by
    rw [smul_def, one_eq_homeomorph_refl]
    exact postcompHomeomorph_refl x
  mul_smul h k x := by
    rw [smul_def, smul_def, smul_def]
    exact (postcompHomeomorph_trans k h x).symm

/-- Postcomposition by an ambient homeomorphism is the scalar action of that homeomorphism. -/
theorem postcompHomeomorph_eq_smul (h : Y ≃ₜ Y) :
    postcompHomeomorph h = fun x : AmbientIsotopyClass X Y => h • x :=
  rfl

/-- The ambient homeomorphism action on representatives. -/
@[simp]
theorem smul_mk (h : Y ≃ₜ Y) (f : C(X, Y)) :
    h • mk f = mk ((h : C(Y, Y)).comp f) :=
  postcompHomeomorph_mk h f

/-- The equivalence induced by an ambient self-homeomorphism has the same forward map as the
ambient homeomorphism action. -/
@[simp]
theorem postcompHomeomorphEquiv_apply_eq_smul (h : Y ≃ₜ Y)
    (x : AmbientIsotopyClass X Y) :
    postcompHomeomorphEquiv h x = h • x := by
  refine induction_on x ?_
  intro f
  rw [postcompHomeomorphEquiv_mk, smul_mk]

end AmbientIsotopyClass

end TauCeti
