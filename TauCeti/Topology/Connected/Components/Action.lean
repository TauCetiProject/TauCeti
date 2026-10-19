/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Actions on connected components

An action by continuous maps descends to connected components. This allows geometric
symmetries of a space, such as Galois symmetries of a spectrum, to act on its components.
-/

public section

namespace ConnectedComponents

variable {G X : Type*} [Monoid G] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X]

/-- An action by continuous maps induces an action on connected components. -/
noncomputable instance instMulActionOfContinuousConstSMul :
    MulAction G (ConnectedComponents X) where
  smul g := (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap
  one_smul x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (one_smul G x)
  mul_smul g h x := by
    obtain ⟨x, rfl⟩ := surjective_coe x
    exact congrArg ConnectedComponents.mk (mul_smul g h x)

/-- The action on components sends the component of a point to that of its translate. -/
@[simp]
theorem smul_mk (g : G) (x : X) :
    g • ConnectedComponents.mk x = ConnectedComponents.mk (g • x) := (rfl)

/-- Each fixed element still acts continuously on the quotient space of components. -/
instance : ContinuousConstSMul G (ConnectedComponents X) where
  continuous_const_smul g :=
    (continuous_const_smul g : Continuous (fun x : X ↦ g • x)).connectedComponentsMap_continuous

end ConnectedComponents
