/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
import TauCeti.Topology.PathComponent

/-!
# Homotopies and homotopy equivalences of totally disconnected spaces

Paths in a totally disconnected space have equal endpoints, so evaluating a homotopy `H` between
continuous maps `f, g : C(X, Y)` into a totally disconnected space `Y` at any point `x : X` shows
`f x = g x`. Two continuous maps into a totally disconnected space are therefore homotopic if and
only if they are equal (`ContinuousMap.homotopic_iff_eq_of_totallyDisconnectedSpace`).

Consequently, a homotopy equivalence `X ≃ₕ Y` between totally disconnected spaces has genuine
two-sided inverses, hence upgrades to a homeomorphism `X ≃ₜ Y` with the same underlying maps
(`ContinuousMap.HomotopyEquiv.toHomeomorphOfTotallyDisconnectedSpace`), inverse to
`Homeomorph.toHomotopyEquiv`.

## Main definitions and results

* `ContinuousMap.Homotopic.eq_of_totallyDisconnectedSpace` and
  `ContinuousMap.homotopic_iff_eq_of_totallyDisconnectedSpace`: homotopic continuous maps into a
  totally disconnected space are equal.
* `ContinuousMap.HomotopyEquiv.toHomeomorphOfTotallyDisconnectedSpace`: a homotopy equivalence
  between totally disconnected spaces as a homeomorphism.
-/

public section

open scoped ContinuousMap

namespace ContinuousMap

section Homotopic

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]

/-- Two homotopic continuous maps into a totally disconnected space are equal. -/
theorem Homotopic.eq_of_totallyDisconnectedSpace {f g : C(X, Y)} (h : f.Homotopic g) : f = g := by
  ext x
  exact Joined.eq_of_totallyDisconnectedSpace ⟨h.some.evalAt x⟩

/-- Continuous maps into a totally disconnected space are homotopic if and only if they are
equal. -/
@[simp]
theorem homotopic_iff_eq_of_totallyDisconnectedSpace {f g : C(X, Y)} :
    f.Homotopic g ↔ f = g :=
  ⟨Homotopic.eq_of_totallyDisconnectedSpace, fun h ↦ h ▸ Homotopic.refl f⟩

end Homotopic

namespace HomotopyEquiv

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y] [TotallyDisconnectedSpace Z]

/-- A homotopy equivalence `e : X ≃ₕ Y` between totally disconnected spaces as a homeomorphism
`X ≃ₜ Y` with the same underlying forward and inverse maps. -/
def toHomeomorphOfTotallyDisconnectedSpace (e : X ≃ₕ Y) : X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x := DFunLike.congr_fun e.left_inv.eq_of_totallyDisconnectedSpace x
  right_inv y := DFunLike.congr_fun e.right_inv.eq_of_totallyDisconnectedSpace y
  continuous_toFun := e.toFun.continuous
  continuous_invFun := e.invFun.continuous

@[simp]
theorem coe_toHomeomorphOfTotallyDisconnectedSpace (e : X ≃ₕ Y) :
    ⇑e.toHomeomorphOfTotallyDisconnectedSpace = ⇑e :=
  (rfl)

@[simp]
theorem coe_toHomeomorphOfTotallyDisconnectedSpace_symm (e : X ≃ₕ Y) :
    ⇑e.toHomeomorphOfTotallyDisconnectedSpace.symm = ⇑e.symm :=
  (rfl)

@[simp]
theorem symm_toHomeomorphOfTotallyDisconnectedSpace (e : X ≃ₕ Y) :
    e.symm.toHomeomorphOfTotallyDisconnectedSpace = e.toHomeomorphOfTotallyDisconnectedSpace.symm :=
  (rfl)

@[simp]
theorem refl_toHomeomorphOfTotallyDisconnectedSpace :
    (HomotopyEquiv.refl X).toHomeomorphOfTotallyDisconnectedSpace = Homeomorph.refl X :=
  (rfl)

@[simp]
theorem trans_toHomeomorphOfTotallyDisconnectedSpace (e₁ : X ≃ₕ Y) (e₂ : Y ≃ₕ Z) :
    (e₁.trans e₂).toHomeomorphOfTotallyDisconnectedSpace =
      e₁.toHomeomorphOfTotallyDisconnectedSpace.trans e₂.toHomeomorphOfTotallyDisconnectedSpace :=
  (rfl)

@[simp]
theorem toHomeomorphOfTotallyDisconnectedSpace_toHomotopyEquiv (e : X ≃ₕ Y) :
    e.toHomeomorphOfTotallyDisconnectedSpace.toHomotopyEquiv = e :=
  HomotopyEquiv.ext rfl rfl

end HomotopyEquiv

end ContinuousMap

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TotallyDisconnectedSpace X] [TotallyDisconnectedSpace Y]

@[simp]
theorem toHomotopyEquiv_toHomeomorphOfTotallyDisconnectedSpace (h : X ≃ₜ Y) :
    h.toHomotopyEquiv.toHomeomorphOfTotallyDisconnectedSpace = h :=
  Homeomorph.ext fun _ ↦ rfl

end Homeomorph
