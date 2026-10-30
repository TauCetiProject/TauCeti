/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Homotopy equivalences: path connectedness and products

A homotopy equivalence `e : X ≃ₕ Y` is not surjective, so path connectedness of `Y` cannot be
read off from the image of a path in `X`. What replaces surjectivity is the trace of the
homotopy `e.toFun ∘ e.invFun ≃ id`: evaluated at a point `y`, it is a path from
`e.toFun (e.invFun y)` to `y`. Two points of `Y` are therefore joined to points in the image of
`e.toFun`, which are joined to each other because `X` is path connected.

This is the prerequisite for the base-point-free homotopy-group statements in
`TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv`, which need the target space to be path
connected before base-point change is available there. The file also records that the product
`ContinuousMap.HomotopyEquiv.prodCongr` of two homotopy equivalences acts componentwise, and that
the projection `X × Y → X` is a homotopy equivalence when `Y` is contractible.

## Main declarations

* `ContinuousMap.HomotopyEquiv.pathConnectedSpace`: a space homotopy equivalent to a path
  connected space is path connected.
* `ContinuousMap.HomotopyEquiv.prodCongr_apply`: the product of two homotopy equivalences acts
  componentwise.
* `ContinuousMap.HomotopyEquiv.prodContractible`: the homotopy equivalence `X × Y ≃ₕ X` given by
  the projection, for `Y` contractible.
-/

public section

namespace TauCeti

open scoped ContinuousMap

variable {X Y Z Z' : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace Z']

/-- **Path connectedness is a homotopy invariant.** A space homotopy equivalent to a path
connected space is path connected. -/
theorem _root_.ContinuousMap.HomotopyEquiv.pathConnectedSpace [PathConnectedSpace X]
    (e : X ≃ₕ Y) : PathConnectedSpace Y where
  nonempty := (PathConnectedSpace.nonempty (X := X)).map e.toFun
  joined y₀ y₁ :=
    -- Evaluating the homotopy `e.toFun ∘ e.invFun ≃ id` at `y` is a path from
    -- `e.toFun (e.invFun y)` to `y`.
    have trace : ∀ y : Y, Joined (e.toFun (e.invFun y)) y := fun y => ⟨e.right_inv.some.evalAt y⟩
    ((trace y₀).symm.trans
        (Joined.map ⟨PathConnectedSpace.somePath (e.invFun y₀) (e.invFun y₁)⟩
          e.toFun.continuous)).trans
      (trace y₁)

/-- The product of two homotopy equivalences acts componentwise. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.prodCongr_apply (h₁ : X ≃ₕ Y) (h₂ : Z ≃ₕ Z')
    (x : X × Z) : h₁.prodCongr h₂ x = (h₁ x.1, h₂ x.2) :=
  (rfl)

variable (X Y) in
/-- The projection `X × Y → X` is a homotopy equivalence when `Y` is contractible: its homotopy
inverse includes `X` at a point of `Y` to which `Y` contracts. -/
noncomputable def _root_.ContinuousMap.HomotopyEquiv.prodContractible [ContractibleSpace Y] :
    (X × Y) ≃ₕ X where
  toFun := ContinuousMap.fst
  invFun := (ContinuousMap.id X).prodMk (ContinuousMap.const X (id_nullhomotopic Y).choose)
  left_inv := by
    obtain ⟨H⟩ := (id_nullhomotopic Y).choose_spec
    exact ContinuousMap.Homotopic.symm ⟨{
      toFun q := (q.2.1, H (q.1, q.2.2))
      continuous_toFun := by fun_prop
      map_zero_left _ := by simp
      map_one_left _ := by simp }⟩
  right_inv := ContinuousMap.Homotopic.refl _

/-- The underlying map of the homotopy equivalence `X × Y ≃ₕ X` for contractible `Y` is the
projection. -/
theorem _root_.ContinuousMap.HomotopyEquiv.prodContractible_toFun [ContractibleSpace Y] :
    (ContinuousMap.HomotopyEquiv.prodContractible X Y).toFun = ContinuousMap.fst :=
  (rfl)

/-- The homotopy equivalence `X × Y ≃ₕ X` for contractible `Y` is the projection. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.coe_prodContractible [ContractibleSpace Y] :
    ⇑(ContinuousMap.HomotopyEquiv.prodContractible X Y) = Prod.fst :=
  (rfl)

end TauCeti
