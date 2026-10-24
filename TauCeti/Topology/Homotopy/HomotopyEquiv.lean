/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Homotopy equivalences: path connectedness, products, and slices of a cylinder

A homotopy equivalence `e : X ≃ₕ Y` is not surjective, so path connectedness of `Y` cannot be
read off from the image of a path in `X`. What replaces surjectivity is the trace of the
homotopy `e.toFun ∘ e.invFun ≃ id`: evaluated at a point `y`, it is a path from
`e.toFun (e.invFun y)` to `y`. Two points of `Y` are therefore joined to points in the image of
`e.toFun`, which are joined to each other because `X` is path connected.

This is the prerequisite for the base-point-free homotopy-group statements in
`TauCeti.Topology.Homotopy.HomotopyGroup.HomotopyEquiv`, which need the target space to be path
connected before base-point change is available there. The file also records that the product
`ContinuousMap.HomotopyEquiv.prodCongr` of two homotopy equivalences acts componentwise.

Finally, the file records that a cylinder `X × [a, b]` is homotopy equivalent to `X`
through any of its slices `X × {t}`: the interval deforms linearly onto the point `t`. This is how
the two ends of a cylinder are seen to induce isomorphisms on homology.

## Main declarations

* `ContinuousMap.HomotopyEquiv.pathConnectedSpace`: a space homotopy equivalent to a path
  connected space is path connected.
* `ContinuousMap.HomotopyEquiv.prodCongr_apply`: the product of two homotopy equivalences acts
  componentwise.
* `ContinuousMap.HomotopyEquiv.prodIcc`: the slice `x ↦ (x, t)` is a homotopy equivalence
  `X ≃ₕ X × [a, b]`, with homotopy inverse the projection.
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

/-- **A cylinder deforms onto each of its slices.** For a point `t` of the interval `[a, b]`, the
slice `x ↦ (x, t)` is a homotopy equivalence `X ≃ₕ X × [a, b]`, with homotopy inverse the
projection: at time `s` a point `(x, u)` is sent to `(x, t + s (u - t))`. -/
def _root_.ContinuousMap.HomotopyEquiv.prodIcc {a b : ℝ} (t : Set.Icc a b) :
    X ≃ₕ X × Set.Icc a b where
  toFun := ⟨fun x ↦ (x, t), by fun_prop⟩
  invFun := .fst
  left_inv := ⟨.refl _⟩
  right_inv := ⟨
    { toFun p := (p.2.1, ⟨t + p.1 * (p.2.2 - t), by
        obtain ⟨⟨s, hs₀, hs₁⟩, -, u, hu₀, hu₁⟩ := p
        obtain ⟨t, ht₀, ht₁⟩ := t
        constructor <;> nlinarith⟩)
      continuous_toFun := by fun_prop
      map_zero_left p := by simp
      map_one_left p := by simp }⟩

/-- The slice homotopy equivalence at `t` sends `x` to `(x, t)`. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.prodIcc_apply {a b : ℝ} (t : Set.Icc a b) (x : X) :
    ContinuousMap.HomotopyEquiv.prodIcc t x = (x, t) :=
  (rfl)

/-- The homotopy inverse of a slice homotopy equivalence is the projection. -/
@[simp]
theorem _root_.ContinuousMap.HomotopyEquiv.prodIcc_symm_apply {a b : ℝ} (t : Set.Icc a b)
    (p : X × Set.Icc a b) : (ContinuousMap.HomotopyEquiv.prodIcc t).symm p = p.1 :=
  (rfl)

end TauCeti
