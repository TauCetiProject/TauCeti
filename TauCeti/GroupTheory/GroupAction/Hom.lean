/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Elementary equivariant maps and the existence of equivariant maps

Two elementary equivariant maps which `Mathlib/GroupTheory/GroupAction/Hom.lean` leaves
unrecorded: the unique equivariant map to the one-point space `PUnit`, and the constant equivariant
map whose value is a fixed point.

An equivariant map `X →[G] Y` sends each point to a point whose stabilizer contains the
stabilizer of the first. Conversely, if every point of `X` has such a point in `Y`, an equivariant
map exists: choose a representative of each orbit of `X`, send it to a point of `Y` fixed by its
stabilizer, and extend along the orbit.

## Main declarations

* `MulActionHom.toPUnit`: the equivariant map from any space to the point.
* `MulActionHom.constOfMemFixedPoints`: the constant equivariant map at a fixed point.
* `TauCeti.MulAction.nonempty_mulActionHom_iff`: an equivariant map exists exactly when every
  stabilizer of `X` is contained in a stabilizer of `Y`.
-/

public section

open MulAction

universe w

namespace MulActionHom

variable {M N X Y : Type*} [SMul M X] {φ : M → N}

variable (X φ) in
/-- The equivariant map from `X` to the point. -/
def toPUnit : X →ₑ[φ] PUnit.{w + 1} :=
  ⟨fun _ ↦ PUnit.unit, fun _ _ ↦ rfl⟩

variable (X φ) in
theorem coe_toPUnit : ⇑(toPUnit.{w} X φ) = Function.const X PUnit.unit :=
  (rfl)

variable [Monoid N] [MulAction N Y]

/-- The equivariant map from `X` with constant value a fixed point `y` of `Y`. -/
def constOfMemFixedPoints {y : Y} (hy : y ∈ fixedPoints N Y) : X →ₑ[φ] Y :=
  ⟨fun _ ↦ y, fun m _ ↦ (hy (φ m)).symm⟩

@[simp]
theorem constOfMemFixedPoints_apply {y : Y} (hy : y ∈ fixedPoints N Y) (x : X) :
    constOfMemFixedPoints (φ := φ) hy x = y :=
  (rfl)

theorem coe_constOfMemFixedPoints {y : Y} (hy : y ∈ fixedPoints N Y) :
    ⇑(constOfMemFixedPoints (X := X) (φ := φ) hy) = Function.const X y :=
  (rfl)

end MulActionHom

namespace TauCeti

open MulAction

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

/-- There is an equivariant map `X →[G] Y` exactly when the stabilizer of every point of `X` is
contained in the stabilizer of some point of `Y`. -/
theorem MulAction.nonempty_mulActionHom_iff :
    Nonempty (X →[G] Y) ↔ ∀ x : X, ∃ y : Y, stabilizer G x ≤ stabilizer G y := by
  refine ⟨fun ⟨f⟩ x => ⟨f x, fun g hg => ?_⟩, fun h => ?_⟩
  · rw [mem_stabilizer_iff, ← map_smul f, mem_stabilizer_iff.mp hg]
  choose w hw using h
  -- `r x` is the chosen representative of the orbit of `x`, and `c x • r x = x`.
  let r : X → X := fun x => (Quotient.mk (orbitRel G X) x).out
  have hr (x : X) : ∃ g : G, g • r x = x := by
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel G X) x))
    exact ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩
  choose c hc using hr
  have hr_smul (g : G) (x : X) : r (g • x) = r x :=
    congrArg Quotient.out (Quotient.sound (orbitRel_apply.mpr (mem_orbit x g)))
  refine ⟨{ toFun := fun x => c x • w (r x), map_smul' := fun g x => ?_ }⟩
  -- The two choices of a group element carrying `r x` to `g • x` differ by a stabilizer element.
  have h1 : c (g • x) • r x = g • x := by simpa only [hr_smul] using hc (g • x)
  have key : (g * c x)⁻¹ * c (g • x) ∈ stabilizer G (r x) := by
    rw [mem_stabilizer_iff, mul_smul, h1, mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff,
      hc]
  have hfix := mem_stabilizer_iff.mp (hw (r x) key)
  rw [mul_smul, inv_smul_eq_iff] at hfix
  -- `MulActionHom` states equivariance for the identity of `G`, written `id g`.
  change c (g • x) • w (r (g • x)) = g • c x • w (r x)
  rw [hr_smul, hfix, mul_smul]

end TauCeti
