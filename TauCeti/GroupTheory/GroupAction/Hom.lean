/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# Elementary equivariant maps and the existence of equivariant maps

Two elementary equivariant maps which `Mathlib/GroupTheory/GroupAction/Hom.lean` leaves
unrecorded: the unique equivariant map to the one-point space `PUnit`, and the constant equivariant
map whose value is a fixed point.

For group actions, the stabilizer of the preimage of a set of values of an equivariant map is the
stabilizer of the set; in particular the stabilizer of the image of a point is the stabilizer of
the fibre through that point.

An equivariant map `X →[G] Y` sends each point to a point whose stabilizer contains the
stabilizer of the first. Conversely, if every point of `X` has such a point in `Y`, an equivariant
map exists: choose a representative of each orbit of `X`, send it to a point of `Y` fixed by its
stabilizer, and extend along the orbit.

## Main declarations

* `MulActionHom.toPUnit`: the equivariant map from any space to the point.
* `MulActionHom.constOfMemFixedPoints`: the constant equivariant map at a fixed point.
* `TauCeti.MulAction.stabilizer_preimage_of_subset_range`: the stabilizer of the preimage of a set
  of values is the stabilizer of the set.
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

open scoped Pointwise

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

section Stabilizer

variable {F : Type*} [FunLike F X Y] [MulActionHomClass F G X Y]

/-- The stabilizer of the preimage of a set of values of an equivariant map is the stabilizer of
the set. -/
theorem MulAction.stabilizer_preimage_of_subset_range (f : F) {s : Set Y}
    (hs : s ⊆ Set.range f) : stabilizer G (f ⁻¹' s) = stabilizer G s := by
  ext g
  rw [mem_stabilizer_iff, mem_stabilizer_iff, ← Group.preimage_smul_set]
  refine Set.preimage_eq_preimage' ?_ hs
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, rfl⟩ := hs hy
  exact ⟨g • x, map_smul f g x⟩

/-- The stabilizer of the preimage of a set under a surjective equivariant map is the stabilizer
of the set. -/
theorem MulAction.stabilizer_preimage_of_surjective {f : F} (hf : Function.Surjective f)
    (s : Set Y) : stabilizer G (f ⁻¹' s) = stabilizer G s :=
  stabilizer_preimage_of_subset_range f (hf.range_eq ▸ Set.subset_univ s)

/-- The stabilizer of the image of a point under an equivariant map is the stabilizer of the
fibre through that point. -/
theorem MulAction.stabilizer_apply_eq_stabilizer_preimage (f : F) (x : X) :
    stabilizer G (f x) = stabilizer G (f ⁻¹' {f x}) := by
  rw [stabilizer_preimage_of_subset_range f (Set.singleton_subset_iff.mpr ⟨x, rfl⟩),
    stabilizer_singleton]

end Stabilizer

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
