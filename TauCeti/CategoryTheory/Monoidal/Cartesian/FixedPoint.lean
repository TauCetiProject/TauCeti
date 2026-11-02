/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.Basic

/-!
# Fixed global points of internal actions

Let a monoid object `G` act on `X` in a cartesian monoidal category. A global point `x` of `X` is
fixed by `G` when its orbit morphism `G ⟶ X`, `g ↦ g • x`, is the constant morphism at `x`.
Equivalently, every `T`-point of `G` fixes the restriction of `x` to `T`, for every test object
`T`. Fixing only the global points of `G` is weaker: for group schemes over a field these are only
the rational points.

Under the trivial action `ModObj.trivialAction` every global point is fixed, and equivariant
morphisms carry fixed points to fixed points. For a group object, `x` is fixed exactly when its
stabilizer is all of `G`: the stabilizing `T`-points are all of `T ⟶ G` for every `T`, or
equivalently the inclusion of the stabilizer into `G` is an isomorphism. For group schemes this
is the scheme-theoretic stabilizer, so a point can fail to be fixed even though every rational
point of the group fixes it.

## Main declarations

* `TauCeti.IsFixedPoint`: the orbit morphism of `x` is constant.
* `TauCeti.isFixedPoint_iff_forall_smul`: `x` is fixed by every test-object point of `G`.
* `TauCeti.isFixedPoint_trivialAction`: every point is fixed under the trivial action.
* `TauCeti.IsFixedPoint.comp`: equivariant morphisms preserve fixed points.
* `TauCeti.isFixedPoint_iff_forall_stabilizerPoints_eq_top` and
  `TauCeti.isFixedPoint_iff_isIso_stabilizer_incl`: a point is fixed exactly when its stabilizer
  is the whole group.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ModObj

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (G : C) {X Y : C}

section Monoid

variable [MonObj G]

/-- A global point `x` is fixed by `G` when its orbit morphism `g ↦ g • x` is the constant
morphism at `x`. -/
def IsFixedPoint [ModObj G X] (x : 𝟙_ C ⟶ X) : Prop :=
  orbitMap G x = toUnit G ≫ x

variable {G}

theorem isFixedPoint_iff [ModObj G X] {x : 𝟙_ C ⟶ X} :
    IsFixedPoint G x ↔ orbitMap G x = toUnit G ≫ x :=
  Iff.rfl

/-- A global point is fixed exactly when every `T`-point of `G` fixes its restriction to `T`. -/
theorem isFixedPoint_iff_forall_smul [ModObj G X] {x : 𝟙_ C ⟶ X} :
    IsFixedPoint G x ↔ ∀ ⦃T : C⦄ (g : T ⟶ G), g • (toUnit T ≫ x) = toUnit T ≫ x := by
  refine ⟨fun h T g ↦ ?_, fun h ↦ ?_⟩
  · rw [← comp_orbitMap, isFixedPoint_iff.mp h, ← Category.assoc, toUnit_unique (g ≫ toUnit G)]
  · rw [isFixedPoint_iff, ← Category.id_comp (orbitMap G x), comp_orbitMap, h]

/-- A test-object point of `G` fixes the restriction of a fixed point. -/
@[simp]
theorem IsFixedPoint.smul_eq [ModObj G X] {x : 𝟙_ C ⟶ X} (hx : IsFixedPoint G x) {T : C}
    (g : T ⟶ G) : g • (toUnit T ≫ x) = toUnit T ≫ x :=
  isFixedPoint_iff_forall_smul.mp hx g

/-- A global point of `G` fixes a fixed point. -/
@[simp]
theorem IsFixedPoint.smul_eq_self [ModObj G X] {x : 𝟙_ C ⟶ X} (hx : IsFixedPoint G x)
    (g : 𝟙_ C ⟶ G) : g • x = x := by
  simpa only [toUnit_unit, Category.id_comp] using hx.smul_eq g

/-- An equivariant morphism carries a fixed point to a fixed point. -/
theorem IsFixedPoint.comp [ModObj G X] [ModObj G Y] {x : 𝟙_ C ⟶ X} (hx : IsFixedPoint G x)
    (f : X ⟶ Y) [IsModHom G f] : IsFixedPoint G (x ≫ f) := by
  rw [isFixedPoint_iff, ← orbitMap_comp, isFixedPoint_iff.mp hx, Category.assoc]

variable (G) in
attribute [local instance] ModObj.trivialAction in
/-- Every global point is fixed under the trivial action. -/
theorem isFixedPoint_trivialAction (x : 𝟙_ C ⟶ X) : IsFixedPoint G x := by
  rw [isFixedPoint_iff_forall_smul]
  intro T g
  exact lift_snd _ _

end Monoid

section Group

variable {G} [GrpObj G] [ModObj G X] {x : 𝟙_ C ⟶ X}

/-- A global point is fixed exactly when, for every test object `T`, every `T`-point of `G`
stabilizes it. -/
theorem isFixedPoint_iff_forall_stabilizerPoints_eq_top :
    IsFixedPoint G x ↔ ∀ T : C, stabilizerPoints G x T = ⊤ := by
  simp only [isFixedPoint_iff_forall_smul, Subgroup.eq_top_iff', MulAction.mem_stabilizer_iff]

variable [HasPullback (orbitMap G x) x]

/-- A global point is fixed exactly when its stabilizer is the whole group, that is, when the
inclusion of the stabilizer is an isomorphism. -/
theorem isFixedPoint_iff_isIso_stabilizer_incl :
    IsFixedPoint G x ↔ IsIso (stabilizer.incl G x) := by
  refine ⟨fun hx ↦ ?_, fun h ↦ ?_⟩
  · have hmem : 𝟙 G ∈ stabilizerPoints G x G :=
      isFixedPoint_iff_forall_stabilizerPoints_eq_top.mp hx G ▸ Subgroup.mem_top _
    refine ⟨stabilizer.lift G x (𝟙 G) hmem, ?_, stabilizer.lift_incl G x _ hmem⟩
    exact (cancel_mono (stabilizer.incl G x)).1 (by simp)
  · rw [isFixedPoint_iff, ← IsIso.inv_hom_id_assoc (stabilizer.incl G x) (orbitMap G x),
      orbitFiber.incl_orbitMap, ← Category.assoc, toUnit_unique (_ ≫ toUnit _)]

/-- The stabilizer of a fixed point is the whole group. -/
theorem IsFixedPoint.isIso_stabilizer_incl (hx : IsFixedPoint G x) :
    IsIso (stabilizer.incl G x) :=
  isFixedPoint_iff_isIso_stabilizer_incl.mp hx

end Group

end TauCeti
