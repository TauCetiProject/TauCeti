/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.PUnit
public import Mathlib.CategoryTheory.Action
public import Mathlib.CategoryTheory.Groupoid.VertexGroup
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Isotropy, arrows and orbits of an action groupoid

For a group `G` acting on a type `X`, Mathlib's `CategoryTheory.ActionCategory G X` is the action
groupoid `G ⋉ X`: its objects correspond to points of `X` through `ActionCategory.objEquiv`, and an
arrow `x ⟶ y` is a group element `g` with `g • x = y`, its *label*. This file records the
dictionary between the groupoid and the action that the orbifold point of view uses, where
`G ⋉ X` is the presentation of the quotient `[X/G]`.

Arrows remember their labels. The total set of arrows is `G × X`, by label and source
(`ActionCategory.totalEquiv`); in these coordinates the source of `(g, x)` is `x`, its target is
`g • x`, the identity at `x` is `(1, x)`, inversion is labelled by `g⁻¹` and composition by the
product, `(f ≫ f').hom = f'.hom * f.hom` (Mathlib's `ActionCategory.comp_hom`).

The isotropy group of the object `x` is the stabilizer of `x`, with every element kept: an
element acting trivially on all of `X` still gives its own automorphism. This is what separates
an ineffective quotient from its effective reduction; for instance the point quotient `[*/G]`
has isotropy `G` and, for nontrivial `G`, is not equivalent to the point with trivial isotropy.
Two group laws on the isotropy group are in use, and both are compared with the stabilizer:
`Aut` and `End` multiply in the order of function composition, `g * h = h ≫ g`, matching the
stabilizer, while Mathlib's vertex group `CategoryTheory.Groupoid.vertexGroup` multiplies in
diagrammatic order, so the stabilizer is its opposite. Transporting isotropy along an arrow is
conjugation by its label.

Finally, the isomorphism classes of objects, the underlying set of the coarse space, are the
orbits of the action.

## Main declarations

* `CategoryTheory.ActionCategory.totalEquiv`: the arrows of `G ⋉ X` are `G × X`.
* `CategoryTheory.ActionCategory.stabilizerMulEquivAut`: the stabilizer of `x` is the
  automorphism group of `x`, compatibly with Mathlib's `ActionCategory.stabilizerIsoEnd`
  (`CategoryTheory.ActionCategory.toEnd_stabilizerMulEquivAut`) and with transport along arrows
  (`CategoryTheory.ActionCategory.autMulEquivOfIso_stabilizerMulEquivAut`).
* `CategoryTheory.ActionCategory.stabilizerMulEquivVertexGroup`: the stabilizer is the opposite
  of the vertex group.
* `CategoryTheory.ActionCategory.stabilizer_eq_bot_of_faithful`: if `G ⋉ X` has a faithful functor
  to a thin category, all stabilizers are trivial; in particular
  `CategoryTheory.ActionCategory.isEmpty_equivalence_punit`.
* `CategoryTheory.ActionCategory.autMulEquivOfMemFixedPoints`: the isotropy at a fixed point is
  all of `G`.
* `CategoryTheory.ActionCategory.orbitQuotientEquivIsomorphismClasses`: orbits are isomorphism
  classes.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public section

open MulAction

namespace CategoryTheory.ActionCategory

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

section Arrows

/-- An arrow of the action groupoid goes from a point to its translate by the arrow's label. -/
theorem hom_smul {x y : X} (f : objEquiv G X x ⟶ objEquiv G X y) :
    (f.hom : G) • x = y :=
  f.map_val

/-- The inverse of an arrow of the action groupoid is labelled by the inverse group element. -/
@[simp]
theorem inv_hom {a b : ActionCategory G X} (f : a ⟶ b) : (inv f).hom = (f.hom⁻¹ : G) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

variable (G X)

/-- The total set of arrows of the action groupoid, identified with `G × X` by recording the
label and the source of each arrow. The target of the arrow labelled `(g, x)` is `g • x`. -/
def totalEquiv : Quiver.Total (ActionCategory G X) ≃ G × X where
  toFun f := (f.hom.hom, f.left.back)
  invFun p := ⟨objEquiv G X p.2, objEquiv G X (p.1 • p.2), Functor.Elements.homMk p.1 rfl⟩
  left_inv := by
    rintro ⟨a, b, f⟩
    have key : ∀ (b' : ActionCategory G X) (f' : a ⟶ b'), b' = b → f'.hom = f.hom →
        (⟨a, b', f'⟩ : Quiver.Total (ActionCategory G X)) = ⟨a, b, f⟩ := by
      rintro _ f' rfl h
      rw [Functor.Elements.hom_ext h]
    exact key _ _ ((congrArg (objEquiv G X) f.map_val).trans (back_coe b)) rfl
  right_inv _ := rfl

variable {G X}

@[simp]
theorem totalEquiv_apply (f : Quiver.Total (ActionCategory G X)) :
    totalEquiv G X f = (f.hom.hom, f.left.back) := (rfl)

@[simp]
theorem totalEquiv_symm_apply_left (p : G × X) :
    ((totalEquiv G X).symm p).left = objEquiv G X p.2 := (rfl)

@[simp]
theorem totalEquiv_symm_apply_right (p : G × X) :
    ((totalEquiv G X).symm p).right = objEquiv G X (p.1 • p.2) := (rfl)

@[simp]
theorem totalEquiv_symm_apply_hom_hom (p : G × X) :
    ((totalEquiv G X).symm p).hom.hom = p.1 := (rfl)

end Arrows

section Isotropy

variable (G)

/-- The stabilizer of `x` is the automorphism group of the corresponding object of the action
groupoid. Every element of the stabilizer, including one acting trivially on all of `X`, is kept
as its own automorphism, and the multiplication matches `g * h = h ≫ g`. -/
def stabilizerMulEquivAut (x : X) : stabilizer G x ≃* Aut (objEquiv G X x) :=
  (toUnits (G := stabilizer G x)).trans
    ((Units.mapEquiv (stabilizerIsoEnd G x)).trans (Aut.unitsEndEquivAut _))

variable {G}

@[simp]
theorem stabilizerMulEquivAut_apply_hom_hom (x : X) (g : stabilizer G x) :
    (stabilizerMulEquivAut G x g).asIso.hom.hom = g := (rfl)

@[simp]
theorem stabilizerMulEquivAut_apply_inv_hom (x : X) (g : stabilizer G x) :
    (stabilizerMulEquivAut G x g).asIso.inv.hom = (g : G)⁻¹ := (rfl)

@[simp]
theorem coe_stabilizerMulEquivAut_symm_apply (x : X) (e : Aut (objEquiv G X x)) :
    ((stabilizerMulEquivAut G x).symm e : G) = e.asIso.hom.hom := (rfl)

/-- Under the inclusion of automorphisms into endomorphisms, `stabilizerMulEquivAut` restricts
to Mathlib's `ActionCategory.stabilizerIsoEnd` on the stabilizer submonoid. -/
theorem toEnd_stabilizerMulEquivAut (x : X) (g : stabilizer G x) :
    Aut.toEnd (stabilizerMulEquivAut G x g) = stabilizerIsoEnd G x ⟨g, g.2⟩ := (rfl)

/-- Transport of automorphisms along an arrow `f` of the action groupoid corresponds to
conjugation of stabilizers by the label of `f`. -/
theorem autMulEquivOfIso_stabilizerMulEquivAut {x y : X}
    (f : objEquiv G X x ⟶ objEquiv G X y) (g : stabilizer G x) :
    Aut.autMulEquivOfIso ((Groupoid.isoEquivHom _ _).symm f) (stabilizerMulEquivAut G x g) =
      stabilizerMulEquivAut G y (stabilizerEquivStabilizer (hom_smul f).symm g) := by
  ext : 2
  apply Functor.Elements.hom_ext
  simp [stabilizerEquivStabilizer_apply, mul_assoc]

variable (G)

/-- The stabilizer of `x` is the opposite of Mathlib's vertex group at the corresponding object.
The vertex group multiplies in diagrammatic order, `f * g = f ≫ g`, while stabilizer labels
compose as `g * h = h ≫ g`. -/
def stabilizerMulEquivVertexGroup (x : X) :
    stabilizer G x ≃* (objEquiv G X x ⟶ objEquiv G X x)ᵐᵒᵖ where
  toFun g := .op (Functor.Elements.homMk (g : G) g.2)
  invFun f := ⟨f.unop.hom, f.unop.map_val⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {G}

@[simp]
theorem stabilizerMulEquivVertexGroup_apply_unop_hom (x : X) (g : stabilizer G x) :
    (stabilizerMulEquivVertexGroup G x g).unop.hom = g := (rfl)

@[simp]
theorem coe_stabilizerMulEquivVertexGroup_symm_apply (x : X)
    (f : (objEquiv G X x ⟶ objEquiv G X x)ᵐᵒᵖ) :
    ((stabilizerMulEquivVertexGroup G x).symm f : G) = f.unop.hom := (rfl)

/-- If the action groupoid admits a faithful functor to a thin category, for instance an
equivalence with a discrete category, then every stabilizer is trivial. -/
theorem stabilizer_eq_bot_of_faithful {D : Type*} [Category D] [Quiver.IsThin D]
    (F : ActionCategory G X ⥤ D) [F.Faithful] (x : X) : stabilizer G x = ⊥ := by
  have : Subsingleton (objEquiv G X x ⟶ objEquiv G X x) :=
    ⟨fun _ _ => F.map_injective (Subsingleton.elim _ _)⟩
  have : Subsingleton (stabilizer G x) := (stabilizerMulEquivVertexGroup G x).toEquiv.subsingleton
  exact Subgroup.eq_bot_of_subsingleton _

end Isotropy

section FixedPoints

variable (G) in
/-- At a fixed point of the action, the isotropy group is all of `G`, including every element
acting trivially on `X`. -/
def autMulEquivOfMemFixedPoints {x : X} (hx : x ∈ fixedPoints G X) :
    Aut (objEquiv G X x) ≃* G :=
  (stabilizerMulEquivAut G x).symm.trans
    ((MulEquiv.subgroupCongr ((Subgroup.eq_top_iff' _).2 fun g => hx g)).trans Subgroup.topEquiv)

@[simp]
theorem autMulEquivOfMemFixedPoints_apply {x : X} (hx : x ∈ fixedPoints G X)
    (e : Aut (objEquiv G X x)) : autMulEquivOfMemFixedPoints G hx e = e.asIso.hom.hom := (rfl)

/-- If the group is nontrivial, the point quotient `[*/G]` is not equivalent to a thin category;
in particular it is not equivalent to the point with trivial isotropy. -/
theorem isEmpty_equivalence_punit [Nontrivial G] {D : Type*} [Category D] [Quiver.IsThin D] :
    IsEmpty (ActionCategory G PUnit ≌ D) := by
  refine ⟨fun e => ?_⟩
  have h := stabilizer_eq_bot_of_faithful e.functor PUnit.unit
  rw [(Subgroup.eq_top_iff' (stabilizer G PUnit.unit)).2 fun _ => rfl] at h
  exact top_ne_bot h

end FixedPoints

section Orbits

/-- Two objects of the action groupoid are connected by an arrow exactly when the corresponding
points lie in the same orbit. -/
theorem nonempty_hom_iff {x y : X} :
    Nonempty (objEquiv G X x ⟶ objEquiv G X y) ↔ ∃ g : G, g • x = y :=
  ⟨fun ⟨f⟩ => ⟨f.hom, hom_smul f⟩, fun ⟨g, hg⟩ => ⟨Functor.Elements.homMk g hg⟩⟩

/-- Two objects of the action groupoid are isomorphic exactly when the corresponding points lie
in the same orbit. -/
theorem isIsomorphic_iff_orbitRel {x y : X} :
    IsIsomorphic (objEquiv G X x) (objEquiv G X y) ↔ orbitRel G X x y := by
  rw [Groupoid.isIsomorphic_iff_nonempty_hom, nonempty_hom_iff, (orbitRel G X).comm',
    orbitRel_apply, mem_orbit_iff]

variable (G X)

/-- The orbit space of the action is the set of isomorphism classes of its action groupoid. -/
def orbitQuotientEquivIsomorphismClasses :
    orbitRel.Quotient G X ≃ _root_.Quotient (isIsomorphicSetoid (ActionCategory G X)) :=
  Quotient.congr (objEquiv G X) fun _ _ => isIsomorphic_iff_orbitRel.symm

variable {G X}

@[simp]
theorem orbitQuotientEquivIsomorphismClasses_mk (x : X) :
    orbitQuotientEquivIsomorphismClasses G X (_root_.Quotient.mk _ x) =
      _root_.Quotient.mk _ (objEquiv G X x) := (rfl)

end Orbits

end CategoryTheory.ActionCategory
