/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
public import TauCeti.CategoryTheory.Codiscrete
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Unit, pair and one-object topological groupoids

The native categories `Discrete X`, `Codiscrete X` and `SingleObj G` become topological
groupoids with arrow spaces homeomorphic to `X`, `X × X` and `G`, respectively. In particular,
a discrete *category* on a space does not replace the topology of that space by the discrete
topology.

Pair-groupoid arrow coordinates are (target, source). Its composable pairs are homeomorphic
to triples (final, middle, initial), and composition discards the middle coordinate. For a
group over a point, categorical composition of the arrow labelled `h` followed by the arrow
labelled `g` has label `g * h`. These descriptions make both the topology and the order of
multiplication explicit for subsequent smooth constructions.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti

namespace UnitGroupoid

variable (X : Type*) [TopologicalSpace X]

/-- The objects of the unit groupoid retain the topology of `X`. -/
instance instTopologicalSpaceObjects : TopologicalSpace (Discrete X) :=
  .induced Discrete.as inferInstance

/-- Forgetting the categorical wrapper is a homeomorphism on objects. -/
def objectHomeomorph : Discrete X ≃ₜ X :=
  discreteEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

/-- Total arrows of the unit groupoid carry the topology of their sources. -/
instance instTopologicalSpaceArrows : TopologicalSpace (Quiver.Total (Discrete X)) :=
  .induced (fun a ↦ a.left.as) inferInstance

/-- Every arrow of the unit groupoid is the unit at its source. -/
def arrowHomeomorph : Quiver.Total (Discrete X) ≃ₜ X where
  toFun a := a.left.as
  invFun x := ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩
  left_inv := by
    rintro ⟨⟨x⟩, ⟨y⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

@[simp]
theorem objectHomeomorph_apply (x : Discrete X) : objectHomeomorph X x = x.as := (rfl)

@[simp]
theorem objectHomeomorph_symm_apply (x : X) :
    (objectHomeomorph X).symm x = Discrete.mk x := (rfl)

@[simp]
theorem arrowHomeomorph_apply (a : Quiver.Total (Discrete X)) :
    arrowHomeomorph X a = a.left.as := (rfl)

@[simp]
theorem arrowHomeomorph_symm_apply (x : X) :
    (arrowHomeomorph X).symm x = ⟨⟨x⟩, ⟨x⟩, 𝟙 _⟩ := (rfl)

/-- The unit groupoid on any topological space is a topological groupoid. -/
instance isTopologicalGroupoid : IsTopologicalGroupoid (Discrete X) where
  continuous_source := (objectHomeomorph X).symm.continuous.comp
    (arrowHomeomorph X).continuous
  continuous_target := by
    convert (objectHomeomorph X).symm.continuous.comp (arrowHomeomorph X).continuous using 1
    funext a
    exact (Discrete.ext (Discrete.eq_of_hom a.hom)).symm
  continuous_unit := (arrowHomeomorph X).symm.continuous.comp (objectHomeomorph X).continuous
  continuous_inverse := by
    apply (arrowHomeomorph X).isInducing.continuous_iff.mpr
    convert (arrowHomeomorph X).continuous using 1
    funext a
    exact (Discrete.eq_of_hom a.hom).symm
  continuous_comp := by
    apply (arrowHomeomorph X).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, arrowHomeomorph_apply, Quiver.Total.comp_left] using
      (arrowHomeomorph X).continuous.comp (continuous_fst.comp continuous_subtype_val)

/-- Composable pairs in the unit groupoid are pairs of the same unit, with the topology
of the object space, not a discrete topology. -/
def composablePairsHomeomorph :
    {p : Quiver.Total (Discrete X) × Quiver.Total (Discrete X) //
      p.1.right = p.2.left} ≃ₜ X where
  toFun p := p.1.1.left.as
  invFun x := ⟨((arrowHomeomorph X).symm x, (arrowHomeomorph X).symm x), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨⟨x⟩, ⟨y⟩, f⟩, ⟨⟨y'⟩, ⟨z⟩, g⟩⟩, h⟩
    obtain rfl := Discrete.eq_of_hom f
    cases h
    obtain rfl := Discrete.eq_of_hom g
    rfl
  right_inv _ := rfl
  continuous_toFun := (arrowHomeomorph X).continuous.comp
    (continuous_fst.comp continuous_subtype_val)
  continuous_invFun := ((arrowHomeomorph X).symm.continuous.prodMk
    (arrowHomeomorph X).symm.continuous).subtype_mk _

@[simp]
theorem composablePairsHomeomorph_apply
    (p : {p : Quiver.Total (Discrete X) × Quiver.Total (Discrete X) //
      p.1.right = p.2.left}) :
    composablePairsHomeomorph X p = p.1.1.left.as := (rfl)

@[simp]
theorem composablePairsHomeomorph_symm_apply (x : X) :
    (composablePairsHomeomorph X).symm x =
      ⟨((arrowHomeomorph X).symm x, (arrowHomeomorph X).symm x), by simp⟩ := (rfl)

end UnitGroupoid

namespace PairGroupoid

variable (X : Type*) [TopologicalSpace X]

/-- The objects of the pair groupoid retain the topology of `X`. -/
instance instTopologicalSpaceObjects : TopologicalSpace (Codiscrete X) :=
  .induced Codiscrete.as inferInstance

/-- Forgetting the categorical wrapper is a homeomorphism on objects. -/
def objectHomeomorph : Codiscrete X ≃ₜ X :=
  codiscreteEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

/-- Pair-groupoid arrows carry the product topology in (target, source) coordinates. -/
instance instTopologicalSpaceArrows : TopologicalSpace (Quiver.Total (Codiscrete X)) :=
  .induced (fun a ↦ (a.right.as, a.left.as)) inferInstance

/-- The unique arrow from `x` to `y` has coordinates `(y, x)`. -/
def arrowHomeomorph : Quiver.Total (Codiscrete X) ≃ₜ X × X where
  toFun a := (a.right.as, a.left.as)
  invFun p := ⟨⟨p.2⟩, ⟨p.1⟩, default⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

@[simp]
theorem objectHomeomorph_apply (x : Codiscrete X) : objectHomeomorph X x = x.as := (rfl)

@[simp]
theorem objectHomeomorph_symm_apply (x : X) :
    (objectHomeomorph X).symm x = Codiscrete.mk x := (rfl)

@[simp]
theorem arrowHomeomorph_apply (a : Quiver.Total (Codiscrete X)) :
    arrowHomeomorph X a = (a.right.as, a.left.as) := (rfl)

@[simp]
theorem arrowHomeomorph_symm_apply (p : X × X) :
    (arrowHomeomorph X).symm p = ⟨⟨p.2⟩, ⟨p.1⟩, default⟩ := (rfl)

/-- Source is the second coordinate of a pair-groupoid arrow. -/
@[fun_prop]
theorem continuous_source :
    Continuous (Quiver.Total.left : Quiver.Total (Codiscrete X) → Codiscrete X) :=
  (objectHomeomorph X).symm.continuous.comp
    (continuous_snd.comp (arrowHomeomorph X).continuous)

/-- Target is the first coordinate of a pair-groupoid arrow. -/
@[fun_prop]
theorem continuous_target :
    Continuous (Quiver.Total.right : Quiver.Total (Codiscrete X) → Codiscrete X) :=
  (objectHomeomorph X).symm.continuous.comp
    (continuous_fst.comp (arrowHomeomorph X).continuous)

/-- The pair groupoid on any topological space is a topological groupoid. -/
instance isTopologicalGroupoid : IsTopologicalGroupoid (Codiscrete X) where
  continuous_source := continuous_source X
  continuous_target := continuous_target X
  continuous_unit := by
    apply (arrowHomeomorph X).isInducing.continuous_iff.mpr
    exact (objectHomeomorph X).continuous.prodMk (objectHomeomorph X).continuous
  continuous_inverse := by
    apply (arrowHomeomorph X).isInducing.continuous_iff.mpr
    exact (continuous_snd.comp (arrowHomeomorph X).continuous).prodMk
      (continuous_fst.comp (arrowHomeomorph X).continuous)
  continuous_comp := by
    apply (arrowHomeomorph X).isInducing.continuous_iff.mpr
    simpa only [Function.comp_def, arrowHomeomorph_apply, objectHomeomorph_apply,
      Quiver.Total.comp_left, Quiver.Total.comp_right] using
      ((objectHomeomorph X).continuous.comp
        ((continuous_target X).comp (continuous_snd.comp continuous_subtype_val))).prodMk
        ((objectHomeomorph X).continuous.comp
          ((continuous_source X).comp (continuous_fst.comp continuous_subtype_val)))

/-- Composable arrows, in categorical order, have coordinates `(z, y, x)` when they run
from `x` to `y` and then from `y` to `z`. The topology is the inherited subspace topology. -/
def composablePairsHomeomorph :
    {p : Quiver.Total (Codiscrete X) × Quiver.Total (Codiscrete X) //
      p.1.right = p.2.left} ≃ₜ X × X × X where
  toFun p := (p.1.2.right.as, p.1.1.right.as, p.1.1.left.as)
  invFun p := ⟨(⟨⟨p.2.2⟩, ⟨p.2.1⟩, default⟩, ⟨⟨p.2.1⟩, ⟨p.1⟩, default⟩), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨x, y, f⟩, ⟨y', z, g⟩⟩, h⟩
    cases h
    rfl
  right_inv _ := rfl
  continuous_toFun := by
    exact ((objectHomeomorph X).continuous.comp
      ((continuous_target X).comp (continuous_snd.comp continuous_subtype_val))).prodMk
      (((objectHomeomorph X).continuous.comp
        ((continuous_target X).comp (continuous_fst.comp continuous_subtype_val))).prodMk
        ((objectHomeomorph X).continuous.comp
          ((continuous_source X).comp (continuous_fst.comp continuous_subtype_val))))
  continuous_invFun := by
    exact (((arrowHomeomorph X).symm.continuous.comp
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd))).prodMk
      ((arrowHomeomorph X).symm.continuous.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).subtype_mk _

@[simp]
theorem composablePairsHomeomorph_apply
    (p : {p : Quiver.Total (Codiscrete X) × Quiver.Total (Codiscrete X) //
      p.1.right = p.2.left}) :
    composablePairsHomeomorph X p =
      (p.1.2.right.as, p.1.1.right.as, p.1.1.left.as) := (rfl)

@[simp]
theorem composablePairsHomeomorph_symm_apply (p : X × X × X) :
    (composablePairsHomeomorph X).symm p =
      ⟨(⟨⟨p.2.2⟩, ⟨p.2.1⟩, default⟩, ⟨⟨p.2.1⟩, ⟨p.1⟩, default⟩), rfl⟩ := (rfl)

end PairGroupoid

namespace OneObjectGroupoid

variable (G : Type*) [TopologicalSpace G]

/-- The one-object category has the unique topology on its singleton object space. -/
instance instTopologicalSpaceObjects : TopologicalSpace (SingleObj G) :=
  inferInstanceAs (TopologicalSpace Unit)

/-- The arrow topology of a one-object category is the topology of its labels. -/
instance instTopologicalSpaceArrows : TopologicalSpace (Quiver.Total (SingleObj G)) :=
  .induced (fun a ↦ a.hom) inferInstance

/-- Total arrows of the one-object quiver recover the original label space. -/
def arrowHomeomorph : Quiver.Total (SingleObj G) ≃ₜ G where
  toFun a := a.hom
  invFun g := ⟨SingleObj.star G, SingleObj.star G, g⟩
  left_inv := by rintro ⟨x, y, g⟩; cases x; cases y; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

@[simp]
theorem arrowHomeomorph_apply (a : Quiver.Total (SingleObj G)) :
    arrowHomeomorph G a = a.hom := (rfl)

@[simp]
theorem arrowHomeomorph_symm_apply (g : G) :
    (arrowHomeomorph G).symm g = ⟨SingleObj.star G, SingleObj.star G, g⟩ := (rfl)

/-- All pairs of labels are composable over the single object. The order here is
categorical: the first label is traversed first. -/
def composablePairsHomeomorph :
    {p : Quiver.Total (SingleObj G) × Quiver.Total (SingleObj G) //
      p.1.right = p.2.left} ≃ₜ G × G where
  toFun p := (arrowHomeomorph G p.1.1, arrowHomeomorph G p.1.2)
  invFun p := ⟨((arrowHomeomorph G).symm p.1, (arrowHomeomorph G).symm p.2), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨x, y, h⟩, ⟨y', z, g⟩⟩, _⟩
    cases x; cases y; cases y'; cases z
    rfl
  right_inv _ := rfl
  continuous_toFun := ((arrowHomeomorph G).continuous.comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
    ((arrowHomeomorph G).continuous.comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := (((arrowHomeomorph G).symm.continuous.comp continuous_fst).prodMk
    ((arrowHomeomorph G).symm.continuous.comp continuous_snd)).subtype_mk _

@[simp]
theorem composablePairsHomeomorph_apply
    (p : {p : Quiver.Total (SingleObj G) × Quiver.Total (SingleObj G) //
      p.1.right = p.2.left}) :
    composablePairsHomeomorph G p = (p.1.1.hom, p.1.2.hom) := (rfl)

@[simp]
theorem composablePairsHomeomorph_symm_apply (p : G × G) :
    (composablePairsHomeomorph G).symm p =
      ⟨((arrowHomeomorph G).symm p.1, (arrowHomeomorph G).symm p.2), rfl⟩ := (rfl)

/-- Categorical composition reverses the order of the two labels. Thus the geometric
product `gh`, first `h` and then `g`, is the original monoid product `g * h`. -/
-- `arrowHomeomorph_apply` already normalizes the left-hand side in the simp set.
theorem arrowHomeomorph_comp [Monoid G]
    (a b : Quiver.Total (SingleObj G)) (h : a.right = b.left) :
    arrowHomeomorph G (a.comp b h) = arrowHomeomorph G b * arrowHomeomorph G a := by
  cases h
  simp [Quiver.Total.comp_def, arrowHomeomorph_apply, SingleObj.comp_as_mul,
    SingleObj.id_as_one]

end OneObjectGroupoid

namespace OneObjectGroupoid

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A topological group is a topological groupoid over one point, with its original arrow
topology and its original geometric multiplication. -/
instance isTopologicalGroupoid : IsTopologicalGroupoid (SingleObj G) where
  continuous_source := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_target := continuous_of_const fun _ _ ↦ Subsingleton.elim _ _
  continuous_unit := continuous_of_const fun x y ↦ by
    cases Subsingleton.elim x y
    rfl
  continuous_inverse := by
    apply (arrowHomeomorph G).isInducing.continuous_iff.mpr
    convert (arrowHomeomorph G).continuous.inv using 1
    funext a
    simp [SingleObj.inv_as_inv]
  continuous_comp := by
    apply (arrowHomeomorph G).isInducing.continuous_iff.mpr
    convert
      ((arrowHomeomorph G).continuous.comp (continuous_snd.comp continuous_subtype_val)).mul
        ((arrowHomeomorph G).continuous.comp (continuous_fst.comp continuous_subtype_val)) using 1
    funext p
    exact arrowHomeomorph_comp G p.1.1 p.1.2 p.2

end OneObjectGroupoid
end TauCeti
