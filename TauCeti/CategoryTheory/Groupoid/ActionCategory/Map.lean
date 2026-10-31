/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Functoriality of action categories and subgroup restrictions

A map `f : X → Y` that is equivariant along a monoid homomorphism `φ : M →* N`, that is
`f (m • x) = φ m • f x`, induces a functor `ActionCategory.map φ f` from the action category
`M ⋉ X` to `N ⋉ Y`: it sends the point `x` to `f x` and the arrow labelled `m` to the arrow
labelled `φ m`. It is faithful when `φ` is injective, and it is full exactly when every arrow
between two image points lifts: whenever `n • f x = f x'`, some `m` with `φ m = n` carries `x` to
`x'` (`CategoryTheory.ActionCategory.full_map_iff`).

The main instance is the restriction of an action groupoid to a subset. Let `H` be a subgroup of a
group `G` acting on `X`, and let `S` be a subset of `X` preserved by `H`, as a `SubMulAction H X`.
The functor `CategoryTheory.ActionCategory.inclusion S : H ⋉ S ⥤ G ⋉ X` keeps each label of `H`
as an element of `G`, so it is faithful and injective on objects, and its objects are exactly
the points of `S`. It is full exactly when `S` is a *slice* for `H`: every element of `G`
carrying a point of `S` into `S` lies in `H` (`CategoryTheory.ActionCategory.full_inclusion_iff`).
In that case the inclusion identifies `H ⋉ S` with the full subgroupoid of `G ⋉ X` on the points
of `S`. For a proper action of a discrete group, a slice at `x` for the stabilizer of `x` is the
local isotropy model of the quotient `[X/G]` near the orbit of `x`. Labels acting trivially are
kept, so the identification retains ineffective isotropy.

## Main declarations

* `CategoryTheory.ActionCategory.map`: the functor induced by an equivariant map.
* `CategoryTheory.ActionCategory.faithful_map`: it is faithful along an injective homomorphism.
* `CategoryTheory.ActionCategory.full_map_iff`: it is full exactly when arrows between image
  points lift.
* `CategoryTheory.ActionCategory.inclusion`: the inclusion of the action category of a subgroup
  on an invariant subset.
* `CategoryTheory.ActionCategory.full_inclusion_iff`: the inclusion is full exactly for a slice.
* `CategoryTheory.ActionCategory.range_inclusion_obj`: its objects are the points of the subset.
* `CategoryTheory.ActionCategory.range_inclusion_total`: for a slice, its arrows are the arrows
  with source and target in the subset.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.1.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open MulAction

namespace CategoryTheory.ActionCategory

section Map

variable {M N : Type*} [Monoid M] [Monoid N] {X Y : Type*} [MulAction M X] [MulAction N Y]

/-- The functor `M ⋉ X ⥤ N ⋉ Y` induced by a map `f : X → Y` that is equivariant along a monoid
homomorphism `φ : M →* N`. It sends the point `x` to `f x` and the arrow labelled `m` to the
arrow labelled `φ m`. -/
def map (φ : M →* N) (f : X →ₑ[φ] Y) : ActionCategory M X ⥤ ActionCategory N Y where
  obj a := objEquiv N Y (f a.back)
  map {a _} g := Functor.Elements.homMk (φ g.hom)
    ((map_smulₛₗ f g.hom a.back).symm.trans (congrArg f g.map_val))
  map_id _ := Functor.Elements.hom_ext (map_one φ)
  map_comp g g' := Functor.Elements.hom_ext (map_mul φ g'.hom g.hom)

variable (φ : M →* N) (f : X →ₑ[φ] Y)

/-- The functor induced by an equivariant map sends the point `x` to `f x`. -/
@[simp]
theorem map_obj (x : X) : (map φ f).obj (objEquiv M X x) = objEquiv N Y (f x) := (rfl)

/-- The point underlying the image of an object is the image of its point. -/
@[simp]
theorem back_map_obj (a : ActionCategory M X) : ((map φ f).obj a).back = f a.back := (rfl)

/-- The functor induced by an equivariant map relabels arrows by the homomorphism. -/
@[simp]
theorem map_map_hom {a b : ActionCategory M X} (g : a ⟶ b) :
    ((map φ f).map g).hom = φ g.hom := (rfl)

/-- The functor induced by an equivariant map along an injective homomorphism is faithful. -/
theorem faithful_map (hφ : Function.Injective φ) : (map φ f).Faithful where
  map_injective h := Functor.Elements.hom_ext (hφ (congrArg Functor.Elements.Hom.hom h))

/-- The functor induced by an equivariant map is full exactly when every arrow between two image
points lifts: if `n • f x = f x'`, then some `m` with `φ m = n` carries `x` to `x'`. -/
theorem full_map_iff : (map φ f).Full ↔
    ∀ (x x' : X) (n : N), n • f x = f x' → ∃ m : M, φ m = n ∧ m • x = x' := by
  constructor
  · intro _ x x' n hn
    obtain ⟨g, hg⟩ := (map φ f).map_surjective
      (X := objEquiv M X x) (Y := objEquiv M X x') (Functor.Elements.homMk n hn)
    exact ⟨g.hom, congrArg Functor.Elements.Hom.hom hg, g.map_val⟩
  · intro h
    refine ⟨fun {a b} g => ?_⟩
    obtain ⟨m, hm, hmx⟩ := h a.back b.back g.hom g.map_val
    exact ⟨Functor.Elements.homMk m hmx, Functor.Elements.hom_ext hm⟩

end Map

section Inclusion

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] {H : Subgroup G}

/-- The inclusion `H ⋉ S ⥤ G ⋉ X` of the action category of a subgroup `H` on an `H`-invariant
subset `S`. It sends a point of `S` to itself and keeps each label of `H` as an element of `G`. -/
def inclusion (S : SubMulAction H X) : ActionCategory H S ⥤ ActionCategory G X :=
  map H.subtype { toFun := Subtype.val, map_smul' := fun _ _ => rfl }

variable (S : SubMulAction H X)

/-- The inclusion sends a point of the invariant subset to itself. -/
@[simp]
theorem inclusion_obj (y : S) :
    (inclusion S).obj (objEquiv H S y) = objEquiv G X (y : X) := (rfl)

/-- The point underlying the image of an object under the inclusion is its point. -/
@[simp]
theorem back_inclusion_obj (a : ActionCategory H S) :
    ((inclusion S).obj a).back = (a.back : X) := (rfl)

/-- The inclusion keeps the label of each arrow. -/
@[simp]
theorem inclusion_map_hom {a b : ActionCategory H S} (g : a ⟶ b) :
    ((inclusion S).map g).hom = H.subtype g.hom := (rfl)

/-- The inclusion of the action category of a subgroup is faithful. -/
instance faithful_inclusion : (inclusion S).Faithful :=
  faithful_map _ _ H.subtype_injective

/-- The inclusion is injective on objects. -/
theorem inclusion_obj_injective : Function.Injective (inclusion S).obj := fun _ _ h =>
  (objEquiv H S).symm.injective (Subtype.ext (congrArg ActionCategory.back h))

/-- The objects in the image of the inclusion are exactly the points of the invariant subset. -/
theorem range_inclusion_obj : Set.range (inclusion S).obj = {a | a.back ∈ S} := by
  ext a
  refine ⟨?_, fun ha => ⟨objEquiv H S ⟨a.back, ha⟩, back_coe a⟩⟩
  rintro ⟨b, rfl⟩
  exact b.back.2

/-- The inclusion of the action category of a subgroup `H` on an invariant subset `S` is full
exactly when `S` is a slice for `H`: every element of `G` carrying a point of `S` into `S`
lies in `H`. -/
theorem full_inclusion_iff :
    (inclusion S).Full ↔ ∀ (g : G) (y : X), y ∈ S → g • y ∈ S → g ∈ H := by
  refine (full_map_iff _ _).trans ⟨fun h g y hy hgy => ?_, fun h y y' g hg => ?_⟩
  · obtain ⟨m, hm, -⟩ := h ⟨y, hy⟩ ⟨g • y, hgy⟩ g rfl
    exact hm ▸ m.2
  · -- `hg` is stated through the underlying function of the equivariant inclusion.
    have hg' : g • (y : X) = y' := hg
    exact ⟨⟨g, h g y y.2 (hg' ▸ y'.2)⟩, rfl, Subtype.ext hg'⟩

/-- For a slice `S` for `H`, the arrows of `H ⋉ S` are, through the inclusion, exactly the arrows
of `G ⋉ X` with source and target in `S`. -/
theorem range_inclusion_total (hS : ∀ (g : G) (y : X), y ∈ S → g • y ∈ S → g ∈ H) :
    Set.range (fun f : Quiver.Total (ActionCategory H S) =>
      (⟨(inclusion S).obj f.left, (inclusion S).obj f.right, (inclusion S).map f.hom⟩ :
        Quiver.Total (ActionCategory G X))) =
      {f | f.left.back ∈ S ∧ f.right.back ∈ S} := by
  ext ⟨l, r, g⟩
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨f, hf⟩
    cases hf
    simp
  · have := (full_inclusion_iff S).mpr hS
    obtain ⟨a, rfl⟩ : l ∈ Set.range (inclusion S).obj := by
      simpa [range_inclusion_obj] using hf.1
    obtain ⟨b, rfl⟩ : r ∈ Set.range (inclusion S).obj := by
      simpa [range_inclusion_obj] using hf.2
    exact ⟨⟨a, b, (inclusion S).preimage g⟩, by simp⟩

end Inclusion

end CategoryTheory.ActionCategory
