/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Category.QuiverTotal
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Basic
public import TauCeti.Combinatorics.Quiver.Prefunctor
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

For a monoid `M` and an `M`-invariant subset `U`, `CategoryTheory.ActionCategory.restrict U` is
the inclusion `M ⋉ U ⥤ M ⋉ X` keeping every label; it is fully faithful, so `M ⋉ U` is the
full subcategory of `M ⋉ X` on the points of `U`. When `U` is open, this is the restriction of a
topological action groupoid to a saturated open set of objects.

## Main declarations

* `CategoryTheory.ActionCategory.map`: the functor induced by an equivariant map.
* `CategoryTheory.ActionCategory.map_id`, `CategoryTheory.ActionCategory.map_comp`: it preserves
  identities and composites.
* `CategoryTheory.ActionCategory.faithful_map`: it is faithful along an injective homomorphism.
* `CategoryTheory.ActionCategory.full_map_iff`: it is full exactly when arrows between image
  points lift.
* `CategoryTheory.ActionCategory.restrict`: the full inclusion of the action category on an
  invariant subset.
* `CategoryTheory.ActionCategory.restrictLift`: a functor whose objects lie in the invariant subset
  factors through that inclusion.
* `CategoryTheory.ActionCategory.exists_functor_of_sections`: a functor out of the action category
  on a subset of the objects of a category, given by sections of arrows labelled by the monoid.
* `CategoryTheory.ActionCategory.singleObjFunctor`: the functor `SingleObj K ⥤ M ⋉ X` at a point
  fixed by the image of a monoid homomorphism `K →* M`.
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

/-- In label-source coordinates, the functor induced by an equivariant map applies the
homomorphism to the label and the equivariant map to the source. -/
@[simp]
theorem mapTotal_totalEquiv_symm (m : M) (x : X) :
    (map φ f).toPrefunctor.mapTotal ((totalEquiv M X).symm (m, x)) =
      (totalEquiv N Y).symm (φ m, f x) := by
  apply (totalEquiv N Y).injective
  simp [totalEquiv_apply, objEquiv]

variable (M X) in
/-- The identity map induces the identity functor. -/
theorem map_id : map (MonoidHom.id M) (MulActionHom.id M : X →[M] X) = 𝟭 _ :=
  Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ HEq.rfl

/-- The functor induced by a composite of equivariant maps is the composite of the induced
functors. -/
theorem map_comp {P Z : Type*} [Monoid P] [MulAction P Z] {ψ : N →* P} (g : Y →ₑ[ψ] Z)
    {χ : M →* P} [MonoidHom.CompTriple φ ψ χ] :
    map φ f ⋙ map ψ g = map χ (g.comp f) :=
  Functor.hext (fun _ ↦ rfl) fun _ _ h ↦
    heq_of_eq <| Functor.Elements.hom_ext (MonoidHom.CompTriple.comp_apply ‹_› h.hom)

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

/-- An injective equivariant map for the same monoid induces a full functor, keeping every
arrow label. -/
theorem full_map_of_injective [MulAction M Y] (f : X →[M] Y)
    (hf : Function.Injective f) : (map (MonoidHom.id M) f).Full :=
  (full_map_iff _ _).2 fun x _ m h ↦ ⟨m, rfl, hf ((map_smul f m x).trans h)⟩

section SingleObj

variable {K : Type*} [Monoid K] (φ : K →* M) (x : X) (hx : ∀ k, φ k • x = x)

/-- The functor `SingleObj K ⥤ M ⋉ X` at a point `x` fixed by the image of `φ : K →* M`. It sends
the unique object to `x` and `k` to the arrow `x ⟶ x` labelled `φ k`: this is Mathlib's
`SingleObj.functor` for `φ`, corestricted to the stabilizer of `x` and composed with
`ActionCategory.stabilizerIsoEnd`. Restricting a family of categories over `M ⋉ X` along it gives
a categorical action of `K` on the category over `x`. -/
-- The body is exposed: a family of categories over `M ⋉ X` restricted along this functor must
-- have, definitionally, the category over `x` as its value at the unique object.
@[expose]
def singleObjFunctor : SingleObj K ⥤ ActionCategory M X :=
  SingleObj.functor ((stabilizerIsoEnd M x).toMonoidHom.comp
    (φ.codRestrict _ fun k => mem_stabilizerSubmonoid_iff.mpr (hx k)))

/-- The functor at a fixed point sends the unique object to that point. -/
@[simp]
theorem singleObjFunctor_obj (a : SingleObj K) :
    (singleObjFunctor φ x hx).obj a = objEquiv M X x := (rfl)

/-- The functor at a fixed point labels the arrow of `k` by `φ k`. -/
@[simp]
theorem singleObjFunctor_map_hom {a b : SingleObj K} (k : a ⟶ b) :
    ((singleObjFunctor φ x hx).map k).hom = φ k := (rfl)

end SingleObj

end Map

section Restrict

variable {M : Type*} [Monoid M] {X : Type*} [MulAction M X]

/-- The inclusion `M ⋉ U ⥤ M ⋉ X` of the action category on an invariant subset `U`. It sends a
point of `U` to itself and keeps each label, so it identifies `M ⋉ U` with the full subcategory
of `M ⋉ X` on the points of `U`. -/
def restrict (U : SubMulAction M X) : ActionCategory M U ⥤ ActionCategory M X :=
  map (MonoidHom.id M) { toFun := Subtype.val, map_smul' := fun _ _ => rfl }

variable (U : SubMulAction M X)

/-- The restriction inclusion is the functor induced by the inclusion of `U`, keeping labels. -/
theorem restrict_eq_map :
    restrict U = map (MonoidHom.id M) { toFun := Subtype.val, map_smul' := fun _ _ => rfl } :=
  (rfl)

/-- The point underlying the image of an object under the restriction inclusion is its point. -/
@[simp]
theorem back_restrict_obj (a : ActionCategory M U) : ((restrict U).obj a).back = (a.back : X) :=
  (rfl)

/-- The restriction inclusion keeps the label of each arrow. -/
@[simp]
theorem restrict_map_hom {a b : ActionCategory M U} (g : a ⟶ b) :
    ((restrict U).map g).hom = g.hom := (rfl)

/-- The restriction inclusion is faithful. -/
instance faithful_restrict : (restrict U).Faithful :=
  faithful_map _ _ fun _ _ h => h

/-- The restriction inclusion is full: every arrow between points of `U` lies in `M ⋉ U`. -/
instance full_restrict : (restrict U).Full :=
  full_map_of_injective _ Subtype.val_injective

/-- A functor into `M ⋉ X` all of whose objects lie in the invariant subset `U` factors through
`M ⋉ U`: this lifts it along the restriction inclusion. -/
def restrictLift {J : Type*} [Category J] (F : J ⥤ ActionCategory M X)
    (hF : ∀ j, (F.obj j).back ∈ U) : J ⥤ ActionCategory M U where
  obj j := objEquiv M U ⟨(F.obj j).back, hF j⟩
  map g := Functor.Elements.homMk (F.map g).hom (Subtype.ext (F.map g).map_val)
  map_id j := Functor.Elements.hom_ext
    ((congrArg Functor.Elements.Hom.hom (F.map_id j)).trans (ActionCategory.id_hom _))
  map_comp g g' := Functor.Elements.hom_ext
    ((congrArg Functor.Elements.Hom.hom (F.map_comp g g')).trans (ActionCategory.comp_hom _ _))

/-- The lift of a functor along the restriction inclusion sends an object to the point of `U`
underlying its image. -/
@[simp]
theorem back_restrictLift_obj {J : Type*} [Category J] (F : J ⥤ ActionCategory M X)
    (hF : ∀ j, (F.obj j).back ∈ U) (j : J) :
    ((restrictLift U F hF).obj j).back = ⟨(F.obj j).back, hF j⟩ := (rfl)

/-- The lift of a functor along the restriction inclusion keeps the label of each arrow. -/
@[simp]
theorem restrictLift_map_hom {J : Type*} [Category J] (F : J ⥤ ActionCategory M X)
    (hF : ∀ j, (F.obj j).back ∈ U) {j j' : J} (g : j ⟶ j') :
    ((restrictLift U F hF).map g).hom = (F.map g).hom := (rfl)

/-- The lift of a functor along the restriction inclusion recovers the functor. -/
@[simp]
theorem restrictLift_comp_restrict {J : Type*} [Category J] (F : J ⥤ ActionCategory M X)
    (hF : ∀ j, (F.obj j).back ∈ U) : restrictLift U F hF ⋙ restrict U = F :=
  (rfl)

end Restrict

section Inclusion

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] {H : Subgroup G}

/-- The inclusion `H ⋉ S ⥤ G ⋉ X` of the action category of a subgroup `H` on an `H`-invariant
subset `S`. It sends a point of `S` to itself and keeps each label of `H` as an element of `G`. -/
def inclusion (S : SubMulAction H X) : ActionCategory H S ⥤ ActionCategory G X :=
  map H.subtype { toFun := Subtype.val, map_smul' := fun _ _ => rfl }

variable (S : SubMulAction H X)

/-- The inclusion is the functor induced by the inclusion of `S` along the inclusion of `H`. -/
theorem inclusion_eq_map :
    inclusion S = map H.subtype { toFun := Subtype.val, map_smul' := fun _ _ => rfl } :=
  (rfl)

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
    Set.range (inclusion S).toPrefunctor.mapTotal = {f | f.left.back ∈ S ∧ f.right.back ∈ S} := by
  ext ⟨l, r, g⟩
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨⟨a, b, f⟩, hf⟩
    rw [Prefunctor.mapTotal_mk] at hf
    cases hf
    simp
  · have := (full_inclusion_iff S).mpr hS
    obtain ⟨a, rfl⟩ : l ∈ Set.range (inclusion S).obj := by
      simpa [range_inclusion_obj] using hf.1
    obtain ⟨b, rfl⟩ : r ∈ Set.range (inclusion S).obj := by
      simpa [range_inclusion_obj] using hf.2
    exact ⟨⟨a, b, (inclusion S).preimage g⟩, (Prefunctor.mapTotal_mk _ _).trans <|
      congrArg (Quiver.Total.mk _ _) ((inclusion S).map_preimage g)⟩

end Inclusion

section OfSections

variable {M : Type*} [Monoid M] {C : Type*} [Category C]

/-- A functor out of the action category of a monoid acting on a subset `U` of the objects of `C`,
given by a section `σ g y` of arrows with source `y` for each label `g` and point `y`: it is the
identity on objects and sends the arrow labelled `g` at `a` to the arrow `σ g a`. The sections
must have the unit and composition behaviour of the action: `σ 1 y` is the identity at `y`, and
`σ (g * h) y` is `σ h y` followed by `σ g` at the target of `σ h y`. -/
theorem exists_functor_of_sections {U : Set C} [MulAction M U] {σ : M → C → Quiver.Total C}
    (hsmul : ∀ (g : M) (y : U), ((g • y : U) : C) = (σ g y).right)
    (hσl : ∀ g : M, ∀ y ∈ U, (σ g y).left = y)
    (hUσ : ∀ y ∈ U, ∀ h : M, (σ h y).right ∈ U)
    (hone : ∀ y ∈ U, σ 1 y = ⟨y, y, 𝟙 y⟩)
    (hmul : ∀ y (hy : y ∈ U) (g h : M), σ (g * h) y =
      (σ h y).comp (σ g (σ h y).right) (hσl g _ (hUσ y hy h)).symm) :
    ∃ F : ActionCategory M U ⥤ C, (∀ a, F.obj a = (a.back : C)) ∧
      ∀ {a b : ActionCategory M U} (f : a ⟶ b),
        (⟨_, _, F.map f⟩ : Quiver.Total C) = σ f.hom a.back := by
  let F : ActionCategory M U ⥤ C :=
    { obj a := a.back
      map {a b} f := Quiver.homOfEq (σ f.hom a.back).hom (hσl _ _ a.back.2)
        ((hsmul _ _).symm.trans (congrArg Subtype.val f.map_val))
      map_id a := eq_of_heq (Quiver.Total.mk.inj ((Quiver.Total.mk_homOfEq _ _ _).trans (by
        rw [ActionCategory.id_hom]
        exact hone _ a.back.2))).2.2
      map_comp {a b c} f g := eq_of_heq (Quiver.Total.mk.inj
        ((Quiver.Total.mk_homOfEq _ _ _).trans <| Eq.trans (by
          rw [ActionCategory.comp_hom, hmul _ a.back.2]
          exact Quiver.Total.comp_congr rfl
            (congrArg (σ g.hom) ((hsmul _ _).symm.trans (congrArg Subtype.val f.map_val))) _ _)
          (Quiver.Total.mk_homOfEq_comp_homOfEq _ _ _ _ _ _).symm)).2.2 }
  exact ⟨F, fun _ ↦ rfl, fun _ ↦ Quiver.Total.mk_homOfEq _ _ _⟩

end OfSections

end CategoryTheory.ActionCategory
