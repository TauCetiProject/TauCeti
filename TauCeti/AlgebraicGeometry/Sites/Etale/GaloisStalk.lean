/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint

/-!
# The Galois action on stalks of étale sheaves on a field

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x : Spec Ω ⟶ Spec K`. Every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of
`Spec Ω` over `Spec K`, that is an endomorphism of the geometric point
`AlgebraicGeometry.Scheme.galoisGeometricPoint K Ω`, hence an endomorphism of the point
`pointSmallEtale x` (through `TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.toPointFunctor`),
hence an endomorphism of the stalk at `x` of every étale sheaf on `Spec K`. This is a left action of
`Gal(Ω/K)`, natural in the sheaf, so the stalk at `x` is a functor
(`AlgebraicGeometry.Scheme.galoisStalk`)

`Sheaf (smallEtaleTopology (Spec K)) A ⥤ Action A Gal(Ω/K)`

for every coefficient category `A` with colimits. For concrete coefficients whose forgetful
functor preserves filtered colimits, such as sets or modules, the action is continuous for the
discrete topology on the stalk and the Krull topology on `Gal(Ω/K)`: every element of the stalk
has an open stabilizer (`AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`). Indeed,
an element of the stalk is represented by a section over an étale `K`-scheme `X` together with a
lift `t : Spec Ω ⟶ X` of `x`. The lift `t` is a point `y` of `X` with an embedding `κ(y) → Ω`,
and `κ(y)` is a finite extension of `K` because étale morphisms are locally quasi-finite. Every
`σ` fixing the image of `κ(y)` fixes `t`, and the elements of `Gal(Ω/K)` fixing a finite
extension of `K` in `Ω` form an open subgroup.

The functor `galoisStalk` lands in `Action A Gal(Ω/K)`. When `Ω` is a separable closure of `K`,
together with `isOpen_stabilizer_galoisStalk` it supplies the forward data of the classification
of étale sheaves on a field by discrete continuous `Gal(Ω/K)`-sets (SGA 4, Exposé VIII, §2).

## Main definitions

* `AlgebraicGeometry.Scheme.galoisGeometricPoint K Ω`: the geometric point `Spec Ω ⟶ Spec K`.
* `AlgebraicGeometry.Scheme.galoisGeometricPointHom K Ω σ`: the endomorphism `Spec σ` of
  `galoisGeometricPoint K Ω` for `σ ∈ Gal(Ω/K)`, and `AlgebraicGeometry.Scheme.galoisPointHom` the
  induced endomorphism of the point of the small étale site.
* `AlgebraicGeometry.Scheme.galoisStalk K Ω A`: the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf
  on `Spec K`, with its action of `Gal(Ω/K)`.

## Main results

* `AlgebraicGeometry.Scheme.smul_toPresheafFiber_galoisStalk`: `σ` sends the germ at a lift `t`
  to the germ at `Spec σ ≫ t`.
* `AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`: for an étale sheaf with values in a
  concrete category whose forgetful functor preserves filtered colimits (such as sets or modules),
  the stabilizer in `Gal(Ω/K)` of every element of the stalk is open.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe w v u

open CategoryTheory Limits Opposite
open TauCeti.AlgebraicGeometry.Scheme (GeometricPoint)

namespace AlgebraicGeometry.Scheme


section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

variable [IsSepClosed Ω]

/-- The geometric point `Spec Ω ⟶ Spec K` of `Spec K` given by the algebra map `K → Ω`. -/
noncomputable abbrev galoisGeometricPoint : GeometricPoint (Spec (.of K)) where
  Ω := Ω
  hom := Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- The endomorphism `Spec σ` of the geometric point `Spec Ω ⟶ Spec K` given by `σ ∈ Gal(Ω/K)`. -/
noncomputable def galoisGeometricPointHom (σ : Gal(Ω/K)) :
    galoisGeometricPoint K Ω ⟶ galoisGeometricPoint K Ω :=
  GeometricPoint.homMk
    (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (Spec.map_algHom_comp_map_algebraMap σ)

/-- The endomorphism of the geometric point given by `σ` is `Spec σ`. -/
@[simp]
theorem galoisGeometricPointHom_hom (σ : Gal(Ω/K)) :
    (galoisGeometricPointHom K Ω σ).hom = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) :=
  (rfl)

/-- The identity of `Gal(Ω/K)` gives the identity of the geometric point. -/
@[simp]
theorem galoisGeometricPointHom_one : galoisGeometricPointHom K Ω 1 = 𝟙 _ := by
  ext1
  rw [galoisGeometricPointHom_hom, GeometricPoint.id_hom,
    ← Spec.map_id, ← CommRingCat.ofHom_id]
  rfl

/-- `σ * τ` gives the composite `Spec σ ≫ Spec τ` of geometric points. -/
theorem galoisGeometricPointHom_mul (σ τ : Gal(Ω/K)) :
    galoisGeometricPointHom K Ω (σ * τ) =
      galoisGeometricPointHom K Ω σ ≫ galoisGeometricPointHom K Ω τ := by
  ext1
  rw [GeometricPoint.comp_hom, galoisGeometricPointHom_hom,
    galoisGeometricPointHom_hom, galoisGeometricPointHom_hom, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rfl

/-- The endomorphism of the point `pointSmallEtale x` of the small étale site of `Spec K`, for the
geometric point `x : Spec Ω ⟶ Spec K`, induced by `σ ∈ Gal(Ω/K)`: a lift `t` of `x` goes to the
lift `Spec σ ≫ t`. -/
noncomputable def galoisPointHom (σ : Gal(Ω/K)) :
    pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  (GeometricPoint.toPointFunctor _).map (galoisGeometricPointHom K Ω σ)

/-- `σ ∈ Gal(Ω/K)` sends a lift `t` of the geometric point to the lift `Spec σ ≫ t`. -/
@[simp]
theorem galoisPointHom_hom_app_left (σ : Gal(Ω/K)) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    ((galoisPointHom K Ω σ).hom.app X t).left =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t.left :=
  (rfl)

/-- The identity of `Gal(Ω/K)` gives the identity of the point. -/
@[simp]
theorem galoisPointHom_one : galoisPointHom K Ω 1 = 𝟙 _ :=
  (congrArg (GeometricPoint.toPointFunctor _).map (galoisGeometricPointHom_one K Ω)).trans
    ((GeometricPoint.toPointFunctor _).map_id _)

/-- `σ * τ` gives the composite of the endomorphisms of the point given by `σ` and `τ`. -/
theorem galoisPointHom_mul (σ τ : Gal(Ω/K)) :
    galoisPointHom K Ω (σ * τ) = galoisPointHom K Ω σ ≫ galoisPointHom K Ω τ :=
  (congrArg (GeometricPoint.toPointFunctor _).map (galoisGeometricPointHom_mul K Ω σ τ)).trans
    ((GeometricPoint.toPointFunctor _).map_comp _ _)

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The endomorphism of the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K` induced by
`σ ∈ Gal(Ω/K)`, natural in the sheaf. -/
noncomputable def galoisStalkMap (σ : Gal(Ω/K)) :
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber (A := A) ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  GrothendieckTopology.Point.Hom.sheafFiber (galoisPointHom K Ω σ)

/-- The identity of `Gal(Ω/K)` acts trivially on stalks. -/
@[simp]
theorem galoisStalkMap_one : galoisStalkMap K Ω A 1 = 𝟙 _ := by
  rw [galoisStalkMap, galoisPointHom_one, GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- The Galois action on stalks is a left action: `σ * τ` acts by `τ` followed by `σ`. -/
@[reassoc, simp]
theorem galoisStalkMap_mul (σ τ : Gal(Ω/K)) :
    galoisStalkMap K Ω A (σ * τ) = galoisStalkMap K Ω A τ ≫ galoisStalkMap K Ω A σ := by
  rw [galoisStalkMap, galoisStalkMap, galoisStalkMap, galoisPointHom_mul,
    GrothendieckTopology.Point.Hom.sheafFiber_comp]

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section of an étale sheaf on `Spec K` to its
germ at the lift `Spec σ ≫ t`. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F =
      (pointSmallEtale _).toPresheafFiber X
        ((galoisPointHom K Ω σ).hom.app X t) F.obj := by
  simp only [galoisStalkMap, Functor.whiskerLeft_app,
    GrothendieckTopology.Point.Hom.presheafFiber_app]
  exact GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc _ _ _ _ _

-- `reassoc` and `elementwise` cannot generate these two forms: the germ lands in the presheaf
-- fiber, while `(galoisStalkMap K Ω A σ).app F` starts at the sheaf fiber, and the two objects
-- are only equal after unfolding `sheafFiber`, so `Category.assoc` does not rewrite the
-- composite and the generated lemmas keep it left-associated.

/-- Version of `toPresheafFiber_galoisStalkMap_app` for a right-associated composite. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app_assoc (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) {Z : A}
    (h : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F ⟶ Z) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F ≫ h =
      (pointSmallEtale _).toPresheafFiber X
        ((galoisPointHom K Ω σ).hom.app X t) F.obj ≫ h :=
  (Category.assoc _ _ _).symm.trans
    (eq_whisker (toPresheafFiber_galoisStalkMap_app K Ω A σ F X t) h)

/-- Elementwise version of `toPresheafFiber_galoisStalkMap_app`, on germs of sections, for
concrete coefficients. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app_apply {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z : ToType (F.obj.obj (op X))) :
    (galoisStalkMap K Ω A σ).app F ((pointSmallEtale _).toPresheafFiber X t F.obj z) =
      (pointSmallEtale _).toPresheafFiber X
        ((galoisPointHom K Ω σ).hom.app X t) F.obj z :=
  (ConcreteCategory.comp_apply _ _ z).symm.trans
    congr($(toPresheafFiber_galoisStalkMap_app K Ω A σ F X t) z)

/-- **The Galois action on stalks of étale sheaves on a field.** The stalk at the geometric point
`Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K`, with the action of `Gal(Ω/K)` through the
automorphisms `Spec σ` of the geometric point. -/
@[expose]
noncomputable def galoisStalk :
    Sheaf (smallEtaleTopology (Spec (.of K))) A ⥤ Action A Gal(Ω/K) where
  obj F :=
    { V := (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F
      ρ :=
        { toFun σ := .of ((galoisStalkMap K Ω A σ).app F)
          map_one' := by
            ext1
            simp
          map_mul' σ τ := by
            ext1
            simp } }
  map f :=
    { hom := (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f
      comm σ := ((galoisStalkMap K Ω A σ).naturality f).symm }

/-- The underlying object of the stalk with its Galois action is the stalk. -/
theorem galoisStalk_obj_V (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) :
    ((galoisStalk K Ω A).obj F).V =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.obj F :=
  (rfl)

/-- `σ ∈ Gal(Ω/K)` acts on the stalk by `galoisStalkMap K Ω A σ`. -/
@[simp]
theorem galoisStalk_obj_ρ_asHom (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (σ : Gal(Ω/K)) :
    (((galoisStalk K Ω A).obj F).ρ σ).asHom = (galoisStalkMap K Ω A σ).app F :=
  (rfl)

/-- The equivariant map of stalks induced by a morphism of sheaves is the map of stalks. -/
@[simp]
theorem galoisStalk_map_hom {F G : Sheaf (smallEtaleTopology (Spec (.of K))) A} (f : F ⟶ G) :
    ((galoisStalk K Ω A).map f).hom =
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f :=
  (rfl)

section Concrete

variable {A : Type (v + 1)} [LargeCategory A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

omit [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)] in
/-- `σ ∈ Gal(Ω/K)` sends the germ of a section at a lift `t` of the geometric point, as an element
of `(galoisStalk K Ω A).obj F`, to its germ at the lift `Spec σ ≫ t`. -/
@[simp]
theorem smul_toPresheafFiber_galoisStalk (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z : ToType (F.obj.obj (op X))) :
    HSMul.hSMul (β := ToType ((galoisStalk K Ω A).obj F)) σ
        ((pointSmallEtale _).toPresheafFiber X t F.obj z) =
      (pointSmallEtale _).toPresheafFiber X ((galoisPointHom K Ω σ).hom.app X t) F.obj z :=
  toPresheafFiber_galoisStalkMap_app_apply K Ω A σ F X t z

/-- **Point stabilizers of the Galois action on stalks are open**: for an étale sheaf `F` on
`Spec K` with values in a concrete category whose forgetful functor preserves filtered colimits,
such as sets or modules, the stabilizer in `Gal(Ω/K)` of every element of
`(galoisStalk K Ω A).obj F` is open in the Krull topology. -/
theorem isOpen_stabilizer_galoisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (p : ToType ((galoisStalk K Ω A).obj F)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) p : Set Gal(Ω/K)) := by
  -- `p` is the germ of a section `z` over an étale `K`-scheme `X` at a lift `t` of the geometric
  -- point, and `t` is fixed by the fixing subgroup of a finite extension `L` of `K`, which is open.
  obtain ⟨X, t, z, hp⟩ := (pointSmallEtale _).toPresheafFiber_jointly_surjective (P := F.obj) p
  have : Etale X.hom := X.prop
  obtain ⟨L, _, hL⟩ :=
    exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq K Ω X.hom t.left (Over.w t)
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
    (fun σ hσ ↦ MulAction.mem_stabilizer_iff.mpr ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht : (galoisPointHom K Ω σ).hom.app X t = t :=
    Over.OverMorphism.ext ((galoisPointHom_hom_app_left K Ω σ X t).trans (hL σ hσ))
  -- `σ` acts on `p` through `galoisStalkMap`, which sends the germ at `t` to the germ at `t`.
  subst hp
  rw [smul_toPresheafFiber_galoisStalk, ht]

end Concrete

end Galois

end AlgebraicGeometry.Scheme
