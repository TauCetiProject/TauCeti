/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.AlgebraicGeometry.RationalPoint.Geometric
public import TauCeti.AlgebraicGeometry.Scheme.SpecAlgHom
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint

/-!
# The Galois action on stalks of étale sheaves on a field

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x : Spec Ω ⟶ Spec K`
(`TauCeti.AlgebraicGeometry.Scheme.galoisGeometricPoint`). Every `σ ∈ Gal(Ω/K)` gives an
automorphism `Spec σ` of `Spec Ω` over `Spec K`, that is an automorphism of this geometric point,
and automorphisms of a geometric point act on its stalks
(`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.stalkAction`). Since `Spec` reverses
composition, this is a left action of `Gal(Ω/K)` on the stalk at `x` of every étale sheaf on
`Spec K`, natural in the sheaf, so the stalk at `x` is a functor
(`TauCeti.AlgebraicGeometry.Scheme.galoisStalk`)

`Sheaf (smallEtaleTopology (Spec K)) A ⥤ Action A Gal(Ω/K)`

for every coefficient category `A` with colimits. For concrete coefficients whose forgetful
functor preserves filtered colimits, such as sets or modules, the action is continuous for the
discrete topology on the stalk and the Krull topology on `Gal(Ω/K)`: every element of the stalk
has an open stabilizer (`TauCeti.AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`).
Indeed, an element of the stalk is represented by a section over an étale `K`-scheme `X` together
with a lift `t : Spec Ω ⟶ X` of `x`. The lift `t` is a point `y` of `X` with an embedding
`κ(y) → Ω`, and `κ(y)` is a finite extension of `K` because étale morphisms are locally
quasi-finite. Every `σ` fixing the image of `κ(y)` fixes `t`, and the elements of `Gal(Ω/K)` fixing
a finite extension of `K` in `Ω` form an open subgroup.

The functor `galoisStalk` lands in `Action A Gal(Ω/K)`. When `Ω` is a separable closure of `K`,
together with `isOpen_stabilizer_galoisStalk` it supplies the forward data of the classification
of étale sheaves on a field by discrete continuous `Gal(Ω/K)`-sets (SGA 4, Exposé VIII, §2).

## Main definitions

* `TauCeti.AlgebraicGeometry.Scheme.galoisGeometricPoint K Ω`: the geometric point
  `Spec Ω ⟶ Spec K`.
* `TauCeti.AlgebraicGeometry.Scheme.galoisGeometricPointAut K Ω`: the homomorphism sending
  `σ ∈ Gal(Ω/K)` to the automorphism `Spec σ` of `galoisGeometricPoint K Ω`.
* `TauCeti.AlgebraicGeometry.Scheme.galoisStalkMap K Ω A σ`: the endomorphism of stalks at
  `Spec Ω ⟶ Spec K` induced by `σ`, natural in the sheaf.
* `TauCeti.AlgebraicGeometry.Scheme.galoisStalk K Ω A`: the stalk at `Spec Ω ⟶ Spec K` of an
  étale sheaf on `Spec K`, with its action of `Gal(Ω/K)`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.smul_toPresheafFiber_galoisStalk`: `σ` sends the germ at a
  lift `t` to the germ at `Spec σ ≫ t`.
* `TauCeti.AlgebraicGeometry.Scheme.isOpen_stabilizer_galoisStalk`: for an étale sheaf with values
  in a concrete category whose forgetful functor preserves filtered colimits (such as sets or
  modules), the stabilizer in `Gal(Ω/K)` of every element of the stalk is open.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe w v u

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme (pointSmallEtale smallEtaleTopology)

namespace TauCeti.AlgebraicGeometry.Scheme

section Galois

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

variable [IsSepClosed Ω]

/-- The geometric point `Spec Ω ⟶ Spec K` of `Spec K` given by the algebra map `K → Ω`. -/
noncomputable abbrev galoisGeometricPoint : GeometricPoint (Spec (.of K)) where
  Ω := Ω
  hom := Spec.map (CommRingCat.ofHom (algebraMap K Ω))

/-- The automorphism `Spec σ` of the geometric point `Spec Ω ⟶ Spec K` given by `σ ∈ Gal(Ω/K)`. -/
noncomputable def galoisGeometricPointIso (σ : Gal(Ω/K)) :
    galoisGeometricPoint K Ω ≅ galoisGeometricPoint K Ω :=
  GeometricPoint.isoMk (Scheme.Spec.mapIso σ.toRingEquiv.toCommRingCatIso.op)
    (Spec.map_algHom_comp_map_algebraMap σ)

/-- The automorphism of the geometric point given by `σ` is `Spec σ`. -/
@[simp]
theorem galoisGeometricPointIso_hom_hom (σ : Gal(Ω/K)) :
    (galoisGeometricPointIso K Ω σ).hom.hom = Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) :=
  GeometricPoint.isoMk_hom_hom _ _

/-- The inverse of the automorphism of the geometric point given by `σ` is `Spec σ⁻¹`. -/
@[simp]
theorem galoisGeometricPointIso_inv_hom (σ : Gal(Ω/K)) :
    (galoisGeometricPointIso K Ω σ).inv.hom = Spec.map (CommRingCat.ofHom (σ.symm : Ω →+* Ω)) :=
  GeometricPoint.isoMk_inv_hom _ _

/-- `σ ↦ Spec σ` as a homomorphism from `Gal(Ω/K)` to the automorphisms of the geometric point
`Spec Ω ⟶ Spec K`. Since `Spec (σ * τ) = Spec σ ≫ Spec τ` and `Aut` multiplies in the order of
function composition, it lands in the opposite group. -/
noncomputable def galoisGeometricPointAut : Gal(Ω/K) →* (Aut (galoisGeometricPoint K Ω))ᵐᵒᵖ where
  toFun σ := .op (.of (galoisGeometricPointIso K Ω σ))
  map_one' := by
    ext1
    simp only [MulOpposite.unop_op, MulOpposite.unop_one, Aut.one_asIso, Iso.refl_hom,
      GeometricPoint.id_hom, galoisGeometricPointIso_hom_hom, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (AlgEquiv.one_apply (R := K))))
  map_mul' σ τ := by
    ext1
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Aut.mul_asIso, Iso.trans_hom,
      GeometricPoint.comp_hom, galoisGeometricPointIso_hom_hom, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (AlgEquiv.mul_apply σ τ)))

/-- `σ` gives the automorphism `galoisGeometricPointIso K Ω σ` of the geometric point. -/
@[simp]
theorem galoisGeometricPointAut_apply (σ : Gal(Ω/K)) :
    (galoisGeometricPointAut K Ω σ).unop.asIso = galoisGeometricPointIso K Ω σ :=
  (rfl)

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- The endomorphism of the stalk at `Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K` induced by
`σ ∈ Gal(Ω/K)`, natural in the sheaf. -/
noncomputable def galoisStalkMap (σ : Gal(Ω/K)) :
    (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber (A := A) ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  ((GeometricPoint.stalkAction A (galoisGeometricPoint K Ω)).comp
    (galoisGeometricPointAut K Ω) σ).asIso.hom

/-- The identity of `Gal(Ω/K)` acts trivially on stalks. -/
@[simp]
theorem galoisStalkMap_one : galoisStalkMap K Ω A 1 = 𝟙 _ :=
  congrArg (·.asIso.hom)
    (map_one ((GeometricPoint.stalkAction A _).comp (galoisGeometricPointAut K Ω)))

/-- The Galois action on stalks is a left action: `σ * τ` acts by `τ` followed by `σ`. -/
@[reassoc, simp]
theorem galoisStalkMap_mul (σ τ : Gal(Ω/K)) :
    galoisStalkMap K Ω A (σ * τ) = galoisStalkMap K Ω A τ ≫ galoisStalkMap K Ω A σ :=
  congrArg (·.asIso.hom)
    (map_mul ((GeometricPoint.stalkAction A _).comp (galoisGeometricPointAut K Ω)) σ τ)

/-- `σ ∈ Gal(Ω/K)` sends the germ at a lift `t` of a section of an étale sheaf on `Spec K` to its
germ at the lift `Spec σ ≫ t`. -/
@[simp]
theorem toPresheafFiber_galoisStalkMap_app (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X) :
    (pointSmallEtale _).toPresheafFiber X t F.obj ≫ (galoisStalkMap K Ω A σ).app F =
      (pointSmallEtale _).toPresheafFiber X
        (((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t)
        F.obj := by
  simp only [galoisStalkMap, MonoidHom.coe_comp, Function.comp_apply,
    GeometricPoint.stalkAction_apply, galoisGeometricPointAut_apply, Functor.whiskerLeft_app,
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
        (((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t)
        F.obj ≫ h :=
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
        (((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t)
        F.obj z :=
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
      (pointSmallEtale _).toPresheafFiber X
        (((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t)
        F.obj z := by
  rw [← toPresheafFiber_galoisStalkMap_app_apply, ← galoisStalk_obj_ρ_asHom]
  exact (Action.ρ_apply_eq_smul _ σ _).symm

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
    X.hom.exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq t.left (Over.w t)
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
    (fun σ hσ ↦ MulAction.mem_stabilizer_iff.mpr ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht :
      ((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t = t :=
    Over.OverMorphism.ext <| (GeometricPoint.toPointFunctor_map_hom_app_left
      (galoisGeometricPointIso K Ω σ).hom X t).trans <|
        (congrArg (· ≫ t.left) (galoisGeometricPointIso_hom_hom K Ω σ)).trans (hL σ hσ)
  -- `σ` acts on `p` through `galoisStalkMap`, which sends the germ at `t` to the germ at `t`.
  subst hp
  rw [smul_toPresheafFiber_galoisStalk, ht]

end Concrete

end Galois

end TauCeti.AlgebraicGeometry.Scheme
