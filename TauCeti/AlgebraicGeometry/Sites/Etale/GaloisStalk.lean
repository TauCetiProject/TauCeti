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
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint

/-!
# The Galois action on stalks of étale sheaves on a field

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x : Spec Ω ⟶ Spec K`
(`TauCeti.AlgebraicGeometry.Scheme.galoisGeometricPoint`, in
`TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint` with the automorphisms
`galoisGeometricPointAut`). Every `σ ∈ Gal(Ω/K)` gives an
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

* `TauCeti.AlgebraicGeometry.Scheme.galoisStalkMap K Ω A σ`: the endomorphism of stalks at
  `Spec Ω ⟶ Spec K` induced by `σ`, natural in the sheaf.
* `TauCeti.AlgebraicGeometry.Scheme.galoisStalk K Ω A`: the stalk at `Spec Ω ⟶ Spec K` of an
  étale sheaf on `Spec K`, with its action of `Gal(Ω/K)`.
* `TauCeti.AlgebraicGeometry.Scheme.galoisStalkForgetIso K Ω A`: the natural isomorphism between
  the underlying object of `galoisStalk K Ω A` and the stalk.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.smul_galoisStalkForgetIso_inv_app_toPresheafFiber`: `σ` sends
  the germ at a lift `t` to the germ at `Spec σ ≫ t`.
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
automorphisms `Spec σ` of the geometric point. Its underlying object is identified with the
stalk by `galoisStalkForgetIso`, through which the action and naturality lemmas are stated. -/
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

/-- The underlying object of the stalk with its Galois action is the stalk, naturally in the
sheaf. -/
noncomputable def galoisStalkForgetIso :
    galoisStalk K Ω A ⋙ Action.forget A Gal(Ω/K) ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber :=
  Iso.refl _

/-- `σ ∈ Gal(Ω/K)` acts on the stalk by `galoisStalkMap K Ω A σ`, read through
`galoisStalkForgetIso`. -/
@[reassoc (attr := simp)]
theorem galoisStalkForgetIso_inv_app_comp_ρ (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (σ : Gal(Ω/K)) :
    (galoisStalkForgetIso K Ω A).inv.app F ≫ (((galoisStalk K Ω A).obj F).ρ σ).asHom =
      (galoisStalkMap K Ω A σ).app F ≫ (galoisStalkForgetIso K Ω A).inv.app F := by
  simp only [galoisStalkForgetIso, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).trans (Category.comp_id ((galoisStalkMap K Ω A σ).app F)).symm

/-- The equivariant map of stalks induced by a morphism of sheaves is the map of stalks, read
through `galoisStalkForgetIso`. -/
@[reassoc (attr := simp)]
theorem galoisStalk_map_hom_comp_galoisStalkForgetIso_hom
    {F G : Sheaf (smallEtaleTopology (Spec (.of K))) A} (f : F ⟶ G) :
    ((galoisStalk K Ω A).map f).hom ≫ (galoisStalkForgetIso K Ω A).hom.app G =
      (galoisStalkForgetIso K Ω A).hom.app F ≫
        (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).sheafFiber.map f :=
  (galoisStalkForgetIso K Ω A).hom.naturality f

section Concrete

variable {A : Type (v + 1)} [LargeCategory A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasColimitsOfSize.{u, u} A]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

omit [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)] in
/-- `σ ∈ Gal(Ω/K)` sends the germ of a section at a lift `t` of the geometric point, as an element
of `(galoisStalk K Ω A).obj F` through `galoisStalkForgetIso`, to its germ at the lift
`Spec σ ≫ t`. -/
@[simp]
theorem smul_galoisStalkForgetIso_inv_app_toPresheafFiber (σ : Gal(Ω/K))
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) (X : (Spec (.of K)).Etale)
    (t : (pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).fiber.obj X)
    (z : ToType (F.obj.obj (op X))) :
    HSMul.hSMul (β := ToType ((galoisStalk K Ω A).obj F)) σ
        ((galoisStalkForgetIso K Ω A).inv.app F
          ((pointSmallEtale _).toPresheafFiber X t F.obj z)) =
      (galoisStalkForgetIso K Ω A).inv.app F ((pointSmallEtale _).toPresheafFiber X
        (((GeometricPoint.toPointFunctor _).map (galoisGeometricPointIso K Ω σ).hom).hom.app X t)
        F.obj z) := by
  have := congr($(galoisStalkForgetIso_inv_app_comp_ρ K Ω A F σ)
    ((pointSmallEtale _).toPresheafFiber X t F.obj z))
  exact (Action.ρ_apply_eq_smul _ σ _).symm.trans <|
    (ConcreteCategory.comp_apply _ _ _).symm.trans <| this.trans <|
      (ConcreteCategory.comp_apply _ _ _).trans <|
        congrArg _ (toPresheafFiber_galoisStalkMap_app_apply K Ω A σ F X t z)

/-- **Point stabilizers of the Galois action on stalks are open**: for an étale sheaf `F` on
`Spec K` with values in a concrete category whose forgetful functor preserves filtered colimits,
such as sets or modules, the stabilizer in `Gal(Ω/K)` of every element of
`(galoisStalk K Ω A).obj F` is open in the Krull topology. -/
theorem isOpen_stabilizer_galoisStalk (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (p : ToType ((galoisStalk K Ω A).obj F)) :
    IsOpen (MulAction.stabilizer Gal(Ω/K) p : Set Gal(Ω/K)) := by
  -- `p` is the germ of a section `z` over an étale `K`-scheme `X` at a lift `t` of the geometric
  -- point, and `t` is fixed by the fixing subgroup of a finite extension `L` of `K`, which is open.
  obtain ⟨X, t, z, hp⟩ := (pointSmallEtale _).toPresheafFiber_jointly_surjective (P := F.obj)
    ((galoisStalkForgetIso K Ω A).hom.app F p)
  have hp' : (galoisStalkForgetIso K Ω A).inv.app F
      ((pointSmallEtale _).toPresheafFiber X t F.obj z) = p := by
    rw [hp, ← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply]
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
  rw [← hp', smul_galoisStalkForgetIso_inv_app_toPresheafFiber, ht]

end Concrete

end Galois

end TauCeti.AlgebraicGeometry.Scheme
