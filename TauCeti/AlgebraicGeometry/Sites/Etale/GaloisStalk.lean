/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.RationalPoint.Geometric
public import TauCeti.AlgebraicGeometry.Sites.Etale.GeometricPoint.Galois

/-!
# The Galois action on stalks of étale sheaves on a field

Let `K` be a field and `Ω` a separably closed field with an algebra map `K → Ω`, giving the
geometric point `x := GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω` with underlying morphism
`x.hom : Spec Ω ⟶ Spec K`. Every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of `Spec Ω` over
`Spec K`, that is an automorphism of `x`, and automorphisms of a geometric point act on its stalks
(`TauCeti.AlgebraicGeometry.Scheme.GeometricPoint.ofOverGaloisStalkAction`). Since `Spec` reverses
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

variable (A : Type v) [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- **The Galois action on stalks of étale sheaves on a field.** The stalk at the geometric point
`Spec Ω ⟶ Spec K` of an étale sheaf on `Spec K`, with the action of `Gal(Ω/K)` through the
automorphisms `Spec σ` of `GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω`. -/
@[expose]
noncomputable def galoisStalk :
    Sheaf (smallEtaleTopology (Spec (.of K))) A ⥤ Action A Gal(Ω/K) where
  obj F :=
    { V := (pointSmallEtale (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj F
      ρ := Aut.toEnd.comp
        ((GeometricPoint.stalkActionApp A
            (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω) F).comp
          (GeometricPoint.autOfAlgEquiv (𝟙 (Spec (.of K))) Ω)) }
  map f :=
    { hom := (pointSmallEtale (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.map f
      comm σ :=
        GeometricPoint.stalkActionApp_naturality A
          (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω) f
          (GeometricPoint.autOfAlgEquiv (𝟙 (Spec (.of K))) Ω σ) }

/-- The underlying object of the stalk with its Galois action is the stalk. -/
theorem galoisStalk_obj_V (F : Sheaf (smallEtaleTopology (Spec (.of K))) A) :
    ((galoisStalk K Ω A).obj F).V =
      (pointSmallEtale (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.obj F :=
  (rfl)

/-- `σ ∈ Gal(Ω/K)` acts on the stalk by `ofOverGaloisStalkAction (𝟙 (Spec (.of K))) Ω σ`. -/
@[simp]
theorem galoisStalk_obj_ρ_asHom (F : Sheaf (smallEtaleTopology (Spec (.of K))) A)
    (σ : Gal(Ω/K)) :
    (((galoisStalk K Ω A).obj F).ρ σ).asHom =
      (GeometricPoint.ofOverGaloisStalkAction (𝟙 (Spec (.of K))) Ω (A := A) σ).asIso.hom.app F := by
  have h :
      (GeometricPoint.autOfAlgEquiv (𝟙 (Spec (.of K))) Ω σ).unop.asIso.hom =
        GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom := by
    simp
  change (GeometricPoint.stalkActionApp A (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω) F
      (GeometricPoint.autOfAlgEquiv (𝟙 (Spec (.of K))) Ω σ)).asIso.hom = _
  rw [← MulOpposite.op_unop (GeometricPoint.autOfAlgEquiv (𝟙 (Spec (.of K))) Ω σ),
    GeometricPoint.stalkActionApp_asIso_hom, GeometricPoint.ofOverGaloisStalkAction_asIso_hom, h]

/-- The equivariant map of stalks induced by a morphism of sheaves is the map of stalks. -/
@[simp]
theorem galoisStalk_map_hom {F G : Sheaf (smallEtaleTopology (Spec (.of K))) A} (f : F ⟶ G) :
    ((galoisStalk K Ω A).map f).hom =
      (pointSmallEtale (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω).hom).sheafFiber.map f :=
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
    (t : (pointSmallEtale (GeometricPoint.ofOver (𝟙 (Spec (.of K))) Ω).hom).fiber.obj X)
    (z : ToType (F.obj.obj (op X))) :
    HSMul.hSMul (β := ToType ((galoisStalk K Ω A).obj F)) σ
        ((pointSmallEtale _).toPresheafFiber X t F.obj z) =
      (pointSmallEtale _).toPresheafFiber X
        (((GeometricPoint.toPointFunctor _).map
          (GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom)).hom.app X t)
        F.obj z := by
  have h := ConcreteCategory.congr_hom
    (GeometricPoint.toPresheafFiber_toPointFunctor_map_sheafFiber_app
      (GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom) F X t) z
  rw [← Action.ρ_apply_eq_smul ((galoisStalk K Ω A).obj F) σ
      ((pointSmallEtale _).toPresheafFiber X t F.obj z),
    galoisStalk_obj_ρ_asHom, GeometricPoint.ofOverGaloisStalkAction_asIso_hom,
    GeometricPoint.toPointFunctor_map_hom_app_apply]
  exact (ConcreteCategory.comp_apply ((pointSmallEtale _).toPresheafFiber X t F.obj)
    (((GeometricPoint.toPointFunctor _).map
      (GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom)).sheafFiber.app F)
    z).symm.trans h

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
    X.hom.exists_finiteDimensional_forall_mem_fixingSubgroup_SpecMap_comp_eq t.left
      ((Over.w t).trans (Category.comp_id _))
  refine Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
    (fun σ hσ ↦ MulAction.mem_stabilizer_iff.mpr ?_)
    (IntermediateField.fixingSubgroup_isOpen L)
  have ht :
      ((GeometricPoint.toPointFunctor _).map
        (GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom)).hom.app X t = t :=
    Over.OverMorphism.ext <| (GeometricPoint.toPointFunctor_map_hom_app_left
      (GeometricPoint.homOfAlgHom (𝟙 (Spec (.of K))) σ.toAlgHom) X t).trans <|
        (congrArg (· ≫ t.left)
          (GeometricPoint.homOfAlgHom_hom (𝟙 (Spec (.of K))) σ.toAlgHom)).trans (hL σ hσ)
  -- `σ` acts on `p` through `ofOverGaloisStalkAction`, which sends the germ at `t` to the germ
  -- at `t`.
  subst hp
  rw [smul_toPresheafFiber_galoisStalk, ht]

end Concrete

end Galois

end TauCeti.AlgebraicGeometry.Scheme
