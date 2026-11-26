/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.ExtendScalars
public import TauCeti.CategoryTheory.Monoidal.Whiskering

/-!
# The tensor-automorphism group functor of a fibre functor

Let `ω : C ⥤ ModuleCat K` be a lax monoidal functor from a monoidal category to modules over a
commutative ring `K`. The main example is a fibre functor `w : C ⥤ FGModuleCat K` of a neutral
Tannakian category followed by the inclusion `forget₂ (FGModuleCat K) (ModuleCat K)`; nothing
below uses finiteness. For a commutative `K`-algebra `R`, the scalar extension
`CategoryTheory.Functor.scalarExtension ω R` is `ω` followed by Mathlib's monoidal extension of
scalars `R ⊗[K] -` (`ModuleCat.extendScalars`); see
`TauCeti.Algebra.Category.ModuleCat.ExtendScalars.Comp`. This file assembles the monoidal natural
automorphisms of these scalar extensions into a group-valued functor

```text
CommAlgCat K ⥤ GrpCat,    R ↦ Aut^⊗(ω_R),
```

`CategoryTheory.Functor.tensorAutFunctor ω`, whose value at `R` is the group of `R`-points of the
group of tensor automorphisms of `ω`. A morphism of algebras `f : R →ₐ[K] S` acts by base change
of components (`CategoryTheory.Functor.tensorAutMapValue`): it whiskers with extension of scalars
along `f` and identifies `ω_R ⋙ S ⊗[R] -` with `ω_S` through the composition isomorphism of
extension of scalars (`CategoryTheory.Functor.scalarExtensionCompIso`). The functor laws are the
unit and associativity coherences of these isomorphisms.

The group functor depends on the fibre functor only up to monoidal equivalence: for an
equivalence `e : C ≌ D` whose functor is strong monoidal, a lax monoidal
`ω' : D ⥤ ModuleCat K` and a monoidal natural isomorphism `ι : e.functor ⋙ ω' ≅ ω`, the two
tensor-automorphism functors are isomorphic
(`CategoryTheory.Functor.tensorAutFunctorIsoOfIso`).

## Main declarations

* `CategoryTheory.Functor.tensorAutMapValue`: base change of monoidal natural automorphisms of
  scalar extension, with its identity and composition laws.
* `CategoryTheory.Functor.tensorAutFunctor`: the tensor-automorphism group functor.
* `CategoryTheory.Functor.tensorAutEquivOfIso` and
  `CategoryTheory.Functor.tensorAutFunctorIsoOfIso`: transport along a monoidal equivalence and a
  monoidal isomorphism of fibre functors.

## References

* P. Deligne, J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), §2, Theorem 2.11.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

universe v₁ v₂ u u₁

namespace CategoryTheory.Functor

open MonoidalCategory

variable {K : Type u} [CommRing K]

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable (ω : C ⥤ ModuleCat.{u} K) [ω.LaxMonoidal]

variable {R S T : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
  [Algebra K T]

/-- Base change of the monoidal natural automorphisms of scalar extension along a morphism of
`K`-algebras: extend the scalars of each component. -/
noncomputable def tensorAutMapValue (f : R →ₐ[K] S) :
    Aut (LaxMonoidalFunctor.of (ω.scalarExtension R)) →*
      Aut (LaxMonoidalFunctor.of (ω.scalarExtension S)) :=
  -- Instance search does not see through the objects of `LaxMonoidalFunctor.of`, so the
  -- monoidality witness is passed explicitly.
  (Aut.autMulEquivOfIso (@LaxMonoidalFunctor.isoMk _ _ _ _ _ _
    (.of (ω.scalarExtension R ⋙ ModuleCat.extendScalars (f : R →+* S))) (.of (ω.scalarExtension S))
    (ω.scalarExtensionCompIso f)
    (inferInstanceAs (NatTrans.IsMonoidal (ω.scalarExtensionCompIso f).hom)))).toMonoidHom.comp
      (LaxMonoidalFunctor.whiskerRightAut _ _)

/-- The components of the base change of a monoidal natural automorphism are the extended
components, conjugated by the composition isomorphism of extension of scalars. -/
@[simp]
theorem tensorAutMapValue_apply_asIso_hom_hom_app (f : R →ₐ[K] S)
    (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) (X : C) :
    (ω.tensorAutMapValue f η).asIso.hom.hom.app X =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
          f.comp_algebraMap.symm).hom.app (ω.obj X) ≫
        (ModuleCat.extendScalars (f : R →+* S)).map (η.asIso.hom.hom.app X) ≫
          (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).inv.app (ω.obj X) := by
  simp only [tensorAutMapValue, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom,
    LaxMonoidalFunctor.comp_hom, NatTrans.comp_app]
  rw [LaxMonoidalFunctor.whiskerRightAut_apply_asIso_hom_hom_app]
  -- Normalize the bundling constructors across `LaxMonoidalFunctor.of`.
  dsimp only [LaxMonoidalFunctor.isoMk, LaxMonoidalFunctor.homMk, LaxMonoidalFunctor.of]
  simp only [scalarExtensionCompIso_inv_app, scalarExtensionCompIso_hom_app]

/-- Base change along the identity is the identity. -/
@[simp]
theorem tensorAutMapValue_id (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) :
    ω.tensorAutMapValue (AlgHom.id K R) η = η := by
  ext X : 5
  rw [tensorAutMapValue_apply_asIso_hom_hom_app]
  exact ModuleCat.extendScalarsComp'_conj_id _ _

/-- Base change along a composite is the composite of base changes. -/
@[simp]
theorem tensorAutMapValue_comp (f : R →ₐ[K] S) (g : S →ₐ[K] T)
    (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) :
    ω.tensorAutMapValue (g.comp f) η = ω.tensorAutMapValue g (ω.tensorAutMapValue f η) := by
  ext X : 5
  simp only [tensorAutMapValue_apply_asIso_hom_hom_app]
  exact ModuleCat.extendScalarsComp'_conj_comp f g _ _

/-- The tensor-automorphism group functor of `ω`: a commutative `K`-algebra `R` is sent to the
group of monoidal natural automorphisms of the scalar extension `ω.scalarExtension R`, and a
morphism of algebras acts by base change of components (`tensorAutMapValue`). -/
-- `@[expose]` matches `TauCeti.GeneralLinear.scalarExtensionAutomorphismsFunctor`: natural
-- transformations out of this functor need its object part to unfold across modules.
@[expose] noncomputable def tensorAutFunctor : CommAlgCat.{u} K ⥤ GrpCat.{max u u₁} where
  obj R := GrpCat.of (Aut (LaxMonoidalFunctor.of (ω.scalarExtension R)))
  map φ := GrpCat.ofHom (ω.tensorAutMapValue φ.hom)
  map_id _ := GrpCat.ext fun η ↦ ω.tensorAutMapValue_id η
  map_comp φ ψ := GrpCat.ext fun η ↦ ω.tensorAutMapValue_comp φ.hom ψ.hom η

/-- The tensor-automorphism functor sends an algebra to the monoidal automorphism group of the
scalar extension. -/
@[simp]
theorem tensorAutFunctor_obj (R : CommAlgCat.{u} K) :
    ω.tensorAutFunctor.obj R = GrpCat.of (Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) :=
  (rfl)

/-- The tensor-automorphism functor acts on morphisms by base change. -/
@[simp]
theorem tensorAutFunctor_map {R S : CommAlgCat.{u} K} (φ : R ⟶ S) :
    ω.tensorAutFunctor.map φ = GrpCat.ofHom (ω.tensorAutMapValue φ.hom) :=
  (rfl)

section Transport

variable {D : Type u₁} [Category.{v₂} D] [MonoidalCategory D]
variable (e : C ≌ D) [e.functor.Monoidal]
variable {ω} {ω' : D ⥤ ModuleCat.{u} K} [ω'.LaxMonoidal] (ι : e.functor ⋙ ω' ≅ ω)
  [NatTrans.IsMonoidal ι.hom]

/-- Transport of monoidal automorphisms of scalar extension along a monoidal equivalence `e`
and a monoidal isomorphism `ι : e.functor ⋙ ω' ≅ ω` of fibre functors. -/
noncomputable def tensorAutEquivOfIso (R : Type u) [CommRing R] [Algebra K R] :
    Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R)) ≃*
      Aut (LaxMonoidalFunctor.of (ω.scalarExtension R)) :=
  (LaxMonoidalFunctor.whiskerLeftAutEquiv e _).trans
    (Aut.autMulEquivOfIso (@LaxMonoidalFunctor.isoMk _ _ _ _ _ _
      (.of (e.functor ⋙ ω'.scalarExtension R)) (.of (ω.scalarExtension R))
      (scalarExtensionIsoOfIso e.functor ι R)
      (inferInstanceAs (NatTrans.IsMonoidal (scalarExtensionIsoOfIso e.functor ι R).hom))))

/-- The components of a transported monoidal automorphism are the components at the image under
`e.functor`, conjugated by the scalar extension of `ι`. -/
@[simp]
theorem tensorAutEquivOfIso_apply_asIso_hom_hom_app (R : Type u) [CommRing R] [Algebra K R]
    (η : Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R))) (X : C) :
    (tensorAutEquivOfIso e ι R η).asIso.hom.hom.app X =
      (ModuleCat.extendScalars (algebraMap K R)).map (ι.inv.app X) ≫
        η.asIso.hom.hom.app (e.functor.obj X) ≫
          (ModuleCat.extendScalars (algebraMap K R)).map (ι.hom.app X) := by
  simp only [tensorAutEquivOfIso, MulEquiv.trans_apply, Aut.autMulEquivOfIso_apply_asIso,
    Iso.trans_hom, Iso.symm_hom, LaxMonoidalFunctor.comp_hom, NatTrans.comp_app,
    LaxMonoidalFunctor.whiskerLeftAutEquiv_apply]
  rw [LaxMonoidalFunctor.whiskerLeftAut_apply_asIso_hom_hom_app]
  -- Normalize the bundling constructors before applying the scalar-extension component API.
  dsimp only [LaxMonoidalFunctor.isoMk, LaxMonoidalFunctor.homMk, LaxMonoidalFunctor.of]
  simp only [scalarExtensionIsoOfIso_inv_app, scalarExtensionIsoOfIso_hom_app]

/-- Transport along a monoidal equivalence commutes with base change of the value algebra. -/
theorem tensorAutEquivOfIso_tensorAutMapValue (f : R →ₐ[K] S)
    (η : Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R))) :
    tensorAutEquivOfIso e ι S (ω'.tensorAutMapValue f η) =
      ω.tensorAutMapValue f (tensorAutEquivOfIso e ι R η) := by
  ext X : 5
  simp only [tensorAutEquivOfIso_apply_asIso_hom_hom_app,
    tensorAutMapValue_apply_asIso_hom_hom_app]
  exact ModuleCat.extendScalarsComp'_conj_naturality f _ _ _

/-- The tensor-automorphism functors of fibre functors that correspond under a monoidal
equivalence are isomorphic. -/
noncomputable def tensorAutFunctorIsoOfIso : ω'.tensorAutFunctor ≅ ω.tensorAutFunctor :=
  NatIso.ofComponents (fun R ↦ (tensorAutEquivOfIso e ι R).toGrpIso) fun φ ↦ by
    rw [tensorAutFunctor_map, tensorAutFunctor_map]
    refine GrpCat.hom_ext (MonoidHom.ext fun η ↦ ?_)
    exact tensorAutEquivOfIso_tensorAutMapValue e ι φ.hom η

/-- The components of `tensorAutFunctorIsoOfIso` are the transports `tensorAutEquivOfIso`. -/
@[simp]
theorem tensorAutFunctorIsoOfIso_hom_app (R : CommAlgCat.{u} K) :
    (tensorAutFunctorIsoOfIso e ι).hom.app R = (tensorAutEquivOfIso e ι R).toGrpIso.hom :=
  (rfl)

end Transport

end CategoryTheory.Functor
