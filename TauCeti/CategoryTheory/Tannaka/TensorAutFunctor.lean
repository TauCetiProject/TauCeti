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
scalars `R ⊗[K] -` (`ModuleCat.extendScalars`). This file assembles the monoidal natural
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

* `CategoryTheory.Functor.scalarExtension`: the scalar extension of `ω` to a commutative
  `K`-algebra.
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

/-! ### Conjugation by the composition isomorphisms of extension of scalars -/

section Conjugation

variable {R S T : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
  [Algebra K T]

/-- Conjugating the extension of scalars of an endomorphism along `R → S` by the composition
isomorphism is functorial in the morphism of algebras: the identity coherence. -/
private theorem extendScalarsComp'_conj_id (M : ModuleCat.{u} K)
    (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R) (algebraMap K R)
        (AlgHom.id K R).comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (AlgHom.id K R : R →+* R)).map φ ≫
        (ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R)
          (algebraMap K R) (AlgHom.id K R).comp_algebraMap.symm).inv.app M = φ := by
  set σ := ModuleCat.extendScalarsComp' (algebraMap K R) (AlgHom.id K R : R →+* R)
    (algebraMap K R) (AlgHom.id K R).comp_algebraMap.symm
  set ι := ModuleCat.extendScalarsId' (AlgHom.id_toRingHom (R := K) (A := R))
  -- The identity coherence of extension of scalars identifies `σ.inv` with `ι.hom`.
  have h : σ.inv.app M = ι.hom.app _ := by
    have := NatTrans.congr_app (ModuleCat.extendScalarsComp'_hom_comp_id (algebraMap K R)
      (AlgHom.id_toRingHom (R := K) (A := R)) (AlgHom.id K R).comp_algebraMap.symm) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      NatTrans.id_app] at this
    rw [← Iso.app_hom, Iso.hom_comp_eq_id] at this
    erw [Category.comp_id] at this
    exact this.symm
  rw [h, ι.hom.naturality, Functor.id_map, ← h, Iso.hom_inv_id_app_assoc]

/-- Conjugating the extension of scalars of an endomorphism by the composition isomorphisms is
functorial in the morphism of algebras: the composition coherence. -/
private theorem extendScalarsComp'_conj_comp (f : R →ₐ[K] S) (g : S →ₐ[K] T)
    (M : ModuleCat.{u} K)
    (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
        (g.comp f).comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (g.comp f : R →+* T)).map φ ≫
        (ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
          (g.comp f).comp_algebraMap.symm).inv.app M =
    (ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
        g.comp_algebraMap.symm).hom.app M ≫
      (ModuleCat.extendScalars (g : S →+* T)).map
        ((ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).hom.app M ≫
          (ModuleCat.extendScalars (f : R →+* S)).map φ ≫
            (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
              f.comp_algebraMap.symm).inv.app M) ≫
        (ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
          g.comp_algebraMap.symm).inv.app M := by
  set σf := ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
    f.comp_algebraMap.symm
  set σg := ModuleCat.extendScalarsComp' (algebraMap K S) (g : S →+* T) (algebraMap K T)
    g.comp_algebraMap.symm
  set σgf := ModuleCat.extendScalarsComp' (algebraMap K R) (g.comp f : R →+* T) (algebraMap K T)
    (g.comp f).comp_algebraMap.symm
  set τ := ModuleCat.extendScalarsComp' (f : R →+* S) (g : S →+* T) (g.comp f : R →+* T)
    (AlgHom.comp_toRingHom g f)
  -- The associativity coherence of extension of scalars along `K → R → S → T`.
  have hA : σg.hom.app M ≫ (ModuleCat.extendScalars (g : S →+* T)).map (σf.hom.app M) =
      σgf.hom.app M ≫ τ.hom.app _ := by
    simpa using NatTrans.congr_app (ModuleCat.extendScalarsComp'_assoc (algebraMap K R)
      (f : R →+* S) (algebraMap K S) f.comp_algebraMap.symm (g : S →+* T)
      (g.comp f : R →+* T) (algebraMap K T) g.comp_algebraMap.symm (AlgHom.comp_toRingHom g f)
      (g.comp f).comp_algebraMap.symm) M
  rw [← cancel_mono (σg.hom.app M ≫ (ModuleCat.extendScalars (g : S →+* T)).map (σf.hom.app M))]
  conv_rhs => rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Category.assoc, Category.assoc, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]
  rw [hA, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, τ.hom.naturality,
    ← reassoc_of% hA, Functor.comp_map, Functor.map_comp]

/-- Conjugation by the composition isomorphism of extension of scalars is natural in the
module. -/
private theorem extendScalarsComp'_conj_naturality (f : R →ₐ[K] S) {M N : ModuleCat.{u} K}
    (u : M ⟶ N) (v : N ⟶ M) (φ : (ModuleCat.extendScalars (algebraMap K R)).obj M ⟶
      (ModuleCat.extendScalars (algebraMap K R)).obj M) :
    (ModuleCat.extendScalars (algebraMap K S)).map v ≫
        ((ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).hom.app M ≫
          (ModuleCat.extendScalars (f : R →+* S)).map φ ≫
            (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
              f.comp_algebraMap.symm).inv.app M) ≫
        (ModuleCat.extendScalars (algebraMap K S)).map u =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
          f.comp_algebraMap.symm).hom.app N ≫
        (ModuleCat.extendScalars (f : R →+* S)).map
          ((ModuleCat.extendScalars (algebraMap K R)).map v ≫ φ ≫
            (ModuleCat.extendScalars (algebraMap K R)).map u) ≫
          (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
            f.comp_algebraMap.symm).inv.app N := by
  have h := (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
    f.comp_algebraMap.symm).inv.naturality u
  simp only [Functor.comp_map] at h
  simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc, h, Functor.comp_map]

end Conjugation

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable (ω : C ⥤ ModuleCat.{u} K) [ω.LaxMonoidal]

/-- The scalar extension of a functor to `K`-modules along a commutative `K`-algebra `R`: the
composite of `ω` with extension of scalars `R ⊗[K] -`. It is lax monoidal, and strong monoidal
when `ω` is. -/
noncomputable abbrev scalarExtension (R : Type u) [CommRing R] [Algebra K R] :
    C ⥤ ModuleCat.{u} R :=
  ω ⋙ ModuleCat.extendScalars (algebraMap K R)

variable {R S T : Type u} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
  [Algebra K T]

/-- Extending the scalars of `ω.scalarExtension R` along a morphism `f : R →ₐ[K] S` of
`K`-algebras is `ω.scalarExtension S`. -/
noncomputable def scalarExtensionCompIso (f : R →ₐ[K] S) :
    ω.scalarExtension R ⋙ ModuleCat.extendScalars (f : R →+* S) ≅ ω.scalarExtension S :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft ω
    (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
      f.comp_algebraMap.symm).symm

/-- `scalarExtensionCompIso` is a monoidal natural isomorphism. -/
instance (f : R →ₐ[K] S) : NatTrans.IsMonoidal (ω.scalarExtensionCompIso f).hom :=
  inferInstanceAs (NatTrans.IsMonoidal ((Functor.associator _ _ _).hom ≫ whiskerLeft ω
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).inv))

/-- Base change of the monoidal natural automorphisms of scalar extension along a morphism of
`K`-algebras: extend the scalars of each component. -/
noncomputable def tensorAutMapValue (f : R →ₐ[K] S) :
    Aut (LaxMonoidalFunctor.of (ω.scalarExtension R)) →*
      Aut (LaxMonoidalFunctor.of (ω.scalarExtension S)) :=
  (Aut.autMulEquivOfIso (LaxMonoidalFunctor.ofIso (ω.scalarExtensionCompIso f))).toMonoidHom.comp
    (LaxMonoidalFunctor.whiskerRightAut _ _)

/-- The components of the base change of a monoidal natural automorphism are the extended
components, conjugated by `scalarExtensionCompIso`. -/
theorem forgetAut_tensorAutMapValue_app (f : R →ₐ[K] S)
    (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) (X : C) :
    (LaxMonoidalFunctor.forgetAut _ (ω.tensorAutMapValue f η)).asIso.hom.app X =
      (ω.scalarExtensionCompIso f).inv.app X ≫
        (ModuleCat.extendScalars (f : R →+* S)).map
          ((LaxMonoidalFunctor.forgetAut _ η).asIso.hom.app X) ≫
          (ω.scalarExtensionCompIso f).hom.app X := by
  rw [LaxMonoidalFunctor.forgetAut_apply_asIso_hom, LaxMonoidalFunctor.forgetAut_apply_asIso_hom]
  simp only [tensorAutMapValue, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom,
    LaxMonoidalFunctor.comp_hom, NatTrans.comp_app]
  rw [LaxMonoidalFunctor.ofIso_hom_hom_app, LaxMonoidalFunctor.ofIso_inv_hom_app,
    LaxMonoidalFunctor.whiskerRightAut_apply_asIso_hom_hom_app]
  -- The components are typed through `LaxMonoidalFunctor.of`; both sides now agree up to
  -- unfolding it.
  rfl

omit [MonoidalCategory C] [ω.LaxMonoidal] in
/-- The components of the inverse of `scalarExtensionCompIso` are those of the composition
isomorphism of extension of scalars. -/
theorem scalarExtensionCompIso_inv_app (f : R →ₐ[K] S) (X : C) :
    (ω.scalarExtensionCompIso f).inv.app X =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).hom.app (ω.obj X) := by
  simp [scalarExtensionCompIso]

omit [MonoidalCategory C] [ω.LaxMonoidal] in
/-- The components of `scalarExtensionCompIso` are those of the inverse of the composition
isomorphism of extension of scalars. -/
theorem scalarExtensionCompIso_hom_app (f : R →ₐ[K] S) (X : C) :
    (ω.scalarExtensionCompIso f).hom.app X =
      (ModuleCat.extendScalarsComp' (algebraMap K R) (f : R →+* S) (algebraMap K S)
        f.comp_algebraMap.symm).inv.app (ω.obj X) := by
  simp [scalarExtensionCompIso]

/-- Base change along the identity is the identity. -/
@[simp]
theorem tensorAutMapValue_id (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) :
    ω.tensorAutMapValue (AlgHom.id K R) η = η := by
  refine LaxMonoidalFunctor.forgetAut_injective _
    (Aut.ext (Iso.ext (NatTrans.ext (funext fun X ↦ ?_))))
  rw [forgetAut_tensorAutMapValue_app, scalarExtensionCompIso_inv_app,
    scalarExtensionCompIso_hom_app]
  exact extendScalarsComp'_conj_id _ _

/-- Base change along a composite is the composite of base changes. -/
@[simp]
theorem tensorAutMapValue_comp (f : R →ₐ[K] S) (g : S →ₐ[K] T)
    (η : Aut (LaxMonoidalFunctor.of (ω.scalarExtension R))) :
    ω.tensorAutMapValue (g.comp f) η = ω.tensorAutMapValue g (ω.tensorAutMapValue f η) := by
  refine LaxMonoidalFunctor.forgetAut_injective _
    (Aut.ext (Iso.ext (NatTrans.ext (funext fun X ↦ ?_))))
  rw [forgetAut_tensorAutMapValue_app, forgetAut_tensorAutMapValue_app,
    forgetAut_tensorAutMapValue_app, scalarExtensionCompIso_inv_app,
    scalarExtensionCompIso_hom_app, scalarExtensionCompIso_inv_app,
    scalarExtensionCompIso_hom_app, scalarExtensionCompIso_inv_app,
    scalarExtensionCompIso_hom_app]
  exact extendScalarsComp'_conj_comp f g _ _

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

/-- The scalar extension of `ω'` precomposed with `e.functor` is that of `ω`, through `ι`. -/
noncomputable def scalarExtensionIsoOfIso (R : Type u) [CommRing R] [Algebra K R] :
    e.functor ⋙ ω'.scalarExtension R ≅ ω.scalarExtension R :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight ι _

/-- `scalarExtensionIsoOfIso` is a monoidal natural isomorphism. -/
instance (R : Type u) [CommRing R] [Algebra K R] :
    NatTrans.IsMonoidal (scalarExtensionIsoOfIso e ι R).hom :=
  inferInstanceAs (NatTrans.IsMonoidal ((Functor.associator _ _ _).inv ≫ whiskerRight ι.hom _))

omit [MonoidalCategory C] [ω.LaxMonoidal] [MonoidalCategory D] [ω'.LaxMonoidal] [e.functor.Monoidal]
  [NatTrans.IsMonoidal ι.hom] in
/-- The components of `scalarExtensionIsoOfIso` are the scalar extensions of those of `ι`. -/
theorem scalarExtensionIsoOfIso_hom_app (R : Type u) [CommRing R] [Algebra K R] (X : C) :
    (scalarExtensionIsoOfIso e ι R).hom.app X = (ModuleCat.extendScalars (algebraMap K R)).map
      (ι.hom.app X) := by
  simp [scalarExtensionIsoOfIso]

omit [MonoidalCategory C] [ω.LaxMonoidal] [MonoidalCategory D] [ω'.LaxMonoidal] [e.functor.Monoidal]
  [NatTrans.IsMonoidal ι.hom] in
/-- The components of the inverse of `scalarExtensionIsoOfIso` are the scalar extensions of those
of `ι.inv`. -/
theorem scalarExtensionIsoOfIso_inv_app (R : Type u) [CommRing R] [Algebra K R] (X : C) :
    (scalarExtensionIsoOfIso e ι R).inv.app X = (ModuleCat.extendScalars (algebraMap K R)).map
      (ι.inv.app X) := by
  simp [scalarExtensionIsoOfIso]

/-- Transport of monoidal automorphisms of scalar extension along a monoidal equivalence `e`
and a monoidal isomorphism `ι : e.functor ⋙ ω' ≅ ω` of fibre functors. -/
noncomputable def tensorAutEquivOfIso (R : Type u) [CommRing R] [Algebra K R] :
    Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R)) ≃*
      Aut (LaxMonoidalFunctor.of (ω.scalarExtension R)) :=
  (LaxMonoidalFunctor.whiskerLeftAutEquiv e _).trans
    (Aut.autMulEquivOfIso (LaxMonoidalFunctor.ofIso (scalarExtensionIsoOfIso e ι R)))

/-- The components of a transported monoidal automorphism are the components at the image under
`e.functor`, conjugated by the scalar extension of `ι`. -/
theorem forgetAut_tensorAutEquivOfIso_app (R : Type u) [CommRing R] [Algebra K R]
    (η : Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R))) (X : C) :
    (LaxMonoidalFunctor.forgetAut _ (tensorAutEquivOfIso e ι R η)).asIso.hom.app X =
      (ModuleCat.extendScalars (algebraMap K R)).map
          (ι.inv.app X) ≫
        (LaxMonoidalFunctor.forgetAut _ η).asIso.hom.app (e.functor.obj X) ≫
          (ModuleCat.extendScalars (algebraMap K R)).map
            (ι.hom.app X) := by
  rw [LaxMonoidalFunctor.forgetAut_apply_asIso_hom, LaxMonoidalFunctor.forgetAut_apply_asIso_hom]
  simp only [tensorAutEquivOfIso, MulEquiv.trans_apply, Aut.autMulEquivOfIso_apply_asIso,
    Iso.trans_hom, Iso.symm_hom, LaxMonoidalFunctor.comp_hom, NatTrans.comp_app,
    LaxMonoidalFunctor.whiskerLeftAutEquiv_apply]
  rw [LaxMonoidalFunctor.ofIso_hom_hom_app, LaxMonoidalFunctor.ofIso_inv_hom_app,
    LaxMonoidalFunctor.whiskerLeftAut_apply_asIso_hom_hom_app,
    scalarExtensionIsoOfIso_hom_app, scalarExtensionIsoOfIso_inv_app]
  rfl

/-- Transport along a monoidal equivalence commutes with base change of the value algebra. -/
theorem tensorAutEquivOfIso_tensorAutMapValue (f : R →ₐ[K] S)
    (η : Aut (LaxMonoidalFunctor.of (ω'.scalarExtension R))) :
    tensorAutEquivOfIso e ι S (ω'.tensorAutMapValue f η) =
      ω.tensorAutMapValue f (tensorAutEquivOfIso e ι R η) := by
  refine LaxMonoidalFunctor.forgetAut_injective _
    (Aut.ext (Iso.ext (NatTrans.ext (funext fun X ↦ ?_))))
  rw [forgetAut_tensorAutEquivOfIso_app, forgetAut_tensorAutMapValue_app,
    forgetAut_tensorAutMapValue_app, forgetAut_tensorAutEquivOfIso_app,
    scalarExtensionCompIso_inv_app, scalarExtensionCompIso_hom_app,
    scalarExtensionCompIso_inv_app, scalarExtensionCompIso_hom_app]
  exact extendScalarsComp'_conj_naturality f _ _ _

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
