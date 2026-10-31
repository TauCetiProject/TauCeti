/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.CategoryTheory.Galois.ContAction
public import TauCeti.CategoryTheory.Galois.Transport

/-!
# The étale fundamental group of a field

Let `K` be a field, `Ω` a separable closure of `K`, and `x : Spec Ω ⟶ Spec K` the geometric point
given by the inclusion `K → Ω`. The étale fundamental group `π₁(Spec K, x)` is the automorphism
group `Aut (FiniteEtaleScheme.fiber x)` of the geometric fibre functor at `x`, a profinite group.
This file identifies it with the absolute Galois group `Gal(Ω/K)`, as topological groups
(`TauCeti.FiniteEtaleScheme.galContinuousMulEquivAutFiber`).

The identification is compatible with Grothendieck's Galois theory for `K`. The geometric fibre
functor at `x` is isomorphic to the functor sending a finite étale `K`-scheme with coordinate
algebra `A` to the finite set `A →ₐ[K] Ω` of its `Ω`-valued points
(`TauCeti.FiniteEtaleScheme.fiberIsoFiniteEtaleFiber`): a lift of `x` to a finite étale `K`-scheme
is the spectrum of a `K`-algebra map from its coordinate algebra to `Ω`. With its action of
`Gal(Ω/K)` by postcomposition, this set of points is `TauCeti.FiniteEtaleScheme.galoisEquivalence`
(`galoisEquivalence_functor`, `TauCeti.galoisFiber_comp_forget₂`). Transporting the Galois action
along the isomorphism makes `Gal(Ω/K)` act on every geometric fibre, and `Gal(Ω/K)` is then a
fundamental group of the fibre functor in the sense of
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`. The latter holds because `Gal(Ω/K)` is
profinite, hence a fundamental group of the forgetful functor on its finite continuous actions
(`ContAction.instIsFundamentalGroup`), and fundamental groups transfer along equivalences of
Galois categories and isomorphisms of fibre functors.

## Main definitions

* `TauCeti.FiniteEtaleScheme.fiberIsoFiniteEtaleFiber`: the geometric fibre functor at `x` is the
  functor of `Ω`-valued points of coordinate algebras.
* `TauCeti.FiniteEtaleScheme.galContinuousMulEquivAutFiber`: `Gal(Ω/K) ≃ₜ* π₁(Spec K, x)`.

## Main results

* `TauCeti.FiniteEtaleScheme.algSpec_map_fiberIsoFiniteEtaleFiber_hom_app`: the `K`-algebra map
  attached to a point of the geometric fibre has the corresponding lift of `x` as spectrum.
* `TauCeti.FiniteEtaleScheme.instIsFundamentalGroupFiber`: `Gal(Ω/K)` is a fundamental group of
  the geometric fibre functor at `x`.
* `TauCeti.FiniteEtaleScheme.galContinuousMulEquivAutFiber_hom_app_apply`: the automorphism of
  the fibre functor attached to `σ` acts on each fibre by `σ`.

## References

* A. Grothendieck, *SGA 1*, Exposé V, Proposition 8.1.
* H. W. Lenstra, *Galois theory for schemes*, Section 5.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace TauCeti.FiniteEtaleScheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- `K`-morphisms `Spec Ω ⟶ Spec A` are `K`-algebra maps `A →ₐ[K] Ω`. -/
private noncomputable def algSpecHomEquiv (A : CommAlgCat.{u} K) :
    ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K Ω)) ⟶
      (algSpec (CommRingCat.of K)).obj (op A)) ≃ (A →ₐ[K] Ω) :=
  ((algSpec.fullyFaithful (R := CommRingCat.of K)).homEquiv
      (X := op (CommAlgCat.of K Ω)) (Y := op A)).symm.trans <|
    Quiver.Hom.opEquiv.symm.trans
      { toFun := CommAlgCat.Hom.hom, invFun := CommAlgCat.ofHom
        left_inv _ := rfl, right_inv _ := rfl }

private theorem algSpecHomEquiv_apply (A : CommAlgCat.{u} K)
    (g : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K Ω)) ⟶
      (algSpec (CommRingCat.of K)).obj (op A)) :
    algSpecHomEquiv K Ω A g =
      ((algSpec.fullyFaithful (R := CommRingCat.of K)).preimage
        (X := op (CommAlgCat.of K Ω)) (Y := op A) g).unop.hom :=
  rfl

private theorem algSpecHomEquiv_comp {A B : CommAlgCat.{u} K} (h : B ⟶ A)
    (g : (algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K Ω)) ⟶
      (algSpec (CommRingCat.of K)).obj (op A)) :
    algSpecHomEquiv K Ω B (g ≫ (algSpec (CommRingCat.of K)).map h.op) =
      (algSpecHomEquiv K Ω A g).comp h.hom := by
  rw [algSpecHomEquiv_apply, algSpecHomEquiv_apply, Functor.FullyFaithful.preimage_comp,
    Functor.FullyFaithful.preimage_map]
  rfl

/-- The lifts of `Spec Ω ⟶ Spec K` to the spectrum of a finite étale `K`-algebra `A` are the
`K`-algebra maps `A →ₐ[K] Ω`, naturally in `A`. -/
private noncomputable def algSpecCompCoyonedaIso :
    (CommAlgCat.finiteEtale (CommRingCat.of K)).ι.op ⋙ algSpec (CommRingCat.of K) ⋙
        coyoneda.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))) ≅
      CommAlgCat.FiniteEtale.fiber K Ω ⋙ FintypeCat.incl :=
  NatIso.ofComponents (fun A ↦ (algSpecHomEquiv K Ω A.unop.obj).toIso) fun f ↦ by
    ext g
    suffices algSpecHomEquiv K Ω _ (g ≫ (algSpec _).map f.unop.hom.op) =
        (algSpecHomEquiv K Ω _ g).comp f.unop.hom.hom by simpa
    exact algSpecHomEquiv_comp K Ω f.unop.hom g

private theorem algSpec_map_algSpecHomEquiv (A : CommAlgCat.{u} K)
    (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⟶
      (algSpec (CommRingCat.of K)).obj (op A)) :
    (algSpec (CommRingCat.of K)).map (CommAlgCat.ofHom (algSpecHomEquiv K Ω A g)).op = g :=
  (algSpecHomEquiv K Ω A).symm_apply_apply g

private theorem functor_comp_ι :
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).functor ⋙
        (finiteEtaleSchemeProperty (Spec (.of K))).ι =
      (CommAlgCat.finiteEtale (CommRingCat.of K)).ι.op ⋙ algSpec (CommRingCat.of K) := by
  rw [finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor, spec_comp_ι]

private theorem algSpecCompCoyonedaIso_hom_app_apply
    (A : (CommAlgCat.FiniteEtale.{u} (CommRingCat.of K))ᵒᵖ)
    (g : ((CommAlgCat.finiteEtale (CommRingCat.of K)).ι.op ⋙ algSpec (CommRingCat.of K) ⋙
        coyoneda.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))))).obj A) :
    (algSpecCompCoyonedaIso K Ω).hom.app A g = algSpecHomEquiv K Ω A.unop.obj g :=
  rfl

variable [IsSepClosed Ω]

/-- The comparison `fiberIsoFiniteEtaleFiber` on underlying types: a lift of the geometric point
to `X ≅ Spec A` is a `K`-algebra map `A →ₐ[K] Ω`. -/
private noncomputable def fiberCompInclIsoFiniteEtaleFiber :
    fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ⋙ FintypeCat.incl ≅
      ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙
        CommAlgCat.FiniteEtale.fiber K Ω) ⋙ FintypeCat.incl :=
  fiberCompInclIso _ ≪≫ (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).counitIso.symm
      _ ≪≫
    Functor.isoWhiskerLeft (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse
      (Functor.isoWhiskerRight (eqToIso (functor_comp_ι K)) _ ≪≫ Functor.associator _ _ _ ≪≫
        algSpecCompCoyonedaIso K Ω)

/-- **The geometric fibre of a finite étale scheme over a field is its set of `Ω`-points.**
The geometric fibre functor of finite étale `K`-schemes at `Spec Ω ⟶ Spec K` is isomorphic to
taking the coordinate algebra `A` and then the finite set `A →ₐ[K] Ω`. A point of the fibre of
`X`, that is a lift of `Spec Ω ⟶ Spec K` to `X`, goes to the `K`-algebra map whose spectrum is
that lift (`algSpec_map_fiberIsoFiniteEtaleFiber_hom_app`). -/
noncomputable def fiberIsoFiniteEtaleFiber :
    fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) ≅
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙
        CommAlgCat.FiniteEtale.fiber K Ω :=
  Functor.fullyFaithfulCancelRight FintypeCat.incl (fiberCompInclIsoFiniteEtaleFiber K Ω)

/-- The `K`-algebra map that `fiberIsoFiniteEtaleFiber K Ω` attaches to a point `y` of the
geometric fibre of a finite étale `K`-scheme `X` has as spectrum the lift of `Spec Ω ⟶ Spec K`
to `X` given by `y`, transported to the spectrum of the coordinate algebra of `X`. -/
theorem algSpec_map_fiberIsoFiniteEtaleFiber_hom_app (X : FiniteEtaleScheme (Spec (.of K)))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :
    (algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom ((fiberIsoFiniteEtaleFiber K Ω).hom.app X y)).op =
      (fiberCompInclIso _).hom.app X y ≫
        ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).counitIso.inv.app X).hom ≫
          eqToHom (by
            rw [finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor, Functor.comp_obj,
              spec_obj_obj]
            rfl) := by
  have h : (fiberIsoFiniteEtaleFiber K Ω).hom.app X y =
      (fiberCompInclIsoFiniteEtaleFiber K Ω).hom.app X y := by
    have := FintypeCat.incl.map_preimage ((fiberCompInclIsoFiniteEtaleFiber K Ω).hom.app X)
    rw [ObjectProperty.ι_map] at this
    rw [fiberIsoFiniteEtaleFiber, Functor.fullyFaithfulCancelRight_hom_app, ← FintypeCat.hom_apply,
      this]
  rw [h]
  simp only [fiberCompInclIsoFiniteEtaleFiber, Functor.isoWhiskerLeft_trans, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, eqToIso.hom,
    NatTrans.comp_app, Functor.comp_obj, ObjectProperty.ι_obj, Functor.flip_obj_obj,
    yoneda_obj_obj, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, ObjectProperty.ι_map, Functor.flip_obj_map, yoneda_map_app, Functor.op_obj,
    Functor.whiskerLeft_app, eqToHom_app, Functor.associator_hom_app, Category.id_comp, comp_apply,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Category.assoc]
  rw [algSpecCompCoyonedaIso_hom_app_apply, algSpec_map_algSpecHomEquiv]

/-- `Gal(Ω/K)` acts on the geometric fibre at `Spec Ω ⟶ Spec K` of a finite étale `K`-scheme
through its action on the `Ω`-points of the coordinate algebra
(`fiberIsoFiniteEtaleFiber_hom_app_smul`). -/
noncomputable instance (X : FiniteEtaleScheme (Spec (.of K))) :
    MulAction Gal(Ω/K) ((fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :=
  letI e : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X ≃
      (((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse.obj X).unop →ₐ[K] Ω) :=
    FintypeCat.equivEquivIso.symm ((fiberIsoFiniteEtaleFiber K Ω).app X)
  e.mulAction Gal(Ω/K)

/-- The identification of the geometric fibre with the `Ω`-points of the coordinate algebra is
`Gal(Ω/K)`-equivariant. -/
theorem fiberIsoFiniteEtaleFiber_hom_app_smul (X : FiniteEtaleScheme (Spec (.of K)))
    (σ : Gal(Ω/K)) (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :
    (fiberIsoFiniteEtaleFiber K Ω).hom.app X (σ • y) =
      (σ : Ω →ₐ[K] Ω).comp ((fiberIsoFiniteEtaleFiber K Ω).hom.app X y) :=
  (FintypeCat.equivEquivIso.symm ((fiberIsoFiniteEtaleFiber K Ω).app X)).apply_symm_apply _

variable [IsGalois K Ω]

attribute [local instance] Functor.mulActionComp in
/-- **The absolute Galois group is a fundamental group of the geometric fibre functor.** For a
separable closure `Ω` of `K`, `Gal(Ω/K)` acting on geometric fibres at `Spec Ω ⟶ Spec K` is a
fundamental group of the Galois category of finite étale `K`-schemes. -/
instance instIsFundamentalGroupFiber :
    IsFundamentalGroup (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) Gal(Ω/K) :=
  have : T2Space Gal(Ω/K) := krullTopology_t2
  have : IsFundamentalGroup
      (((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙ galoisFiber K Ω) ⋙
        forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u}) Gal(Ω/K) :=
    Functor.isFundamentalGroup_comp _ _ _
  Iso.isFundamentalGroup
    (F' := ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙ galoisFiber K Ω) ⋙
      forget₂ (ContAction FintypeCat.{u} Gal(Ω/K)) FintypeCat.{u})
    (fiberIsoFiniteEtaleFiber K Ω) fun X σ y ↦
    fiberIsoFiniteEtaleFiber_hom_app_smul K Ω X σ y

/-- **The étale fundamental group of a field is its absolute Galois group.** For a separable
closure `Ω` of `K`, the automorphism group of the geometric fibre functor of finite étale
`K`-schemes at `Spec Ω ⟶ Spec K` is `Gal(Ω/K)`, as topological groups. -/
noncomputable def galContinuousMulEquivAutFiber :
    Gal(Ω/K) ≃ₜ* Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))) where
  toMulEquiv := toAutMulEquiv _ _
  continuous_toFun := (toAutMulEquiv_isHomeomorph _ _).continuous
  continuous_invFun := (toAutMulEquiv_isHomeomorph _ _).homeomorph.symm.continuous

/-- The automorphism of the geometric fibre functor attached to `σ ∈ Gal(Ω/K)` acts on every
fibre by `σ`. -/
@[simp]
theorem galContinuousMulEquivAutFiber_hom_app_apply (σ : Gal(Ω/K))
    (X : FiniteEtaleScheme (Spec (.of K)))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :
    (galContinuousMulEquivAutFiber K Ω σ).asIso.hom.app X y = σ • y :=
  toAut_hom_app_apply _ σ y

/-- Over a separably closed field `K`, the étale fundamental group at the geometric point
`Spec K ⟶ Spec K` is trivial. -/
instance [IsSepClosed K] :
    Subsingleton (Aut (fiber (Spec.map (CommRingCat.ofHom (algebraMap K K))))) :=
  (galContinuousMulEquivAutFiber K K).toEquiv.symm.subsingleton

end TauCeti.FiniteEtaleScheme
