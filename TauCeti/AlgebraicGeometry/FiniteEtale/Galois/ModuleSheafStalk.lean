/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.ModuleSheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.GaloisStalk

/-!
# The stalk of the étale sheaf of a Galois representation

Let `Ω` be a separably closed field, finite and Galois over `K` (as `ℂ` over `ℝ`), and `ρ` a
representation of `Gal(Ω/K)` on a `Λ`-module `M`. The geometric point `Spec Ω ⟶ Spec K` is then
finite étale, so the stalk there of an étale sheaf is its module of sections over `Spec Ω`. For
`galoisModuleSheaf K Ω ρ` these sections are the `Gal(Ω/K)`-maps into `ρ` from the Galois set of
`Spec Ω`, the `K`-embeddings `Ω → Ω`, on which `Gal(Ω/K)` acts simply transitively; evaluation at
the identity identifies them with `M`
(`TauCeti.FiniteEtaleScheme.etaleStalkGaloisModuleSheafEquiv`). Under this identification the
Galois action on the stalk (`TauCeti.AlgebraicGeometry.Scheme.galoisStalkMap`) is `ρ`
(`TauCeti.FiniteEtaleScheme.etaleStalkGaloisModuleSheafEquiv_galoisStalkMap`): `σ` acts on the
stalk through `Spec σ`, which acts on the Galois set by `φ ↦ φ ∘ σ`.

## Main definitions

* `TauCeti.FiniteEtaleScheme.etaleStalkGaloisModuleSheafEquiv`: the stalk of
  `galoisModuleSheaf K Ω ρ` at `Spec Ω ⟶ Spec K` is `M`.

## Main results

* `TauCeti.FiniteEtaleScheme.galoisStalkMap_comp_pointSmallEtaleSheafFiberIso`: on sections over
  `Spec Ω`, the Galois action on the stalk is restriction along `Spec σ`.
* `TauCeti.FiniteEtaleScheme.etaleStalkGaloisModuleSheafEquiv_galoisStalkMap`: the Galois action
  on the stalk is `ρ`.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2.
-/

public section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry FintypeCatDiscrete

namespace TauCeti.FiniteEtaleScheme

open TauCeti.AlgebraicGeometry.Scheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]
  [FiniteDimensional K Ω]

variable {Λ : Type u} [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ Gal(Ω/K) M)

/-- For a finite separable extension `Ω` of `K`, the morphism `Spec Ω ⟶ Spec K` is étale. -/
instance etale_specMap_algebraMap (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsSeparable K Ω] [FiniteDimensional K Ω] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  have : Algebra.Etale K Ω := Algebra.Etale.of_isSeparable K Ω
  (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- `Ω`, finite and separable over `K`, as a finite étale `K`-algebra. -/
noncomputable abbrev finiteEtaleField : CommAlgCat.FiniteEtale.{u} K :=
  haveI : Algebra.Etale K Ω := Algebra.Etale.of_isSeparable K Ω
  CommAlgCat.FiniteEtale.of K Ω

omit [IsSepClosed Ω] [IsGalois K Ω] in
/-- `Gal(Ω/K)` acts simply transitively on the `K`-embeddings `Ω → Ω`, through the identity. -/
theorem bijective_smul_algHomId :
    Function.Bijective fun σ : Gal(Ω/K) ↦ σ • (AlgHom.id K Ω) := by
  refine ⟨fun σ τ h ↦ AlgEquiv.ext fun x ↦ congr($h x), fun φ ↦ ?_⟩
  exact ⟨AlgEquiv.ofBijective φ φ.bijective, AlgHom.ext fun x ↦ rfl⟩

/-- **The stalk of the étale sheaf of a Galois representation.** For `Ω` finite over `K`, the stalk
of `galoisModuleSheaf K Ω ρ` at the geometric point `Spec Ω ⟶ Spec K` is `M`: the point is étale,
so the stalk is the module of sections over `Spec Ω`, which are the `Gal(Ω/K)`-maps from the
`K`-embeddings `Ω → Ω` into `ρ`, and these are determined by their value at the identity. -/
@[expose] noncomputable def etaleStalkGaloisModuleSheafEquiv :
    (etaleStalk Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj
      (galoisModuleSheaf K Ω ρ) ≃ₗ[Λ] M :=
  let s := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let X := (spec (.of K)).obj (op (finiteEtaleField K Ω))
  -- The étale `K`-scheme `Spec Ω` is the finite étale `K`-scheme `X`, definitionally.
  ((Scheme.pointSmallEtaleSheafFiberIso s).app _ ≪≫
    galoisModuleSheafObjIso K Ω ρ X ≪≫
    (ContAction.modulePresheaf ρ).mapIso
      ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).symm.op
    ).toLinearEquiv ≪≫ₗ
    ContAction.modulePresheafObjEquivOfBijective ρ
      (S := (galoisFiber K Ω).obj (op (finiteEtaleField K Ω)))
      (AlgHom.id K Ω) (bijective_smul_algHomId K Ω)

/-- `σ` as an endomorphism of the finite étale `K`-algebra `Ω`. -/
noncomputable abbrev finiteEtaleFieldHom (σ : Gal(Ω/K)) :
    finiteEtaleField K Ω ⟶ finiteEtaleField K Ω :=
  haveI : Algebra.Etale K Ω := Algebra.Etale.of_isSeparable K Ω
  CommAlgCat.FiniteEtale.ofHom (σ : Ω →ₐ[K] Ω)

/-- `etaleStalkGaloisModuleSheafEquiv` sends an element of the stalk, viewed as a section over
`Spec Ω`, to the value at the identity embedding of the corresponding `Gal(Ω/K)`-map. -/
theorem etaleStalkGaloisModuleSheafEquiv_apply
    (x : (etaleStalk Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj
      (galoisModuleSheaf K Ω ρ)) :
    etaleStalkGaloisModuleSheafEquiv K Ω ρ x =
      (ContAction.modulePresheafObjEquiv ρ _
        ((galoisModuleSheafObjIso K Ω ρ ((spec (.of K)).obj (op (finiteEtaleField K Ω)))).hom
          ((Scheme.pointSmallEtaleSheafFiberIso (A := ModuleCat.{u} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app
              (galoisModuleSheaf K Ω ρ) x))).val
        ((ContAction.fiberFunctor Gal(Ω/K)).map
          ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).inv
          (AlgHom.id K Ω)) :=
  (ContAction.modulePresheafObjEquivOfBijective_apply ρ _ _ _).trans
    (ContAction.modulePresheafObjEquiv_map_apply ρ _ _ _)

/-- On sections over `Spec Ω`, the Galois action on the stalk is restriction along `Spec σ`. -/
theorem galoisStalkMap_comp_pointSmallEtaleSheafFiberIso (σ : Gal(Ω/K)) :
    (galoisStalkMap K Ω (ModuleCat.{u} Λ) σ).app (galoisModuleSheaf K Ω ρ) ≫
        (Scheme.pointSmallEtaleSheafFiberIso
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) =
      (Scheme.pointSmallEtaleSheafFiberIso
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) ≫
        (galoisModuleSheaf K Ω ρ).obj.map
          ((toEtale _).map ((spec (.of K)).map (finiteEtaleFieldHom K Ω σ).op)).op := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ fun Y y ↦ ?_
  erw [toPresheafFiber_galoisStalkMap_app_assoc]
  erw [Scheme.toPresheafFiber_pointSmallEtaleSheafFiberIso_hom_app, ← Category.assoc,
    Scheme.toPresheafFiber_pointSmallEtaleSheafFiberIso_hom_app]
  refine Eq.trans ?_ ((galoisModuleSheaf K Ω ρ).obj.map_comp _ _)
  refine congrArg _ (congrArg Quiver.Hom.op ((Scheme.Etale.forget _).map_injective ?_))
  erw [Scheme.forget_map_pointSmallEtaleFiberCorepresentableBy_homEquiv_symm, Functor.map_comp,
    Scheme.forget_map_pointSmallEtaleFiberCorepresentableBy_homEquiv_symm]
  refine Over.OverMorphism.ext ?_
  erw [GeometricPoint.toPointFunctor_map_hom_app_left, galoisGeometricPointIso_hom_hom]
  rfl

/-- The map of Galois sets induced by `Spec σ` sends the point corresponding to the identity
embedding to its translate by `σ`. -/
theorem fiberFunctor_map_galoisEquivalence_map_spec_map (σ : Gal(Ω/K)) :
    (ContAction.fiberFunctor Gal(Ω/K)).map
        ((galoisEquivalence K Ω).functor.map ((spec (.of K)).map (finiteEtaleFieldHom K Ω σ).op))
        ((ContAction.fiberFunctor Gal(Ω/K)).map
          ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).inv
          (AlgHom.id K Ω)) =
      σ • (ContAction.fiberFunctor Gal(Ω/K)).map
          ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).inv
          (AlgHom.id K Ω) := by
  have h := congr(ConcreteCategory.hom ((ContAction.fiberFunctor Gal(Ω/K)).map
    $((specCompGaloisEquivalenceFunctorIso K Ω).inv.naturality (finiteEtaleFieldHom K Ω σ).op))
      (AlgHom.id K Ω))
  simp only [Functor.map_comp] at h
  refine h.symm.trans ?_
  have hσ : (ContAction.fiberFunctor Gal(Ω/K)).map
      ((galoisFiber K Ω).map (finiteEtaleFieldHom K Ω σ).op) (AlgHom.id K Ω) =
        σ • (AlgHom.id K Ω : (ContAction.fiberFunctor Gal(Ω/K)).obj
          ((galoisFiber K Ω).obj (op (finiteEtaleField K Ω)))) :=
    AlgHom.ext fun _ ↦ rfl
  change (ContAction.fiberFunctor Gal(Ω/K)).map
      ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).inv
      ((ContAction.fiberFunctor Gal(Ω/K)).map
        ((galoisFiber K Ω).map (finiteEtaleFieldHom K Ω σ).op) (AlgHom.id K Ω)) = _
  rw [hσ]
  exact ContAction.fiberFunctor_map_smul _ σ _

/-- **The stalk is `ρ` as a Galois representation.** Under `etaleStalkGaloisModuleSheafEquiv`, the
action of `σ ∈ Gal(Ω/K)` on the stalk (`galoisStalkMap`) is `ρ σ`. -/
theorem etaleStalkGaloisModuleSheafEquiv_galoisStalkMap (σ : Gal(Ω/K))
    (x : (etaleStalk Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj
      (galoisModuleSheaf K Ω ρ)) :
    etaleStalkGaloisModuleSheafEquiv K Ω ρ
        ((galoisStalkMap K Ω (ModuleCat.{u} Λ) σ).app _ x) =
      ρ σ (etaleStalkGaloisModuleSheafEquiv K Ω ρ x) := by
  rw [etaleStalkGaloisModuleSheafEquiv_apply, etaleStalkGaloisModuleSheafEquiv_apply]
  have h := congr(ConcreteCategory.hom
    $(galoisStalkMap_comp_pointSmallEtaleSheafFiberIso K Ω ρ σ) x)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  have h' := congr(ConcreteCategory.hom
    $(galoisModuleSheafObjIso_hom_naturality K Ω ρ
      ((spec (.of K)).map (finiteEtaleFieldHom K Ω σ).op))
      ((Scheme.pointSmallEtaleSheafFiberIso (A := ModuleCat.{u} Λ)
            (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) x))
  simp only at h'
  erw [h', ContAction.modulePresheafObjEquiv_map_apply,
    fiberFunctor_map_galoisEquivalence_map_spec_map]
  exact (ContAction.mem_equivariantMaps ρ _).1 (Subtype.property _) σ _

end TauCeti.FiniteEtaleScheme
