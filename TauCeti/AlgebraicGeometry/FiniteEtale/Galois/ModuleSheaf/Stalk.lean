/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.ModuleSheaf.Basic
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

* `TauCeti.FiniteEtaleScheme.toEtaleSpecFiniteEtaleFieldIso`: for `L` finite separable over `K`,
  the finite étale `K`-scheme `Spec L`, in the small étale site of `Spec K`, is the étale point
  `Spec L ⟶ Spec K`.
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

section FiniteSeparable

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- `L`, finite and separable over `K`, as a finite étale `K`-algebra. -/
noncomputable abbrev finiteEtaleField : CommAlgCat.FiniteEtale.{u} K :=
  haveI : Algebra.Etale K L := Algebra.Etale.of_isSeparable K L
  CommAlgCat.FiniteEtale.of K L

/-- `σ` as an endomorphism of the finite étale `K`-algebra `L`. -/
noncomputable abbrev finiteEtaleFieldHom (σ : Gal(L/K)) :
    finiteEtaleField K L ⟶ finiteEtaleField K L :=
  haveI : Algebra.Etale K L := Algebra.Etale.of_isSeparable K L
  CommAlgCat.FiniteEtale.ofHom (σ : L →ₐ[K] L)

/-- The finite étale `K`-scheme `Spec L`, regarded in the small étale site of `Spec K`, is the
étale point `Spec L ⟶ Spec K`. -/
noncomputable def toEtaleSpecFiniteEtaleFieldIso :
    (toEtale _).obj ((spec (.of K)).obj (op (finiteEtaleField K L))) ≅
      Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (Scheme.Etale.forgetFullyFaithful _).preimageIso (specObjObjIso (.of K) (finiteEtaleField K L))

/-- The morphism over `Spec K` underlying `toEtaleSpecFiniteEtaleFieldIso` is `specObjObjIso`. -/
@[simp]
theorem forget_map_toEtaleSpecFiniteEtaleFieldIso_hom :
    (Scheme.Etale.forget _).map (toEtaleSpecFiniteEtaleFieldIso K L).hom =
      (specObjObjIso (.of K) (finiteEtaleField K L)).hom :=
  (Scheme.Etale.forgetFullyFaithful _).map_preimage _

end FiniteSeparable

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]
  [FiniteDimensional K Ω]

variable {Λ : Type u} [CommRing Λ] {M : Type u} [AddCommGroup M] [Module Λ M]
  (ρ : Representation Λ Gal(Ω/K) M)

/-- **The stalk of the étale sheaf of a Galois representation.** For `Ω` finite over `K`, the stalk
of `galoisModuleSheaf K Ω ρ` at the geometric point `Spec Ω ⟶ Spec K` is `M`: the point is étale,
so the stalk is the module of sections over `Spec Ω`, which are the `Gal(Ω/K)`-maps from the
`K`-embeddings `Ω → Ω` into `ρ`, and these are determined by their value at the identity. -/
noncomputable def etaleStalkGaloisModuleSheafEquiv :
    (etaleStalk Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj
      (galoisModuleSheaf K Ω ρ) ≃ₗ[Λ] M :=
  ((Scheme.pointSmallEtaleSheafFiberIso _).app _ ≪≫
    (galoisModuleSheaf K Ω ρ).obj.mapIso (toEtaleSpecFiniteEtaleFieldIso K Ω).op ≪≫
    galoisModuleSheafObjIso K Ω ρ _ ≪≫
    (ContAction.modulePresheaf ρ).mapIso
      ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).symm.op
    ).toLinearEquiv ≪≫ₗ
    -- `σ • AlgHom.id K Ω` is `σ` as an algebra map, so `Gal(Ω/K)` acts simply transitively on
    -- the `K`-embeddings `Ω → Ω` because every such embedding is an automorphism.
    ContAction.modulePresheafObjEquivOfBijective ρ
      (S := (galoisFiber K Ω).obj (op (finiteEtaleField K Ω)))
      (AlgHom.id K Ω) (Algebra.IsAlgebraic.algEquivEquivAlgHom K Ω).bijective

/-- `etaleStalkGaloisModuleSheafEquiv` sends an element of the stalk, viewed as a section over
`Spec Ω`, to the value at the identity embedding of the corresponding `Gal(Ω/K)`-map. -/
theorem etaleStalkGaloisModuleSheafEquiv_apply
    (x : (etaleStalk Λ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj
      (galoisModuleSheaf K Ω ρ)) :
    etaleStalkGaloisModuleSheafEquiv K Ω ρ x =
      (ContAction.modulePresheafObjEquiv ρ _
        ((galoisModuleSheafObjIso K Ω ρ ((spec (.of K)).obj (op (finiteEtaleField K Ω)))).hom
          ((galoisModuleSheaf K Ω ρ).obj.map (toEtaleSpecFiniteEtaleFieldIso K Ω).hom.op
            ((Scheme.pointSmallEtaleSheafFiberIso (A := ModuleCat.{u} Λ)
              (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app
                (galoisModuleSheaf K Ω ρ) x)))).val
        ((ContAction.fiberFunctor Gal(Ω/K)).map
          ((specCompGaloisEquivalenceFunctorIso K Ω).app (op (finiteEtaleField K Ω))).inv
          (AlgHom.id K Ω)) :=
  (ContAction.modulePresheafObjEquivOfBijective_apply ρ _ _ _).trans
    (ContAction.modulePresheafObjEquiv_map_apply ρ _ _ _)

/-- On sections over `Spec Ω`, the Galois action on the stalk is restriction along `Spec σ`. The
stalk is identified with these sections through `pointSmallEtaleSheafFiberIso` and
`toEtaleSpecFiniteEtaleFieldIso`. -/
theorem galoisStalkMap_comp_pointSmallEtaleSheafFiberIso (σ : Gal(Ω/K)) :
    (galoisStalkMap K Ω (ModuleCat.{u} Λ) σ).app (galoisModuleSheaf K Ω ρ) ≫
        (Scheme.pointSmallEtaleSheafFiberIso
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) ≫
          (galoisModuleSheaf K Ω ρ).obj.map (toEtaleSpecFiniteEtaleFieldIso K Ω).hom.op =
      (Scheme.pointSmallEtaleSheafFiberIso
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) ≫
        (galoisModuleSheaf K Ω ρ).obj.map (toEtaleSpecFiniteEtaleFieldIso K Ω).hom.op ≫
          (galoisModuleSheaf K Ω ρ).obj.map
            ((toEtale _).map ((spec (.of K)).map (finiteEtaleFieldHom K Ω σ).op)).op := by
  refine GrothendieckTopology.Point.presheafFiber_hom_ext _ fun Y y ↦ ?_
  -- `presheafFiber_hom_ext` takes germs of `(sheafToPresheaf _ _).obj F`, which is `F.obj` only
  -- after unfolding `sheafToPresheaf`, so the germ lemmas below need `erw` to match.
  erw [toPresheafFiber_galoisStalkMap_app_assoc, ← Category.assoc,
    Scheme.toPresheafFiber_pointSmallEtaleSheafFiberIso_hom_app]
  rw [← Functor.map_comp, ← Functor.map_comp]
  erw [← Category.assoc, Scheme.toPresheafFiber_pointSmallEtaleSheafFiberIso_hom_app]
  rw [← Functor.map_comp, ← op_comp, ← op_comp, ← op_comp]
  refine congrArg _ (congrArg Quiver.Hom.op ((Scheme.Etale.forget _).map_injective ?_))
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Scheme.forget_map_pointSmallEtaleFiberCorepresentableBy_homEquiv_symm]
  -- The Galois-translated lift is a lift of `(galoisGeometricPoint K Ω).hom`, which is
  -- `Spec.map (CommRingCat.ofHom (algebraMap K Ω))` only after unfolding the abbreviation.
  erw [Scheme.forget_map_pointSmallEtaleFiberCorepresentableBy_homEquiv_symm]
  rw [forget_map_toEtale_map, forget_map_toEtaleSpecFiniteEtaleFieldIso_hom]
  -- The composite passes through `(Scheme.Etale.forget _).obj ((toEtale _).obj X)`, which is
  -- `X.obj` only after unfolding `toEtale`.
  erw [spec_map_hom_comp_specObjObjIso_hom]
  refine (congrArg (_ ≫ ·) (Over.OverMorphism.ext ?_)).trans (Category.assoc _ _ _).symm
  -- The lift `y` is an element of the fibre functor, a morphism over `Spec K` only after
  -- unfolding `pointSmallEtale`.
  erw [GeometricPoint.toPointFunctor_map_hom_app_left, galoisGeometricPointIso_hom_hom]
  -- `finiteEtaleFieldHom K Ω σ` is `σ` as a `K`-algebra map, so both sides are `Spec σ ≫ y.left`.
  rfl

/-- The map of Galois sets induced by `Spec σ` sends the point corresponding to the identity
embedding to its translate by `σ`. -/
private theorem fiberFunctor_map_galoisEquivalence_map_spec_map (σ : Gal(Ω/K)) :
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
  -- `galoisFiber` acts on morphisms by precomposition, and `σ • φ` is postcomposition with `σ`:
  -- applied to the identity embedding, both give `σ`.
  have hσ : (ContAction.fiberFunctor Gal(Ω/K)).map
      ((galoisFiber K Ω).map (finiteEtaleFieldHom K Ω σ).op) (AlgHom.id K Ω) =
        σ • (AlgHom.id K Ω : (ContAction.fiberFunctor Gal(Ω/K)).obj
          ((galoisFiber K Ω).obj (op (finiteEtaleField K Ω)))) :=
    (galoisFiber_map_hom_apply K Ω _ _).trans (AlgHom.ext fun _ ↦ rfl)
  -- Evaluate the composite of maps of Galois sets in `h` pointwise; `rw` and `simp` with
  -- `ConcreteCategory.comp_apply` do not see through the composite of functions here.
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
      ((galoisModuleSheaf K Ω ρ).obj.map (toEtaleSpecFiniteEtaleFieldIso K Ω).hom.op
        ((Scheme.pointSmallEtaleSheafFiberIso (A := ModuleCat.{u} Λ)
          (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).hom.app (galoisModuleSheaf K Ω ρ) x)))
  simp only [ConcreteCategory.comp_apply] at h'
  rw [h', ContAction.modulePresheafObjEquiv_map_apply,
    fiberFunctor_map_galoisEquivalence_map_spec_map]
  exact (ContAction.mem_equivariantMaps ρ _).1 (Subtype.property _) σ _

end TauCeti.FiniteEtaleScheme
