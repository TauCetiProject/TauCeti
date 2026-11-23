/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.AlgebraicGeometry.FiniteEtale.AffineFiber
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Basic
public import TauCeti.AlgebraicGeometry.FiniteEtale.Galois.Category
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
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

/-- The forward functor of the finite étale anti-equivalence, followed by the inclusion, is
Mathlib's `algSpec` on finite étale algebras. The definitions involved are not exposed, so this
is an equation of functors obtained by rewriting with
`finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor` and `spec_comp_ι`. -/
private theorem functor_comp_ι :
    (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).functor ⋙
        (finiteEtaleSchemeProperty (Spec (.of K))).ι =
      (CommAlgCat.finiteEtale (CommRingCat.of K)).ι.op ⋙ algSpec (CommRingCat.of K) := by
  rw [finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor, spec_comp_ι]

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
        algSpecCompCoyonedaIso (.of K) Ω)

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

/-- A point `y` of the geometric fibre of `X`, as a lift of `Spec Ω ⟶ Spec K` to `X`, goes to
the `K`-algebra map of that lift transported to the spectrum of the coordinate algebra. -/
private theorem fiberCompInclIsoFiniteEtaleFiber_hom_app_apply
    (X : FiniteEtaleScheme (Spec (.of K)))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :
    (fiberCompInclIsoFiniteEtaleFiber K Ω).hom.app X y =
      AlgebraicGeometry.algSpecHomEquivAlgHom _ (.of K Ω) ((fiberCompInclIso _).hom.app X y ≫
        ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).counitIso.inv.app X).hom ≫
          eqToHom (Functor.congr_obj (functor_comp_ι K) _)) := by
  refine (?_ : _ = (algSpecCompCoyonedaIso (.of K) Ω).hom.app _ _).trans
    (algSpecCompCoyonedaIso_hom_app_apply (.of K) Ω _ _)
  simp [fiberCompInclIsoFiniteEtaleFiber]
  -- The two sides differ only in how the types of the morphisms of types are written: `simp`
  -- unfolds composites of functors on one side only.
  rfl

/-- The `K`-algebra map that `fiberIsoFiniteEtaleFiber K Ω` attaches to a point `y` of the
geometric fibre of a finite étale `K`-scheme `X` has as spectrum the lift of `Spec Ω ⟶ Spec K`
to `X` given by `y`, transported to the spectrum of the coordinate algebra of `X`. That
spectrum is the target of the counit of `finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme` by
`finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor` and `spec_obj_obj`. -/
theorem algSpec_map_fiberIsoFiniteEtaleFiber_hom_app (X : FiniteEtaleScheme (Spec (.of K)))
    (y : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj X) :
    (algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom ((fiberIsoFiniteEtaleFiber K Ω).hom.app X y)).op =
      (fiberCompInclIso _).hom.app X y ≫
        ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).counitIso.inv.app X).hom ≫
          eqToHom (by
            rw [finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor, Functor.comp_obj,
              spec_obj_obj]
            -- `CommAlgCat.ofHom` writes the coordinate algebra `A` as `CommAlgCat.of K A`.
            rfl) := by
  have h : (fiberIsoFiniteEtaleFiber K Ω).hom.app X y =
      (fiberCompInclIsoFiniteEtaleFiber K Ω).hom.app X y := by
    have := FintypeCat.incl.map_preimage ((fiberCompInclIsoFiniteEtaleFiber K Ω).hom.app X)
    rw [ObjectProperty.ι_map] at this
    rw [fiberIsoFiniteEtaleFiber, Functor.fullyFaithfulCancelRight_hom_app, ← FintypeCat.hom_apply,
      this]
  rw [h, fiberCompInclIsoFiniteEtaleFiber_hom_app_apply,
    AlgebraicGeometry.algSpec_map_algSpecHomEquivAlgHom]
  -- Both casts are `eqToHom`s to the same object, written as `A` and as `CommAlgCat.of K A`.
  rfl

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
  ((FintypeCat.equivEquivIso.symm ((fiberIsoFiniteEtaleFiber K Ω).app X)).apply_symm_apply _).trans
    (AlgEquiv.smul_algHom_def σ _)

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
      -- `σ` acts on `A →ₐ[K] Ω` by postcomposition, and on the underlying finite set of a finite
      -- continuous `Gal(Ω/K)`-set through `ρ`.
      ((fiberIsoFiniteEtaleFiber_hom_app_smul K Ω X σ y).trans
        (AlgEquiv.smul_algHom_def σ _).symm).trans <|
        (galoisFiber_obj_ρ_apply K Ω _ σ _).symm.trans (Action.ρ_apply_eq_smul _ σ _)

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
