/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Module.Right.DGCategory
public import TauCeti.Algebra.Homology.AInfinity.Module.Right.Restriction.Basic
public import TauCeti.CategoryTheory.DG.Functor.Basic

/-!
# Restriction of right A-infinity modules as a DG functor

Let `f : A ⟶ B` be a morphism of `A∞` algebras with coaugmented bar map `F : Tᶜ(sA) ⟶ Tᶜ(sB)`.
Restriction along `f` (`TauCeti.AInfinityRightModule.restrictScalars`) acts not only on module
morphisms but on all cochains of the morphism complexes.  A cochain `φ` of degree `p` from `M` to
`N` over `B` restricts to the cochain of degree `p` over `A` whose Taylor map is the Taylor map of
`φ` read through `id ⊗ F`.  This is the unique cochain intertwined with `φ` by the maps `id ⊗ F` of
cofree bar comodules (`TauCeti.AInfinityRightModule.homCochains.eq_restrictScalars_iff`).

Restriction of cochains commutes with the differentials of the morphism complexes, preserves
identities and composition, and on the closed degree-zero cochains it is the restriction of module
morphisms.  Hence restriction is a DG functor between the DG categories of right `A∞` modules
(`TauCeti.AInfinityRightModuleCat.restrictScalarsDGFunctor`), whose underlying functor on closed
degree-zero morphisms is the restriction functor `TauCeti.AInfinityRightModuleCat.restrictScalars`.
In particular it induces the restriction functor on homotopy categories of right `A∞` modules,
through `CategoryTheory.EnrichedFunctor.mapDGHomotopyCategory`.  This is the form of restriction
through which an `A∞` quasi-isomorphism of algebras compares categories of modules up to homotopy.

## Main definitions

* `TauCeti.AInfinityRightModule.homCochains.restrictScalars`: the restriction of cochains of the
  morphism complex along an `A∞` morphism.
* `TauCeti.AInfinityRightModuleCat.restrictScalarsDGFunctor`: restriction along an `A∞` morphism as
  a DG functor between the DG categories of right `A∞` modules.

## Main results

* `TauCeti.AInfinityRightModule.homCochains.lTensor_coaugmentedBarMap_comp_restrictScalars` and
  `TauCeti.AInfinityRightModule.homCochains.eq_restrictScalars_iff`: the restriction of a cochain
  is the unique cochain intertwined with it by the maps `id ⊗ F`.
* `TauCeti.AInfinityRightModule.homCochains.restrictScalars_homDifferential`: restriction of
  cochains commutes with the differentials.
* `TauCeti.AInfinityRightModule.homCochains.restrictScalars_comp` and
  `TauCeti.AInfinityRightModule.homCochains.restrictScalars_id`: restriction of cochains preserves
  composition and identities.
* `TauCeti.AInfinityRightModule.homCochains.coe_restrictScalars_barMap`: on the bar map of a module
  morphism, restriction of cochains is restriction of module morphisms.
* `TauCeti.AInfinityRightModuleCat.dgMap_restrictScalarsDGFunctor_homEquivDGCycles`: the
  underlying functor of the DG functor on closed degree-zero morphisms is the restriction
  functor.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 4.
* K. Lefèvre-Hasegawa, *Sur les A-infini catégories*, thèse de doctorat, Université Paris 7
  (2003), Chapter 4.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u uR uA uB uM uN uP

attribute [local instance] Comodule.cofree

namespace AInfinityRightModule

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  {MM : AInfinityRightModule BB M} {NN : AInfinityRightModule BB N}
  {PP : AInfinityRightModule BB P}

namespace homCochains

variable (f : AInfinityHom AA BB)

/-- The cofree lift of the Taylor map of a cochain of degree `p` after `id ⊗ F` is a cochain of
degree `p` between the restricted modules. -/
private theorem cofreeLift_taylor_comp_mem {p : ℤ} (φ : homCochains MM NN p) :
    (Comodule.Hom.cofreeLift (C := TensorWords R A)
      (((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor N ∘ₗ
          (φ : (M ⊗[R] TensorWords R B) →ₗ[R] N ⊗[R] TensorWords R B)) ∘ₗ
        f.coaugmentedBarMap.lTensor M)).toLinearMap ∈
      homCochains (MM.restrictScalars f) (NN.restrictScalars f) p := by
  refine cofreeLift_mem_homCochains ?_
  rw [restrictScalars_grading, restrictScalars_grading]
  simpa only [zero_add] using
    (isHomogeneous_taylor φ).comp (isHomogeneous_lTensor_coaugmentedBarMap f MM.grading)

/-- The **restriction of a cochain** of degree `p` along an `A∞` morphism `f`: the cochain of
degree `p` between the restricted modules whose Taylor map is the Taylor map of the cochain after
`id ⊗ F`, for `F` the coaugmented bar map of `f`. -/
noncomputable def restrictScalars (p : ℤ) :
    homCochains MM NN p →ₗ[R] homCochains (MM.restrictScalars f) (NN.restrictScalars f) p where
  toFun φ := ⟨_, cofreeLift_taylor_comp_mem f φ⟩
  map_add' φ ψ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, LinearMap.comp_add, LinearMap.add_comp,
      Comodule.Hom.cofreeLift_toLinearMap, LinearMap.rTensor_add]
  map_smul' r φ := by
    apply Subtype.ext
    simp only [SetLike.val_smul, LinearMap.comp_smul, LinearMap.smul_comp,
      Comodule.Hom.cofreeLift_toLinearMap, LinearMap.rTensor_smul, RingHom.id_apply]

/-- A restricted cochain is the cofree lift of the Taylor map of the cochain after `id ⊗ F`. -/
theorem coe_restrictScalars {p : ℤ} (φ : homCochains MM NN p) :
    (restrictScalars f p φ : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      (Comodule.Hom.cofreeLift (C := TensorWords R A)
        (((TensorProduct.rid R N).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor N ∘ₗ
            (φ : (M ⊗[R] TensorWords R B) →ₗ[R] N ⊗[R] TensorWords R B)) ∘ₗ
          f.coaugmentedBarMap.lTensor M)).toLinearMap :=
  (rfl)

/-- The Taylor map of a restricted cochain is the Taylor map of the cochain after `id ⊗ F`. -/
theorem taylor_restrictScalars {p : ℤ} (φ : homCochains MM NN p) :
    (TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor N ∘ₗ
          (restrictScalars f p φ : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      ((TensorProduct.rid R N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R B)).lTensor N ∘ₗ
          (φ : (M ⊗[R] TensorWords R B) →ₗ[R] N ⊗[R] TensorWords R B)) ∘ₗ
        f.coaugmentedBarMap.lTensor M := by
  rw [coe_restrictScalars, Comodule.Hom.rid_comp_lTensor_counit_comp_cofreeLift]

/-- **A restricted cochain is intertwined with the original cochain** by the maps `id ⊗ F` of
cofree bar comodules. -/
theorem lTensor_coaugmentedBarMap_comp_restrictScalars {p : ℤ} (φ : homCochains MM NN p) :
    f.coaugmentedBarMap.lTensor N ∘ₗ
        (restrictScalars f p φ : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      (φ : (M ⊗[R] TensorWords R B) →ₗ[R] N ⊗[R] TensorWords R B) ∘ₗ
        f.coaugmentedBarMap.lTensor M := by
  rw [coe_restrictScalars, lTensor_coaugmentedBarMap_comp_cofreeLift, ← eq_cofreeLift]

/-- **Characterization of restricted cochains**: a cochain between the restricted modules is the
restriction of `φ` exactly when the maps `id ⊗ F` intertwine it with `φ`. -/
theorem eq_restrictScalars_iff {p : ℤ} (φ : homCochains MM NN p)
    (ψ : homCochains (MM.restrictScalars f) (NN.restrictScalars f) p) :
    ψ = restrictScalars f p φ ↔
      f.coaugmentedBarMap.lTensor N ∘ₗ
          (ψ : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
        (φ : (M ⊗[R] TensorWords R B) →ₗ[R] N ⊗[R] TensorWords R B) ∘ₗ
          f.coaugmentedBarMap.lTensor M := by
  refine ⟨fun h ↦ h ▸ lTensor_coaugmentedBarMap_comp_restrictScalars f φ, fun h ↦ ext_taylor ?_⟩
  rw [taylor_restrictScalars, ← rid_comp_lTensor_counit_comp_lTensor_coaugmentedBarMap f, h]
  simp only [LinearMap.comp_assoc]

/-- **Restriction of cochains commutes with the differentials** of the morphism complexes. -/
@[simp]
theorem restrictScalars_homDifferential {p : ℤ} (φ : homCochains MM NN p) :
    restrictScalars f (p + 1) (homDifferential MM NN p φ) =
      homDifferential (MM.restrictScalars f) (NN.restrictScalars f) p (restrictScalars f p φ) := by
  refine ext_taylor ?_
  rw [taylor_restrictScalars, taylor_homDifferential, taylor_homDifferential,
    taylor_restrictScalars, restrictScalars_taylor]
  simp only [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_assoc,
    lTensor_coaugmentedBarMap_comp_restrictScalars, barDifferential_comp_lTensor_coaugmentedBarMap]

/-- **Restriction of cochains preserves composition.** -/
@[simp]
theorem restrictScalars_comp {p q n : ℤ} (h : p + q = n) (ψ : homCochains NN PP p)
    (φ : homCochains MM NN q) :
    restrictScalars f n (comp h ψ φ) =
      comp h (restrictScalars f p ψ) (restrictScalars f q φ) := by
  have hψ := congrArg
    (· ∘ₗ (restrictScalars f q φ : (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A))
    (taylor_restrictScalars f ψ)
  refine ext_taylor ?_
  simp only [LinearMap.comp_assoc] at hψ
  simp only [taylor_restrictScalars, coe_comp, LinearMap.comp_assoc]
  rw [hψ, lTensor_coaugmentedBarMap_comp_restrictScalars]

/-- On the bar map of a module morphism, restriction of cochains is restriction of the module
morphism. -/
@[simp]
theorem coe_restrictScalars_barMap (φ : AInfinityRightModuleHom MM NN) :
    (restrictScalars f 0 ⟨φ.barMap, φ.barMap_mem_homCochains⟩ :
        (M ⊗[R] TensorWords R A) →ₗ[R] N ⊗[R] TensorWords R A) =
      (φ.restrictScalars f).barMap := by
  rw [coe_restrictScalars, AInfinityRightModuleHom.barMap_eq_cofreeLift (φ.restrictScalars f),
    AInfinityRightModuleHom.taylor_restrictScalars, AInfinityRightModuleHom.taylor_def]

/-- **Restriction of cochains preserves identities.** -/
@[simp]
theorem restrictScalars_id : restrictScalars f 0 (id MM) = id (MM.restrictScalars f) := by
  have hM : id MM = ⟨_, (AInfinityRightModuleHom.id MM).barMap_mem_homCochains⟩ :=
    Subtype.ext (coe_id.trans (AInfinityRightModuleHom.barMap_id MM).symm)
  apply Subtype.ext
  rw [hM, coe_restrictScalars_barMap, AInfinityRightModuleHom.restrictScalars_id,
    AInfinityRightModuleHom.barMap_id, coe_id]

end homCochains

end AInfinityRightModule

/-! ### The restriction DG functor -/

namespace AInfinityRightModuleCat

open AInfinityRightModule

variable {R : Type u} {A : Type u} {B : Type u} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B} (f : AInfinityHom AA BB)

/-- **Restriction along an `A∞` morphism `f : A ⟶ B` as a DG functor** from the DG category of right
`A∞` modules over `B` to that over `A`: it restricts modules along `f`, and restricts the cochains
of the morphism complexes (`TauCeti.AInfinityRightModule.homCochains.restrictScalars`). -/
noncomputable def restrictScalarsDGFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (AInfinityRightModuleCat.{u, u, u} BB)
      (AInfinityRightModuleCat.{u, u, u} AA) :=
  EnrichedFunctor.ofDGMap (fun M ↦ of (M.str.restrictScalars f))
    (fun {M N} n ↦ (dgHomLinearEquivCochains _ _ n).symm.toLinearMap ∘ₗ
      homCochains.restrictScalars f n ∘ₗ (dgHomLinearEquivCochains M N n).toLinearMap)
    (fun n φ ↦ (dgHomLinearEquivCochains _ _ (n + 1)).injective <| by
      rw [dgDifferential_eq (of _)]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        dgDifferential_eq, homCochains.restrictScalars_homDifferential])
    (fun M ↦ (dgHomLinearEquivCochains _ _ 0).injective <| by
      rw [dgId_eq (of _)]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        dgId_eq, homCochains.restrictScalars_id])
    (fun φ ψ h ↦ (dgHomLinearEquivCochains _ _ _).injective <| by
      rw [dgComp_eq (of _) (of _) (of _)]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        dgComp_eq]
      rw [← homCochains.restrictScalars_comp]
      exact (homCochains.restrictScalars f _).map_smul_of_tower _ _)

/-- The restriction DG functor restricts modules. -/
@[simp]
theorem restrictScalarsDGFunctor_obj (M : AInfinityRightModuleCat.{u, u, u} BB) :
    (restrictScalarsDGFunctor f).obj M = (restrictScalars f).obj M :=
  (rfl)

/-- Transport homogeneous morphisms from the objects of the restriction DG functor to the
corresponding objects of the underlying restriction functor. -/
noncomputable def dgHomLinearEquivRestrictScalarsDGFunctor
    (M N : AInfinityRightModuleCat.{u, u, u} BB) (n : ℤ) :
    DGHom R n ((restrictScalarsDGFunctor f).obj M) ((restrictScalarsDGFunctor f).obj N) ≃ₗ[R]
      DGHom R n ((restrictScalars f).obj M) ((restrictScalars f).obj N) :=
  LinearEquiv.cast (R := R)
    (M := fun P : AInfinityRightModuleCat.{u, u, u} AA ×
        AInfinityRightModuleCat.{u, u, u} AA ↦ DGHom R n P.1 P.2) <|
      congrArg₂ (·, ·) (restrictScalarsDGFunctor_obj f M)
        (restrictScalarsDGFunctor_obj f N)

/-- The restriction DG functor restricts cochains of the morphism complexes. -/
@[simp]
theorem dgHomLinearEquivCochains_dgMap_restrictScalarsDGFunctor
    {M N : AInfinityRightModuleCat.{u, u, u} BB} {n : ℤ} (φ : DGHom R n M N) :
    dgHomLinearEquivCochains ((restrictScalars f).obj M) ((restrictScalars f).obj N) n
        (dgHomLinearEquivRestrictScalarsDGFunctor f M N n
          ((restrictScalarsDGFunctor f).dgMap n φ)) =
      homCochains.restrictScalars f n (dgHomLinearEquivCochains M N n φ) := by
  have hM := restrictScalarsDGFunctor_obj f M
  have hN := restrictScalarsDGFunctor_obj f N
  cases hM
  cases hN
  simp only [dgHomLinearEquivRestrictScalarsDGFunctor]
  rw [EnrichedFunctor.dgMap_apply]
  -- The degree-`n` component of the chain map of `EnrichedFunctor.ofDGMap` is the prescribed map.
  exact LinearEquiv.apply_symm_apply _ _

/-- **The restriction DG functor restricts module morphisms**: on the closed degree-zero morphism
of a module morphism `φ`, it is the closed degree-zero morphism of the restriction of `φ`. -/
@[simp]
theorem dgMap_restrictScalarsDGFunctor_homEquivDGCycles
    {M N : AInfinityRightModuleCat.{u, u, u} BB} (φ : M ⟶ N) :
    dgHomLinearEquivRestrictScalarsDGFunctor f M N 0
        ((restrictScalarsDGFunctor f).dgMap 0
          (homEquivDGCycles M N φ : DGHom R 0 M N)) =
      (homEquivDGCycles ((restrictScalars f).obj M) ((restrictScalars f).obj N)
        ((restrictScalars f).map φ) : DGHom R 0 _ _) := by
  have hφ : dgHomLinearEquivCochains M N 0 (homEquivDGCycles M N φ : DGHom R 0 M N) =
      ⟨φ.barMap, φ.barMap_mem_homCochains⟩ :=
    Subtype.ext (coe_homEquivDGCycles_apply φ)
  apply (dgHomLinearEquivCochains ((restrictScalars f).obj M)
    ((restrictScalars f).obj N) 0).injective
  rw [dgHomLinearEquivCochains_dgMap_restrictScalarsDGFunctor, hφ]
  exact Subtype.ext <| (homCochains.coe_restrictScalars_barMap f φ).trans
    (coe_homEquivDGCycles_apply ((restrictScalars f).map φ)).symm

end AInfinityRightModuleCat

end TauCeti
