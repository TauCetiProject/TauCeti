/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Finiteness.Cardinality
import TauCeti.Algebra.Module.Projective.LinearMap

/-!
# Exactness and finite generation under coextension of scalars

Let `f : R →+* S` be a ring homomorphism. Mathlib's coextension of scalars
`ModuleCat.coextendScalars f` sends an `R`-module `M` to the `S`-module `Hom_R(S, M)`, with `S`
acting through right multiplication on the source. It is right adjoint to restriction of
scalars, so it is left exact. This file records when it is exact and when it preserves finite
generation.

* If `S` is a projective `R`-module through `f`, then `Hom_R(S, -)` preserves surjections, so
  coextension of scalars sends short exact sequences to short exact sequences.
* If `R` and `S` are algebras over a commutative ring `k`, `f` is a `k`-algebra homomorphism,
  `R` is a finitely generated `k`-module and `S` is a finitely generated projective `R`-module
  through `f`, then coextension of scalars sends finitely generated `R`-modules to finitely
  generated `S`-modules: `Hom_R(S, M)` is then finitely generated already over `k`.

The motivating instance is coinduction of representations from a subgroup `H` of a finite group
`G`: the group algebra `k[G]` is free of finite rank over `k[H]`, and `Hom_{k[H]}(k[G], M)` is the
coinduced module.

## Main definitions

* `AlgHom.coextendScalarsLinearEquiv`: `k`-linear identification of
  `(ModuleCat.coextendScalars f.toRingHom).obj M` with
  `(ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of S S) →ₗ[R] M`.
* `TauCeti.coextendScalarsBaseEquiv`: specialization identifying
  `(ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)` with `A →ₗ[k] V`.
* `AlgHom.finiteModulesCoextendScalars`: coextension of scalars as a functor between the
  categories of finitely generated modules.

## Main results

* `ModuleCat.coextendScalars_map_shortExact`: coextension of scalars along a ring homomorphism
  making `S` a projective `R`-module preserves short exact sequences.
* `AlgHom.isFG_coextendScalars`: coextension of scalars along a finite projective homomorphism of
  algebras over `k`, with `R` finite over `k`, preserves finite generation.
-/

public section

open CategoryTheory

universe v u₁ u₂

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

/-- Coextension of scalars is additive, as a right adjoint of the additive restriction of
scalars. -/
instance : (coextendScalars.{u₁, u₂, max v u₂} f).Additive :=
  (restrictCoextendScalarsAdj.{v, u₁, u₂} f).right_adjoint_additive

/-- **Coextension of scalars along a projective ring homomorphism is exact.** If `S` is a
projective `R`-module through `f`, then `Hom_R(S, -)` sends a short exact sequence of
`R`-modules to a short exact sequence of `S`-modules. -/
theorem coextendScalars_map_shortExact (hf : letI := f.toModule; Module.Projective R S)
    {T : ShortComplex (ModuleCat.{max v u₂} R)} (hT : T.ShortExact) :
    (T.map (coextendScalars f)).ShortExact := by
  have := hT.mono_f
  have := hT.epi_g
  refine { exact := hT.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance,
           mono_f := (coextendScalars f).map_mono T.f,
           epi_g := (epi_iff_surjective _).mpr fun x ↦ ?_ }
  -- A map out of the projective module `S` lifts along the surjection `T.g`.
  have : Module.Projective R ((restrictScalars f).obj (of S S)) := hf
  obtain ⟨y, hy⟩ := Module.projective_lifting_property T.g.hom
    (CoextendScalars.equiv f T.X₃ x) ((epi_iff_surjective _).mp inferInstance)
  exact ⟨(CoextendScalars.equiv f T.X₂).symm y, CoextendScalars.ext hy⟩

end ModuleCat

namespace AlgHom

variable {k : Type*} [CommRing k] {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] [Algebra k R]
  [Algebra k S] (f : R →ₐ[k] S)

private theorem coextendScalars_equiv_algebraMap_smul_apply (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M]
    (c : k) (x : (ModuleCat.coextendScalars f.toRingHom).obj M)
    (s : (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of S S)) :
    ModuleCat.CoextendScalars.equiv f.toRingHom M (algebraMap k S c • x) s =
      c • ModuleCat.CoextendScalars.equiv f.toRingHom M x s := by
  -- `(ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of S S)` has underlying type `S`.
  let s' : S := s
  have hs : algebraMap k R c • s = s' * algebraMap k S c := by
    rw [ModuleCat.restrictScalars.smul_def]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    exact Algebra.commutes c s'
  have hmul :=
    ModuleCat.CoextendScalars.smul_apply f.toRingHom M x (algebraMap k S c) s'
  rw [hmul, ← algebraMap_smul R c]
  exact (congrArg (ModuleCat.CoextendScalars.equiv f.toRingHom M x) hs.symm).trans
    (map_smul _ _ _)

/-- Over `k`, the coextension of scalars `(ModuleCat.coextendScalars f.toRingHom).obj M` is
`k`-linearly equivalent to `(ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of S S) →ₗ[R] M`.
-/
noncomputable def coextendScalarsLinearEquiv (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M] :
    letI : Module k ((ModuleCat.coextendScalars (f : R →+* S)).obj M) :=
      Module.restrictScalars k S ((ModuleCat.coextendScalars (f : R →+* S)).obj M)
    (ModuleCat.coextendScalars (f : R →+* S)).obj M ≃ₗ[k]
      ((ModuleCat.restrictScalars (f : R →+* S)).obj (ModuleCat.of S S) →ₗ[R] M) :=
  letI : Module k ((ModuleCat.coextendScalars (f : R →+* S)).obj M) :=
    Module.restrictScalars k S ((ModuleCat.coextendScalars (f : R →+* S)).obj M)
  { ModuleCat.CoextendScalars.equiv (f : R →+* S) M with
    map_smul' := fun c x ↦ LinearMap.ext fun s ↦
      coextendScalars_equiv_algebraMap_smul_apply f M c x s }

/-- Evaluating `AlgHom.coextendScalarsLinearEquiv` recovers `ModuleCat.CoextendScalars.equiv`. -/
@[simp]
theorem coextendScalarsLinearEquiv_apply (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M]
    (x : (ModuleCat.coextendScalars (f : R →+* S)).obj M)
    (s : (ModuleCat.restrictScalars (f : R →+* S)).obj (ModuleCat.of S S)) :
    f.coextendScalarsLinearEquiv M x s =
      ModuleCat.CoextendScalars.equiv f.toRingHom M x s := by
  rw [coextendScalarsLinearEquiv]; rfl

/-- Evaluating the inverse of `AlgHom.coextendScalarsLinearEquiv` recovers the inverse of
`ModuleCat.CoextendScalars.equiv`. -/
@[simp]
theorem coextendScalarsLinearEquiv_symm_apply (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M]
    (φ : (ModuleCat.restrictScalars (f : R →+* S)).obj (ModuleCat.of S S) →ₗ[R] M) :
    (f.coextendScalarsLinearEquiv M).symm φ =
      (ModuleCat.CoextendScalars.equiv f.toRingHom M).symm φ := by
  rw [coextendScalarsLinearEquiv]; rfl

/-- Applying `AlgHom.coextendScalarsLinearEquiv` to `algebraMap k S c • x` scales by `c`. -/
theorem coextendScalarsLinearEquiv_algebraMap_smul (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M] (c : k)
    (x : (ModuleCat.coextendScalars (f : R →+* S)).obj M) :
    f.coextendScalarsLinearEquiv M (algebraMap k S c • x) =
      c • f.coextendScalarsLinearEquiv M x :=
  LinearMap.ext fun s ↦ coextendScalars_equiv_algebraMap_smul_apply f M c x s

/-- Applying the inverse of `AlgHom.coextendScalarsLinearEquiv` to `c • φ` multiplies by
`algebraMap k S c`. -/
theorem coextendScalarsLinearEquiv_symm_smul (M : ModuleCat.{v} R)
    [Module k M] [IsScalarTower k R M] (c : k)
    (φ : (ModuleCat.restrictScalars (f : R →+* S)).obj (ModuleCat.of S S) →ₗ[R] M) :
    (f.coextendScalarsLinearEquiv M).symm (c • φ) =
      algebraMap k S c • (f.coextendScalarsLinearEquiv M).symm φ :=
  (f.coextendScalarsLinearEquiv M).injective (by
    rw [(f.coextendScalarsLinearEquiv M).apply_symm_apply,
      coextendScalarsLinearEquiv_algebraMap_smul,
      (f.coextendScalarsLinearEquiv M).apply_symm_apply])

/-- **Finite generation under coextension of scalars.** Let `f : R →ₐ[k] S` be a homomorphism of
algebras over a commutative ring `k`, with `R` finitely generated over `k` and `S` finitely
generated and projective over `R` through `f`. Then `Hom_R(S, M)` is a finitely generated
`S`-module for every finitely generated `R`-module `M`. -/
theorem isFG_coextendScalars [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S)
    {M : ModuleCat.{max v u₂} R} (hM : ModuleCat.isFG R M) :
    ModuleCat.isFG S ((ModuleCat.coextendScalars f.toRingHom).obj M) := by
  let S' := (ModuleCat.restrictScalars (f : R →+* S)).obj (ModuleCat.of S S)
  let X := (ModuleCat.coextendScalars (f : R →+* S)).obj M
  have : Module.Projective R S' := hproj
  have : Module.Finite R S' := hfin
  have : Module.Finite R M := hM
  -- The `k`-module structures on `M` and on `Hom_R(S, M)` come from those of `R` and `S`.
  let : Module k M := Module.restrictScalars k R M
  have : IsScalarTower k R M := IsScalarTower.restrictScalars k R M
  have : Module.Finite k M := .trans R M
  let : Module k X := Module.restrictScalars k S X
  have : IsScalarTower k S X := IsScalarTower.restrictScalars k S X
  let e : X ≃ₗ[k] (S' →ₗ[R] M) := f.coextendScalarsLinearEquiv M
  -- `Hom_R(S, M)` is finitely generated over `k` because `S` is finitely generated and projective
  -- over `R` and `M` is finitely generated over `k` (`Module.Finite.linearMap_of_projective`).
  have : Module.Finite k X := .equiv e.symm
  exact .of_restrictScalars_finite k S X

/-- **Coextension of scalars on finitely generated modules.** A homomorphism `f : R →ₐ[k] S`
of algebras over a commutative ring `k`, with `R` finitely generated over `k` and `S` finitely
generated and projective over `R` through `f`, induces a functor from the finitely generated
`R`-modules to the finitely generated `S`-modules, sending `M` to `Hom_R(S, M)`. -/
noncomputable def finiteModulesCoextendScalars [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S) :
    FGModuleCat.{max v u₂} R ⥤ FGModuleCat.{max v u₂} S :=
  (ModuleCat.isFG S).lift
    ((ModuleCat.isFG R).ι ⋙ ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f.toRingHom)
    fun M ↦ f.isFG_coextendScalars hproj hfin M.property

instance [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S) :
    (f.finiteModulesCoextendScalars hproj hfin).Additive := by
  unfold finiteModulesCoextendScalars
  infer_instance

/-- The underlying module of the image of a finitely generated module under
`AlgHom.finiteModulesCoextendScalars` is its coextension of scalars, naturally in the module. -/
noncomputable def finiteModulesCoextendScalarsCompιIso [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S) :
    f.finiteModulesCoextendScalars hproj hfin ⋙ (ModuleCat.isFG S).ι ≅
      (ModuleCat.isFG R).ι ⋙ ModuleCat.coextendScalars.{u₁, u₂, max v u₂} f.toRingHom :=
  ObjectProperty.liftCompιIso _ _ _

@[simp]
theorem finiteModulesCoextendScalars_obj_obj [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S) (M : FGModuleCat.{max v u₂} R) :
    ((f.finiteModulesCoextendScalars hproj hfin).obj M).obj =
      (ModuleCat.coextendScalars f.toRingHom).obj M.obj :=
  (rfl)

end AlgHom

namespace TauCeti

/-- For a `k`-algebra `A` and a `k`-module `V`, coextension of scalars
`(ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)` is `k`-linearly equivalent
to `A →ₗ[k] V`. -/
noncomputable def coextendScalarsBaseEquiv (k : Type u₁) (A : Type u₂) (V : Type v)
    [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] :
    let M := (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)
    letI : Module k M := Module.restrictScalars k A M
    M ≃ₗ[k] (A →ₗ[k] V) :=
  -- `ModuleCat.restrictScalars (algebraMap k A)` wraps `A` with the restricted `k`-action;
  -- `ModuleCat.restrictScalars.smul_def` identifies it with the `Algebra k A` scalar action.
  let eA : (ModuleCat.restrictScalars (algebraMap k A)).obj (ModuleCat.of A A) ≃ₗ[k] A :=
    { toFun := fun b ↦ b
      invFun := fun b ↦ b
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c b ↦ by
        let b' : A := b
        rw [ModuleCat.restrictScalars.smul_def, RingHom.id_apply]
        exact (smul_eq_mul _ _).trans (Algebra.smul_def c b').symm }
  ((Algebra.ofId k A).coextendScalarsLinearEquiv (ModuleCat.of k V)).trans
    (LinearEquiv.congrLeft (ModuleCat.of k V) k eA)

/-- Evaluating `TauCeti.coextendScalarsBaseEquiv` on a functional agrees with pointwise
evaluation. -/
@[simp]
theorem coextendScalarsBaseEquiv_apply (k : Type u₁) (A : Type u₂) (V : Type v)
    [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
    (ψ : (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) (b : A) :
    coextendScalarsBaseEquiv k A V ψ b = ψ b := by
  rw [coextendScalarsBaseEquiv]; rfl

/-- Evaluating `TauCeti.coextendScalarsBaseEquiv` on `a • ψ` right-translates the argument by `a`.
-/
theorem coextendScalarsBaseEquiv_smul_apply (k : Type u₁) (A : Type u₂) (V : Type v)
    [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] (a : A)
    (ψ : (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) (b : A) :
    coextendScalarsBaseEquiv k A V (a • ψ) b = coextendScalarsBaseEquiv k A V ψ (b * a) := by
  rw [coextendScalarsBaseEquiv_apply, ModuleCat.CoextendScalars.smul_apply,
    coextendScalarsBaseEquiv_apply]

/-- Applying `TauCeti.coextendScalarsBaseEquiv` to `algebraMap k A c • ψ` scales by `c`. -/
theorem coextendScalarsBaseEquiv_algebraMap_smul (k : Type u₁) (A : Type u₂) (V : Type v)
    [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] (c : k)
    (ψ : (ModuleCat.coextendScalars (algebraMap k A)).obj (ModuleCat.of k V)) :
    coextendScalarsBaseEquiv k A V (algebraMap k A c • ψ) =
      c • coextendScalarsBaseEquiv k A V ψ :=
  congrArg (LinearEquiv.congrLeft (ModuleCat.of k V) k _).toLinearMap
    ((Algebra.ofId k A).coextendScalarsLinearEquiv_algebraMap_smul (ModuleCat.of k V) c ψ)

/-- Applying the inverse of `TauCeti.coextendScalarsBaseEquiv` to `c • φ` multiplies by
`algebraMap k A c`. -/
theorem coextendScalarsBaseEquiv_symm_smul (k : Type u₁) (A : Type u₂) (V : Type v)
    [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] (c : k) (φ : A →ₗ[k] V) :
    (coextendScalarsBaseEquiv k A V).symm (c • φ) =
      algebraMap k A c • (coextendScalarsBaseEquiv k A V).symm φ :=
  (coextendScalarsBaseEquiv k A V).injective (by
    rw [(coextendScalarsBaseEquiv k A V).apply_symm_apply,
      coextendScalarsBaseEquiv_algebraMap_smul,
      (coextendScalarsBaseEquiv k A V).apply_symm_apply])

end TauCeti
