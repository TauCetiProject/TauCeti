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

/-- **Finite generation under coextension of scalars.** Let `f : R →ₐ[k] S` be a homomorphism of
algebras over a commutative ring `k`, with `R` finitely generated over `k` and `S` finitely
generated and projective over `R` through `f`. Then `Hom_R(S, M)` is a finitely generated
`S`-module for every finitely generated `R`-module `M`. -/
theorem isFG_coextendScalars [Module.Finite k R]
    (hproj : letI := f.toRingHom.toModule; Module.Projective R S)
    (hfin : letI := f.toRingHom.toModule; Module.Finite R S)
    {M : ModuleCat.{max v u₂} R} (hM : ModuleCat.isFG R M) :
    ModuleCat.isFG S ((ModuleCat.coextendScalars f.toRingHom).obj M) := by
  let S' := (ModuleCat.restrictScalars f.toRingHom).obj (ModuleCat.of S S)
  let X := (ModuleCat.coextendScalars f.toRingHom).obj M
  have : Module.Projective R S' := hproj
  have : Module.Finite R S' := hfin
  have : Module.Finite R M := hM
  -- The `k`-module structures on `M` and on `Hom_R(S, M)` come from those of `R` and `S`.
  let : Module k M := Module.compHom M (algebraMap k R)
  have : IsScalarTower k R M := ⟨fun c r m ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : Module.Finite k M := .trans R M
  let : Module k X := Module.compHom X (algebraMap k S)
  have : IsScalarTower k S X := ⟨fun c s x ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
  -- Over `k`, the action of `S` on `Hom_R(S, M)` is the pointwise action on values.
  let e : X ≃ₗ[k] (S' →ₗ[R] M) :=
    { ModuleCat.CoextendScalars.equiv f.toRingHom M with
      map_smul' := fun c x ↦ LinearMap.ext fun s ↦ by
        have hs : algebraMap k R c • s = (show S from s) * algebraMap k S c := by
          rw [ModuleCat.restrictScalars.smul_def]
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
          exact Algebra.commutes c (show S from s)
        -- Both `k`-actions are defined through `Module.compHom`; unfold them to the actions of
        -- `algebraMap k S c` and `algebraMap k R c`.
        change ModuleCat.CoextendScalars.equiv f.toRingHom M (algebraMap k S c • x) s =
          algebraMap k R c • ModuleCat.CoextendScalars.equiv f.toRingHom M x s
        exact (congrArg (ModuleCat.CoextendScalars.equiv f.toRingHom M x) hs.symm).trans
          (map_smul _ _ _) }
  -- `S` is a direct summand of some `R^n`, so `Hom_R(S, M)` is a quotient of `Hom_R(R^n, M)`,
  -- which is finitely generated over `k` because `M` is.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R S'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let restrict : ((Fin n → R) →ₗ[R] M) →ₗ[k] (S' →ₗ[R] M) :=
    { toFun := fun ψ ↦ ψ ∘ₗ σ
      map_add' := fun _ _ ↦ LinearMap.add_comp _ _ _
      map_smul' := fun _ _ ↦ LinearMap.smul_comp _ _ _ }
  have hrestrict : Function.Surjective restrict := fun ψ ↦
    ⟨ψ ∘ₗ π, by simp only [restrict, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_assoc, hσ,
      LinearMap.comp_id]⟩
  have : Module.Finite k (S' →ₗ[R] M) := .of_surjective restrict hrestrict
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
