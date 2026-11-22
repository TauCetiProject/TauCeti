/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Algebraic glueing data and flat module recovery

A *glueing datum* over a ring diagram `R₁, R₂ → R₁₂` consists of modules `M₁` over `R₁`, `M₂` over
`R₂`, `M₁₂` over `R₁₂`, together with `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`
(Kedlaya–Liu, Definition 2.7.3). Given a base ring `R` mapping compatibly to `R₁`, `R₂`, `R₁₂`,
its `R`-module of sections `GlueingDatum.sections` consists of pairs `(m₁, m₂)` matching on `M₁₂`.

When `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is a flat `R`-module, flat base change recovers `N`
canonically as `N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R`
(`GlueingDatum.equivSectionsOfModule`).

## Main definitions

* `TauCeti.Huber.GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂`: modules `M₁`, `M₂`, `M₁₂` equipped with
  `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`.
* `TauCeti.Huber.GlueingDatum.diff`, `TauCeti.Huber.GlueingDatum.sections R D`,
  `TauCeti.Huber.GlueingDatum.fst`, `TauCeti.Huber.GlueingDatum.snd`,
  `TauCeti.Huber.GlueingDatum.lift`, `TauCeti.Huber.GlueingDatum.baseChangeFst`,
  `TauCeti.Huber.GlueingDatum.baseChangeSnd`, `TauCeti.Huber.GlueingDatum.ofModule`,
  `TauCeti.Huber.GlueingDatum.toSectionsOfModule`, and
  `TauCeti.Huber.GlueingDatum.equivSectionsOfModule`: the difference map, global sections of a
  glueing datum, projections and their universal lift and base changes, the canonical datum of an
  `R`-module, and recovery for flat modules.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.7, Definition 2.7.3 and Proposition 2.7.5.
-/

public section

open TensorProduct

namespace TauCeti.Huber

section GlueingDatum

variable {R₁ R₂ R₁₂ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [Algebra R₁ R₁₂] [Algebra R₂ R₁₂]
  {M₁ M₂ M₁₂ : Type*} [AddCommGroup M₁] [Module R₁ M₁] [AddCommGroup M₂] [Module R₂ M₂]
  [AddCommGroup M₁₂] [Module R₁₂ M₁₂]

variable (R₁ R₂ R₁₂ M₁ M₂ M₁₂) in
/-- A *glueing datum* on `R₁, R₂ → R₁₂`: modules `M₁` over `R₁`, `M₂` over `R₂`, `M₁₂` over
`R₁₂`, and `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂`
(Kedlaya–Liu, Definition 2.7.3). -/
@[ext]
structure GlueingDatum where
  /-- Identification `R₁₂ ⊗_{R₁} M₁ ≃ₗ[R₁₂] M₁₂`. -/
  ψ₁ : R₁₂ ⊗[R₁] M₁ ≃ₗ[R₁₂] M₁₂
  /-- Identification `R₁₂ ⊗_{R₂} M₂ ≃ₗ[R₁₂] M₁₂`. -/
  ψ₂ : R₁₂ ⊗[R₂] M₂ ≃ₗ[R₁₂] M₁₂

/-- Swapping the two pieces of a glueing datum. -/
def GlueingDatum.symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    GlueingDatum R₂ R₁ R₁₂ M₂ M₁ M₁₂ where
  ψ₁ := D.ψ₂
  ψ₂ := D.ψ₁

@[simp]
theorem GlueingDatum.symm_ψ₁ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.symm.ψ₁ = D.ψ₂ := by rfl

@[simp]
theorem GlueingDatum.symm_ψ₂ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.symm.ψ₂ = D.ψ₁ := by rfl

@[simp]
theorem GlueingDatum.symm_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.symm.symm = D := by rfl

section Sections

variable (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂]
  [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
  [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]

/-- The `R`-module of sections `{(m₁, m₂) ∈ M₁ × M₂ | ψ₁(1 ⊗ m₁) = ψ₂(1 ⊗ m₂)}` of a glueing
datum, over a base ring `R` mapping compatibly to `R₁`, `R₂`, `R₁₂`. -/
def GlueingDatum.sections (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : Submodule R (M₁ × M₂) where
  carrier := {x | D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd] at hx ⊢
    rw [← algebraMap_smul R₁ r x.1, ← algebraMap_smul R₂ r x.2, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, ← algebraMap_smul R₁₂ (algebraMap R R₁ r),
      ← algebraMap_smul R₁₂ (algebraMap R R₂ r), map_smul, map_smul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hx]

/-- The `R`-linear difference map `(m₁, m₂) ↦ ψ₁ (1 ⊗ m₁) - ψ₂ (1 ⊗ m₂)` out of `M₁ × M₂` whose
kernel is `D.sections R`. -/
def GlueingDatum.diff (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] :
    M₁ × M₂ →ₗ[R] M₁₂ where
  toFun x := D.ψ₁ (1 ⊗ₜ x.1) - D.ψ₂ (1 ⊗ₜ x.2)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add, map_add]
    abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    rw [← algebraMap_smul R₁ r x.1, ← algebraMap_smul R₂ r x.2, TensorProduct.tmul_smul,
      TensorProduct.tmul_smul, ← algebraMap_smul R₁₂ (algebraMap R R₁ r),
      ← algebraMap_smul R₁₂ (algebraMap R R₂ r), map_smul, map_smul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul, algebraMap_smul, smul_sub]

/-- First projection from the module of sections to `M₁`. -/
def GlueingDatum.fst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₁ :=
  (LinearMap.fst R M₁ M₂).comp (D.sections R).subtype

/-- Second projection from the module of sections to `M₂`. -/
def GlueingDatum.snd (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₂ :=
  (LinearMap.snd R M₁ M₂).comp (D.sections R).subtype

/-- Universal property of `D.sections R`: two compatible `R`-linear maps `f₁ : N →ₗ[R] M₁` and
`f₂ : N →ₗ[R] M₂` lift uniquely to an `R`-linear map `N →ₗ[R] D.sections R`. -/
def GlueingDatum.lift {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
    [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    {N : Type*} [AddCommMonoid N] [Module R N]
    (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    N →ₗ[R] D.sections R :=
  (f₁.prod f₂).codRestrict (D.sections R) h

/-- First base-changed projection `R₁ ⊗[R] D.sections R →ₗ[R₁] M₁`, induced by `D.fst R`. -/
noncomputable def GlueingDatum.baseChangeFst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    R₁ ⊗[R] D.sections R →ₗ[R₁] M₁ :=
  (D.fst R).liftBaseChange R₁

/-- Second base-changed projection `R₂ ⊗[R] D.sections R →ₗ[R₂] M₂`, induced by `D.snd R`. -/
noncomputable def GlueingDatum.baseChangeSnd (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    R₂ ⊗[R] D.sections R →ₗ[R₂] M₂ :=
  (D.snd R).liftBaseChange R₂

/-- Over a subsingleton overlap module `M₁₂`, the cocycle condition is vacuous and the sections
identify with `M₁ × M₂`. -/
def GlueingDatum.sectionsEquivProdOfSubsingleton [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R ≃ₗ[R] M₁ × M₂ :=
  LinearEquiv.ofTop (D.sections R) (Submodule.eq_top_iff'.mpr fun _ ↦ Subsingleton.elim _ _)

section Simps

variable {R}

@[simp]
theorem GlueingDatum.mem_sections_iff (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {x : M₁ × M₂} :
    x ∈ D.sections R ↔ D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2) := by rfl

@[simp]
theorem GlueingDatum.diff_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] (x : M₁ × M₂) :
    D.diff R x = D.ψ₁ (1 ⊗ₜ x.1) - D.ψ₂ (1 ⊗ₜ x.2) := by rfl

/-- The sections submodule is the kernel of the difference map `D.diff R`. -/
theorem GlueingDatum.sections_eq_ker (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] :
    D.sections R = LinearMap.ker (D.diff R) := by
  ext x
  simp [sub_eq_zero]

@[simp]
theorem GlueingDatum.fst_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.fst R x = x.val.1 := by rfl

@[simp]
theorem GlueingDatum.snd_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.snd R x = x.val.2 := by rfl

@[simp]
theorem GlueingDatum.coe_lift_apply {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) (n : N) :
    ((D.lift f₁ f₂ h n : D.sections R) : M₁ × M₂) = (f₁ n, f₂ n) := by rfl

theorem GlueingDatum.fst_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) (n : N) :
    D.fst R (D.lift f₁ f₂ h n) = f₁ n := by rfl

theorem GlueingDatum.snd_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) (n : N) :
    D.snd R (D.lift f₁ f₂ h n) = f₂ n := by rfl

@[simp]
theorem GlueingDatum.fst_comp_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    (D.fst R).comp (D.lift f₁ f₂ h) = f₁ := by
  ext n; rfl

@[simp]
theorem GlueingDatum.snd_comp_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    (D.snd R).comp (D.lift f₁ f₂ h) = f₂ := by
  ext n; rfl

/-- Two `R`-linear maps into `D.sections R` agree if their compositions with `D.fst R` and
`D.snd R` agree. -/
@[ext]
theorem GlueingDatum.sections_hom_ext {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {g₁ g₂ : N →ₗ[R] D.sections R}
    (h₁ : (D.fst R).comp g₁ = (D.fst R).comp g₂)
    (h₂ : (D.snd R).comp g₁ = (D.snd R).comp g₂) : g₁ = g₂ := by
  ext n
  · exact LinearMap.congr_fun h₁ n
  · exact LinearMap.congr_fun h₂ n

/-- Uniqueness of the universal lift into `D.sections R`: any `R`-linear map `g : N →ₗ[R]
D.sections R` recovering `f₁` and `f₂` under `D.fst R` and `D.snd R` equals `D.lift f₁ f₂ h`. -/
theorem GlueingDatum.eq_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {f₁ : N →ₗ[R] M₁} {f₂ : N →ₗ[R] M₂}
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) {g : N →ₗ[R] D.sections R}
    (h₁ : (D.fst R).comp g = f₁) (h₂ : (D.snd R).comp g = f₂) :
    g = D.lift f₁ f₂ h :=
  D.sections_hom_ext (h₁.trans (D.fst_comp_lift f₁ f₂ h).symm)
    (h₂.trans (D.snd_comp_lift f₁ f₂ h).symm)

@[simp]
theorem GlueingDatum.baseChangeFst_tmul (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (r₁ : R₁) (x : D.sections R) :
    D.baseChangeFst R (r₁ ⊗ₜ x) = r₁ • D.fst R x := by rfl

@[simp]
theorem GlueingDatum.baseChangeSnd_tmul (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (r₂ : R₂) (x : D.sections R) :
    D.baseChangeSnd R (r₂ ⊗ₜ x) = r₂ • D.snd R x := by rfl

/-- The defining overlap compatibility of the two projections of a section `x : D.sections R`. -/
theorem GlueingDatum.ψ₁_one_tmul_fst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : D.ψ₁ (1 ⊗ₜ D.fst R x) = D.ψ₂ (1 ⊗ₜ D.snd R x) :=
  x.property

@[simp]
theorem GlueingDatum.sectionsEquivProdOfSubsingleton_apply [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.sectionsEquivProdOfSubsingleton R x = x.val := by rfl

@[simp]
theorem GlueingDatum.coe_sectionsEquivProdOfSubsingleton_symm [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : M₁ × M₂) :
    ((D.sectionsEquivProdOfSubsingleton R).symm x : M₁ × M₂) = x := by rfl

end Simps

end Sections

section OfModule

variable (R₁ R₂ R₁₂) in
/-- The canonical glueing datum `(R₁ ⊗_R N, R₂ ⊗_R N, R₁₂ ⊗_R N)` attached to an `R`-module `N`. -/
def GlueingDatum.ofModule (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
    (N : Type*) [AddCommGroup N] [Module R N] :
    GlueingDatum R₁ R₂ R₁₂ (R₁ ⊗[R] N) (R₂ ⊗[R] N) (R₁₂ ⊗[R] N) where
  ψ₁ := AlgebraTensorModule.cancelBaseChange R R₁ R₁₂ R₁₂ N
  ψ₂ := AlgebraTensorModule.cancelBaseChange R R₂ R₁₂ R₁₂ N

variable {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
  [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
  {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
theorem GlueingDatum.ofModule_ψ₁_tmul (r₁₂ : R₁₂) (r₁ : R₁) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (r₁₂ ⊗ₜ (r₁ ⊗ₜ n)) = (r₁ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₁ R₁₂ r₁₂ n r₁

@[simp]
theorem GlueingDatum.ofModule_ψ₂_tmul (r₁₂ : R₁₂) (r₂ : R₂) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (r₁₂ ⊗ₜ (r₂ ⊗ₜ n)) = (r₂ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₂ R₁₂ r₁₂ n r₂

variable (R₁ R₂ R₁₂ R N) in
/-- The canonical `R`-linear comparison map `n ↦ (1 ⊗ n, 1 ⊗ n)` from an `R`-module `N` into the
sections of its associated glueing datum `GlueingDatum.ofModule`. -/
def GlueingDatum.toSectionsOfModule :
    N →ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R where
  toFun n := ⟨((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n), by simp⟩
  map_add' x y := by ext <;> simp [TensorProduct.tmul_add]
  map_smul' r x := by ext <;> simp [TensorProduct.tmul_smul]

@[simp]
theorem GlueingDatum.coe_toSectionsOfModule_apply (n : N) :
    (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) =
      ((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n) := by rfl

private theorem ofModule_cocycle_eq_rTensor (z : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :
    LinearMap.rTensor N
      ((IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
        (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂))
      ((TensorProduct.prodLeft R R R₁ R₂ N).symm z) =
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (1 ⊗ₜ z.1) -
      (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (1 ⊗ₜ z.2) := by
  obtain ⟨w, rfl⟩ := (TensorProduct.prodLeft R R R₁ R₂ N).surjective z
  rw [LinearEquiv.symm_apply_apply]
  induction w using TensorProduct.inductionOn with
  | tmul r n => rcases r with ⟨r₁, r₂⟩; simp [Algebra.algebraMap_eq_smul_one]
  | add x y hx hy =>
    rw [map_add, map_add, Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add,
      TensorProduct.tmul_add, map_add, map_add, hx, hy, add_sub_add_comm]

/-- Whenever `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is a flat `R`-module, the canonical map
`GlueingDatum.toSectionsOfModule` is bijective: flat base change preserves both injectivity of
`R → R₁ × R₂` and exactness at `(R₁ × R₂) ⊗_R N`. -/
theorem GlueingDatum.bijective_toSectionsOfModule_of_flat [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) :
    Function.Bijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N) := by
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  let e := TensorProduct.prodLeft R R R₁ R₂ N
  have hval : ∀ n : N, e (ι.rTensor N ((TensorProduct.lid R N).symm n)) =
      (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :=
    fun n ↦ by simp [e, ι]
  have hexN : Function.Exact (ι.rTensor N) (δ.rTensor N) := Module.Flat.rTensor_exact N hexact
  refine ⟨fun n₁ n₂ hn ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
  · have hsub := congrArg Subtype.val hn
    rw [← hval n₁, ← hval n₂] at hsub
    exact (TensorProduct.lid R N).symm.injective
      (Module.Flat.rTensor_preserves_injective_linearMap ι hinj (e.injective hsub))
  · obtain ⟨w, hw⟩ := (hexN (e.symm z)).mp
      (by rw [ofModule_cocycle_eq_rTensor z, sub_eq_zero]; exact hz)
    refine ⟨TensorProduct.lid R N w, Subtype.ext ?_⟩
    rw [← hval, LinearEquiv.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]

/-- For a flat `R`-module `N` over an exact ring diagram `0 → R → R₁ × R₂ → R₁₂`, the sections of
`GlueingDatum.ofModule R₁ R₂ R₁₂ R N` are canonically `R`-linearly isomorphic to `N`. -/
noncomputable def GlueingDatum.equivSectionsOfModule [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) :
    N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R :=
  LinearEquiv.ofBijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N)
    (GlueingDatum.bijective_toSectionsOfModule_of_flat hinj hexact)

@[simp]
theorem GlueingDatum.equivSectionsOfModule_apply [Module.Flat R N]
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2) (n : N) :
    GlueingDatum.equivSectionsOfModule hinj hexact n =
      GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n := by rfl

end OfModule

end GlueingDatum

end TauCeti.Huber

end
