/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.Patching.Projective
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Algebraic glueing data and flat module recovery

A *glueing datum* over `R₁, R₂ → R₁₂` consists of modules `M₁`, `M₂`, `M₁₂` over `R₁`, `R₂`,
`R₁₂` and `R₁₂`-linear isomorphisms `ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂` (Kedlaya–Liu, Definition
2.7.3). Over a base ring `R`, its module of sections `GlueingDatum.sections` consists of pairs
`(m₁, m₂)` matching in `M₁₂`, identified with `TauCeti.PatchedModule` via
`GlueingDatum.sectionsEquivPatchedModule`. When `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is a
flat `R`-module, `GlueingDatum.equivSectionsOfModule` recovers `N` from `GlueingDatum.ofModule`.

## Main definitions

* `TauCeti.GlueingDatum`, `TauCeti.GlueingDatum.patchedTransition`,
  `TauCeti.GlueingDatum.sectionsEquivPatchedModule`, and
  `TauCeti.GlueingDatum.sectionsOfModuleEquivPatchedModule`.
* `TauCeti.GlueingDatum.diff`, `sections`, `sectionsEquivSymm`, `fst`, `snd`, `lift`,
  `baseChangeFst`, `baseChangeSnd`, `ofModule`, `toSectionsOfModule`, and `equivSectionsOfModule`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.7, Definition 2.7.3 and Proposition 2.7.5.
-/

public section

open TensorProduct

namespace TauCeti

section GlueingDatum
variable {R₁ R₂ R₁₂ : Type*} [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [Algebra R₁ R₁₂] [Algebra R₂ R₁₂] {M₁ M₂ M₁₂ : Type*} [AddCommGroup M₁] [Module R₁ M₁]
  [AddCommGroup M₂] [Module R₂ M₂] [AddCommGroup M₁₂] [Module R₁₂ M₁₂]

variable (R₁ R₂ R₁₂ M₁ M₂ M₁₂) in
/-- A *glueing datum* on `R₁, R₂ → R₁₂`: modules `M₁`, `M₂`, `M₁₂` and `R₁₂`-linear isomorphisms
`ψᵢ : R₁₂ ⊗_{Rᵢ} Mᵢ ≃ₗ[R₁₂] M₁₂` (Kedlaya–Liu, Definition 2.7.3). -/
@[ext] structure GlueingDatum where
  /-- Identification `R₁₂ ⊗_{R₁} M₁ ≃ₗ[R₁₂] M₁₂`. -/
  ψ₁ : R₁₂ ⊗[R₁] M₁ ≃ₗ[R₁₂] M₁₂
  /-- Identification `R₁₂ ⊗_{R₂} M₂ ≃ₗ[R₁₂] M₁₂`. -/
  ψ₂ : R₁₂ ⊗[R₂] M₂ ≃ₗ[R₁₂] M₁₂

/-- Swapping the two pieces of a glueing datum. -/
def GlueingDatum.symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    GlueingDatum R₂ R₁ R₁₂ M₂ M₁ M₁₂ := ⟨D.ψ₂, D.ψ₁⟩

@[simp] theorem GlueingDatum.symm_ψ₁ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.symm.ψ₁ = D.ψ₂ :=
  by rfl
@[simp] theorem GlueingDatum.symm_ψ₂ (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.symm.ψ₂ = D.ψ₁ :=
  by rfl
@[simp] theorem GlueingDatum.symm_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.symm.symm = D :=
  by rfl

/-- The transition isomorphism `R₁₂ ⊗_{R₁} M₁ ≃ₗ[R₁₂] R₁₂ ⊗_{R₂} M₂` from `D.ψ₂.symm ∘ D.ψ₁`. -/
noncomputable def GlueingDatum.patchedTransition (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    BalancedExtension (algebraMap R₁ R₁₂) M₁ ≃ₗ[R₁₂] BalancedExtension (algebraMap R₂ R₁₂) M₂ :=
  (balancedExtensionEquivTensorProduct R₁ R₁₂ M₁).trans
    ((D.ψ₁.trans D.ψ₂.symm).trans (balancedExtensionEquivTensorProduct R₂ R₁₂ M₂).symm)

@[simp] theorem GlueingDatum.patchedTransition_tmul (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (r₁₂ : R₁₂) (m₁ : M₁) :
    D.patchedTransition (BalancedExtension.tmul (algebraMap R₁ R₁₂) r₁₂ m₁) =
      (balancedExtensionEquivTensorProduct R₂ R₁₂ M₂).symm (D.ψ₂.symm (D.ψ₁ (r₁₂ ⊗ₜ m₁))) := by
  simp [GlueingDatum.patchedTransition]

section CommSq
variable (R R₁ R₂ R₁₂ : Type*) [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₁₂]
  [Algebra R R₁] [Algebra R R₂] [Algebra R R₁₂] [Algebra R₁ R₁₂] [Algebra R₂ R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]

/-- The commutative square `(algebraMap R₁ R₁₂).comp (algebraMap R R₁) =
(algebraMap R₂ R₁₂).comp (algebraMap R R₂)` underlying a glueing datum over `R`. -/
theorem GlueingDatum.commSq :
    (algebraMap R₁ R₁₂).comp (algebraMap R R₁) = (algebraMap R₂ R₁₂).comp (algebraMap R R₂) :=
  (IsScalarTower.algebraMap_eq R R₁ R₁₂).symm.trans (IsScalarTower.algebraMap_eq R R₂ R₁₂)
end CommSq

section Sections
variable (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁] [Module R M₂]
  [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]

/-- The `R`-module of sections `{(m₁, m₂) ∈ M₁ × M₂ | ψ₁(1 ⊗ m₁) = ψ₂(1 ⊗ m₂)}` of `D`. -/
def GlueingDatum.sections (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : Submodule R (M₁ × M₂) where
  carrier := {x | D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2)}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, tmul_add, map_add] at hx hy ⊢
    rw [hx, hy]
  zero_mem' := by simp
  smul_mem' r x hx := by
    simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd] at hx ⊢
    rw [← algebraMap_smul R₁ r x.1, ← algebraMap_smul R₂ r x.2, tmul_smul, tmul_smul,
      ← algebraMap_smul R₁₂ (algebraMap R R₁ r), ← algebraMap_smul R₁₂ (algebraMap R R₂ r),
      map_smul, map_smul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hx]

/-- The `R`-linear difference map `(m₁, m₂) ↦ ψ₁ (1 ⊗ m₁) - ψ₂ (1 ⊗ m₂)` out of `M₁ × M₂`. -/
def GlueingDatum.diff (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] : M₁ × M₂ →ₗ[R] M₁₂ where
  toFun x := D.ψ₁ (1 ⊗ₜ x.1) - D.ψ₂ (1 ⊗ₜ x.2)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, tmul_add, map_add]; abel
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    rw [← algebraMap_smul R₁ r x.1, ← algebraMap_smul R₂ r x.2, tmul_smul, tmul_smul,
      ← algebraMap_smul R₁₂ (algebraMap R R₁ r), ← algebraMap_smul R₁₂ (algebraMap R R₂ r),
      map_smul, map_smul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      algebraMap_smul, algebraMap_smul, smul_sub]

/-- First projection from the module of sections to `M₁`. -/
def GlueingDatum.fst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₁ :=
  (LinearMap.fst R M₁ M₂).comp (D.sections R).subtype
/-- Second projection from the module of sections to `M₂`. -/
def GlueingDatum.snd (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R →ₗ[R] M₂ :=
  (LinearMap.snd R M₁ M₂).comp (D.sections R).subtype
/-- Universal property of `D.sections R`: lift of compatible `f₁`, `f₂`. -/
def GlueingDatum.lift {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] [Module R M₁]
    [Module R M₂] [IsScalarTower R R₁ M₁] [IsScalarTower R R₂ M₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {N : Type*} [AddCommMonoid N] [Module R N]
    (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂) (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    N →ₗ[R] D.sections R := (f₁.prod f₂).codRestrict (D.sections R) h
/-- First base-changed projection `R₁ ⊗[R] D.sections R →ₗ[R₁] M₁`, induced by `D.fst R`. -/
noncomputable def GlueingDatum.baseChangeFst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    R₁ ⊗[R] D.sections R →ₗ[R₁] M₁ := (D.fst R).liftBaseChange R₁
/-- Second base-changed projection `R₂ ⊗[R] D.sections R →ₗ[R₂] M₂`, induced by `D.snd R`. -/
noncomputable def GlueingDatum.baseChangeSnd (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    R₂ ⊗[R] D.sections R →ₗ[R₂] M₂ := (D.snd R).liftBaseChange R₂
/-- Over a subsingleton overlap `M₁₂`, `D.sections R` identifies with `M₁ × M₂`. -/
def GlueingDatum.sectionsEquivProdOfSubsingleton [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) : D.sections R ≃ₗ[R] M₁ × M₂ :=
  LinearEquiv.ofTop (D.sections R) (Submodule.eq_top_iff'.mpr fun _ ↦ Subsingleton.elim _ _)
/-- Swapping the two pieces gives `D.sections R ≃ₗ[R] D.symm.sections R`. -/
def GlueingDatum.sectionsEquivSymm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.sections R ≃ₗ[R] D.symm.sections R where
  toFun x := ⟨(x.val.2, x.val.1), x.property.symm⟩
  invFun x := ⟨(x.val.2, x.val.1), x.property.symm⟩
  map_add' _ _ := rfl; map_smul' _ _ := rfl; left_inv _ := rfl; right_inv _ := rfl

section Simps
variable {R}
@[simp] theorem GlueingDatum.mem_sections_iff (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    {x : M₁ × M₂} : x ∈ D.sections R ↔ D.ψ₁ (1 ⊗ₜ x.1) = D.ψ₂ (1 ⊗ₜ x.2) := by rfl
@[simp] theorem GlueingDatum.diff_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] (x : M₁ × M₂) :
    D.diff R x = D.ψ₁ (1 ⊗ₜ x.1) - D.ψ₂ (1 ⊗ₜ x.2) := by rfl
/-- The sections submodule is the kernel of the difference map `D.diff R`. -/
theorem GlueingDatum.sections_eq_ker (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    [Module R M₁₂] [IsScalarTower R R₁₂ M₁₂] :
    D.sections R = LinearMap.ker (D.diff R) := by ext x; simp [sub_eq_zero]
@[simp] theorem GlueingDatum.fst_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.fst R x = x.val.1 := by rfl
@[simp] theorem GlueingDatum.snd_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.snd R x = x.val.2 := by rfl
@[simp] theorem GlueingDatum.coe_lift_apply {N : Type*} [AddCommMonoid N] [Module R N]
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
@[simp] theorem GlueingDatum.fst_comp_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    (D.fst R).comp (D.lift f₁ f₂ h) = f₁ := by ext n; rfl
@[simp] theorem GlueingDatum.snd_comp_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (f₁ : N →ₗ[R] M₁) (f₂ : N →ₗ[R] M₂)
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) :
    (D.snd R).comp (D.lift f₁ f₂ h) = f₂ := by ext n; rfl
/-- Two `R`-linear maps into `D.sections R` agree if their compositions with `fst` and `snd` do. -/
@[ext] theorem GlueingDatum.sections_hom_ext {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {g₁ g₂ : N →ₗ[R] D.sections R}
    (h₁ : (D.fst R).comp g₁ = (D.fst R).comp g₂)
    (h₂ : (D.snd R).comp g₁ = (D.snd R).comp g₂) : g₁ = g₂ := by
  ext n <;> [exact LinearMap.congr_fun h₁ n; exact LinearMap.congr_fun h₂ n]
/-- Uniqueness of the universal lift `D.lift f₁ f₂ h`. -/
theorem GlueingDatum.eq_lift {N : Type*} [AddCommMonoid N] [Module R N]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) {f₁ : N →ₗ[R] M₁} {f₂ : N →ₗ[R] M₂}
    (h : ∀ n, D.ψ₁ (1 ⊗ₜ f₁ n) = D.ψ₂ (1 ⊗ₜ f₂ n)) {g : N →ₗ[R] D.sections R}
    (h₁ : (D.fst R).comp g = f₁) (h₂ : (D.snd R).comp g = f₂) : g = D.lift f₁ f₂ h :=
  D.sections_hom_ext (h₁.trans (D.fst_comp_lift f₁ f₂ h).symm)
    (h₂.trans (D.snd_comp_lift f₁ f₂ h).symm)
@[simp] theorem GlueingDatum.baseChangeFst_tmul (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (r₁ : R₁) (x : D.sections R) : D.baseChangeFst R (r₁ ⊗ₜ x) = r₁ • D.fst R x := by rfl
@[simp] theorem GlueingDatum.baseChangeSnd_tmul (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (r₂ : R₂) (x : D.sections R) : D.baseChangeSnd R (r₂ ⊗ₜ x) = r₂ • D.snd R x := by rfl
/-- The defining overlap compatibility of the two projections of a section `x : D.sections R`. -/
theorem GlueingDatum.ψ₁_one_tmul_fst (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : D.ψ₁ (1 ⊗ₜ D.fst R x) = D.ψ₂ (1 ⊗ₜ D.snd R x) := x.property
@[simp] theorem GlueingDatum.sectionsEquivProdOfSubsingleton_apply [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    D.sectionsEquivProdOfSubsingleton R x = x.val := by rfl
@[simp] theorem GlueingDatum.coe_sectionsEquivProdOfSubsingleton_symm [Subsingleton M₁₂]
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : M₁ × M₂) :
    ((D.sectionsEquivProdOfSubsingleton R).symm x : M₁ × M₂) = x := by rfl
@[simp] theorem GlueingDatum.coe_sectionsEquivSymm_apply (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) :
    ((D.sectionsEquivSymm R x : D.symm.sections R) : M₂ × M₁) = (x.val.2, x.val.1) := by rfl
@[simp] theorem GlueingDatum.coe_sectionsEquivSymm_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.symm.sections R) :
    (((D.sectionsEquivSymm R).symm x : D.sections R) : M₁ × M₂) = (x.val.2, x.val.1) := by rfl
theorem GlueingDatum.fst_sectionsEquivSymm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : D.symm.fst R (D.sectionsEquivSymm R x) = D.snd R x := by rfl
theorem GlueingDatum.snd_sectionsEquivSymm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : D.symm.snd R (D.sectionsEquivSymm R x) = D.fst R x := by rfl
theorem GlueingDatum.fst_sectionsEquivSymm_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.symm.sections R) : D.fst R ((D.sectionsEquivSymm R).symm x) = D.symm.snd R x := by rfl
theorem GlueingDatum.snd_sectionsEquivSymm_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.symm.sections R) : D.snd R ((D.sectionsEquivSymm R).symm x) = D.symm.fst R x := by rfl
@[simp] theorem GlueingDatum.fst_comp_sectionsEquivSymm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    (D.symm.fst R).comp (D.sectionsEquivSymm R).toLinearMap = D.snd R := by ext x; rfl
@[simp] theorem GlueingDatum.snd_comp_sectionsEquivSymm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    (D.symm.snd R).comp (D.sectionsEquivSymm R).toLinearMap = D.fst R := by ext x; rfl
@[simp] theorem GlueingDatum.fst_comp_sectionsEquivSymm_symm
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    (D.fst R).comp (D.sectionsEquivSymm R).symm.toLinearMap = D.symm.snd R := by ext x; rfl
@[simp] theorem GlueingDatum.snd_comp_sectionsEquivSymm_symm
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    (D.snd R).comp (D.sectionsEquivSymm R).symm.toLinearMap = D.symm.fst R := by ext x; rfl
end Simps

section PatchedModuleComparison
/-- Canonical `R`-linear equivalence identifying `D.sections R` with
`PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap`. -/
noncomputable def GlueingDatum.sectionsEquivPatchedModule (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) :
    D.sections R ≃ₗ[R]
      PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap where
  toFun x := ⟨x.val.1, x.val.2, by
    simp only [LinearEquiv.coe_coe, patchedTransition_tmul]
    rw [x.property, LinearEquiv.symm_apply_apply, balancedExtensionEquivTensorProduct_symm_tmul]⟩
  invFun x := ⟨(x.fst, x.snd), by
    have hx := congrArg (D.ψ₂ ∘ balancedExtensionEquivTensorProduct R₂ R₁₂ M₂) x.apply_one_tmul_fst
    simpa only [mem_sections_iff, Function.comp_apply, LinearEquiv.coe_coe,
      patchedTransition_tmul, LinearEquiv.apply_symm_apply,
      balancedExtensionEquivTensorProduct_tmul] using hx⟩
  map_add' _ _ := rfl; left_inv _ := rfl; right_inv _ := rfl
  map_smul' r x := PatchedModule.ext (algebraMap_smul R₁ r x.val.1).symm
    (algebraMap_smul R₂ r x.val.2).symm

@[simp] theorem GlueingDatum.fst_sectionsEquivPatchedModule_apply
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    (D.sectionsEquivPatchedModule R x).fst = x.val.1 := by rfl
@[simp] theorem GlueingDatum.snd_sectionsEquivPatchedModule_apply
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂) (x : D.sections R) :
    (D.sectionsEquivPatchedModule R x).snd = x.val.2 := by rfl
@[simp] theorem GlueingDatum.coe_sectionsEquivPatchedModule_symm
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap) :
    (((D.sectionsEquivPatchedModule R).symm x : D.sections R) : M₁ × M₂) = (x.fst, x.snd) := by rfl
/-- `GlueingDatum.sectionsEquivPatchedModule` intertwines `D.fst` with `PatchedModule.fst`. -/
theorem GlueingDatum.fst_sectionsEquivPatchedModule (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : (D.sectionsEquivPatchedModule R x).fst = D.fst R x := by rfl
/-- `GlueingDatum.sectionsEquivPatchedModule` intertwines `D.snd` with `PatchedModule.snd`. -/
theorem GlueingDatum.snd_sectionsEquivPatchedModule (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : D.sections R) : (D.sectionsEquivPatchedModule R x).snd = D.snd R x := by rfl
/-- The inverse of `GlueingDatum.sectionsEquivPatchedModule` intertwines first projections. -/
theorem GlueingDatum.fst_sectionsEquivPatchedModule_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap) :
    D.fst R ((D.sectionsEquivPatchedModule R).symm x) = x.fst := by rfl
/-- The inverse of `GlueingDatum.sectionsEquivPatchedModule` intertwines second projections. -/
theorem GlueingDatum.snd_sectionsEquivPatchedModule_symm (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap) :
    D.snd R ((D.sectionsEquivPatchedModule R).symm x) = x.snd := by rfl
/-- `PatchedModule.compareFst` commutes with `D.baseChangeFst` along `sectionsEquivPatchedModule`
and `balancedExtensionEquivTensorProduct`. -/
theorem GlueingDatum.compareFst_sectionsEquivPatchedModule (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : R₁ ⊗[R] D.sections R) :
    PatchedModule.compareFst (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap
        ((balancedExtensionEquivTensorProduct R R₁ _).symm
          (AlgebraTensorModule.congr (LinearEquiv.refl R₁ R₁)
            (D.sectionsEquivPatchedModule R) x)) = D.baseChangeFst R x := by
  induction x using TensorProduct.inductionOn with
  | tmul _ _ => simp | add _ _ hx hy => simp only [map_add, hx, hy]
/-- `PatchedModule.compareSnd` commutes with `D.baseChangeSnd` along `sectionsEquivPatchedModule`
and `balancedExtensionEquivTensorProduct`. -/
theorem GlueingDatum.compareSnd_sectionsEquivPatchedModule (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : R₂ ⊗[R] D.sections R) :
    PatchedModule.compareSnd (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap
        ((balancedExtensionEquivTensorProduct R R₂ _).symm
          (AlgebraTensorModule.congr (LinearEquiv.refl R₂ R₂)
            (D.sectionsEquivPatchedModule R) x)) = D.baseChangeSnd R x := by
  induction x using TensorProduct.inductionOn with
  | tmul _ _ => simp | add _ _ hx hy => simp only [map_add, hx, hy]
/-- `D.baseChangeFst` commutes with `PatchedModule.compareFst` along
`balancedExtensionEquivTensorProduct` and `sectionsEquivPatchedModule.symm`. -/
theorem GlueingDatum.baseChangeFst_sectionsEquivPatchedModule_symm
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : BalancedExtension (algebraMap R R₁)
      (PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap)) :
    D.baseChangeFst R (AlgebraTensorModule.congr (LinearEquiv.refl R₁ R₁)
        (D.sectionsEquivPatchedModule R).symm (balancedExtensionEquivTensorProduct R R₁ _ x)) =
      PatchedModule.compareFst (GlueingDatum.commSq R R₁ R₂ R₁₂)
        D.patchedTransition.toLinearMap x := by
  induction x using BalancedExtension.induction_on with
  | tmul _ _ => simp | add _ _ hx hy => simp only [map_add, hx, hy]
/-- `D.baseChangeSnd` commutes with `PatchedModule.compareSnd` along
`balancedExtensionEquivTensorProduct` and `sectionsEquivPatchedModule.symm`. -/
theorem GlueingDatum.baseChangeSnd_sectionsEquivPatchedModule_symm
    (D : GlueingDatum R₁ R₂ R₁₂ M₁ M₂ M₁₂)
    (x : BalancedExtension (algebraMap R R₂)
      (PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) D.patchedTransition.toLinearMap)) :
    D.baseChangeSnd R (AlgebraTensorModule.congr (LinearEquiv.refl R₂ R₂)
        (D.sectionsEquivPatchedModule R).symm (balancedExtensionEquivTensorProduct R R₂ _ x)) =
      PatchedModule.compareSnd (GlueingDatum.commSq R R₁ R₂ R₁₂)
        D.patchedTransition.toLinearMap x := by
  induction x using BalancedExtension.induction_on with
  | tmul _ _ => simp | add _ _ hx hy => simp only [map_add, hx, hy]
end PatchedModuleComparison
end Sections

section OfModule

variable (R₁ R₂ R₁₂) in
/-- Canonical glueing datum `(R₁ ⊗_R N, R₂ ⊗_R N, R₁₂ ⊗_R N)` attached to an `R`-module `N`. -/
def GlueingDatum.ofModule (R : Type*) [CommRing R] [Algebra R R₁] [Algebra R R₂]
    [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
    (N : Type*) [AddCommGroup N] [Module R N] :
    GlueingDatum R₁ R₂ R₁₂ (R₁ ⊗[R] N) (R₂ ⊗[R] N) (R₁₂ ⊗[R] N) where
  ψ₁ := AlgebraTensorModule.cancelBaseChange R R₁ R₁₂ R₁₂ N
  ψ₂ := AlgebraTensorModule.cancelBaseChange R R₂ R₁₂ R₁₂ N

variable {R : Type*} [CommRing R] [Algebra R R₁] [Algebra R R₂] [Algebra R R₁₂]
  [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂] {N : Type*} [AddCommGroup N] [Module R N]

@[simp] theorem GlueingDatum.ofModule_ψ₁_tmul (r₁₂ : R₁₂) (r₁ : R₁) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (r₁₂ ⊗ₜ (r₁ ⊗ₜ n)) = (r₁ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₁ R₁₂ r₁₂ n r₁
@[simp] theorem GlueingDatum.ofModule_ψ₂_tmul (r₁₂ : R₁₂) (r₂ : R₂) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (r₁₂ ⊗ₜ (r₂ ⊗ₜ n)) = (r₂ • r₁₂) ⊗ₜ n :=
  AlgebraTensorModule.cancelBaseChange_tmul R R₂ R₁₂ r₁₂ n r₂
@[simp] theorem GlueingDatum.ofModule_ψ₂_symm_tmul (r₁₂ : R₁₂) (n : N) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂.symm (r₁₂ ⊗ₜ n) = r₁₂ ⊗ₜ ((1 : R₂) ⊗ₜ n) :=
  (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂.symm_apply_eq.mpr (by simp)

variable (R₁ R₂ R₁₂ R N) in
/-- Canonical `R`-linear map `n ↦ (1 ⊗ n, 1 ⊗ n)` into `(GlueingDatum.ofModule ...).sections R`. -/
def GlueingDatum.toSectionsOfModule :
    N →ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R where
  toFun n := ⟨((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n), by simp⟩
  map_add' _ _ := by ext <;> simp [tmul_add]
  map_smul' _ _ := by ext <;> simp [tmul_smul]

@[simp] theorem GlueingDatum.coe_toSectionsOfModule_apply (n : N) :
    (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) =
      ((1 : R₁) ⊗ₜ[R] n, (1 : R₂) ⊗ₜ[R] n) := by rfl

private theorem ofModule_patchedTransition_map
    (x : BalancedExtension (algebraMap R₁ R₁₂) (BalancedExtension (algebraMap R R₁) N)) :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).patchedTransition (BalancedExtension.map
        (algebraMap R₁ R₁₂) (balancedExtensionEquivTensorProduct R R₁ N).toLinearMap x) =
      BalancedExtension.map (algebraMap R₂ R₁₂)
        (balancedExtensionEquivTensorProduct R R₂ N).toLinearMap
        (BalancedExtension.commSqEquiv (GlueingDatum.commSq R R₁ R₂ R₁₂) N x) := by
  induction x using BalancedExtension.induction_on with
  | tmul r₁₂ z => induction z using BalancedExtension.induction_on with
    | tmul => simp [Algebra.smul_def, mul_comm r₁₂]
    | add _ _ h₁ h₂ => simp only [BalancedExtension.tmul_add, map_add, h₁, h₂]
  | add _ _ h₁ h₂ => simp only [map_add, h₁, h₂]
private theorem commSqEquiv_map_symm (x : BalancedExtension (algebraMap R₁ R₁₂) (R₁ ⊗[R] N)) :
    BalancedExtension.commSqEquiv (GlueingDatum.commSq R R₁ R₂ R₁₂) N (BalancedExtension.map
        (algebraMap R₁ R₁₂) (balancedExtensionEquivTensorProduct R R₁ N).symm.toLinearMap x) =
      BalancedExtension.map (algebraMap R₂ R₁₂)
        (balancedExtensionEquivTensorProduct R R₂ N).symm.toLinearMap
        ((GlueingDatum.ofModule R₁ R₂ R₁₂ R N).patchedTransition x) := by
  induction x using BalancedExtension.induction_on with
  | tmul r₁₂ z => induction z using TensorProduct.inductionOn with
    | tmul => simp [Algebra.smul_def, mul_comm r₁₂]
    | add _ _ h₁ h₂ => simp only [BalancedExtension.tmul_add, map_add, h₁, h₂]
  | add _ _ h₁ h₂ => simp only [map_add, h₁, h₂]

variable (R₁ R₂ R₁₂ R N) in
/-- Canonical `R`-linear equivalence identifying the sections of `GlueingDatum.ofModule` with
`PatchedModule` of the module `N`. -/
noncomputable def GlueingDatum.sectionsOfModuleEquivPatchedModule :
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R ≃ₗ[R]
      PatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂)
        (BalancedExtension.commSqEquiv (GlueingDatum.commSq R R₁ R₂ R₁₂) N).toLinearMap :=
  let hsq := GlueingDatum.commSq R R₁ R₂ R₁₂
  let e : PatchedModule hsq (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).patchedTransition.toLinearMap
      ≃ₗ[R] PatchedModule hsq (BalancedExtension.commSqEquiv hsq N).toLinearMap :=
    LinearEquiv.ofLinearMap
      (PatchedModule.map (balancedExtensionEquivTensorProduct R R₁ N).symm.toLinearMap
        (balancedExtensionEquivTensorProduct R R₂ N).symm.toLinearMap commSqEquiv_map_symm)
      (PatchedModule.map (balancedExtensionEquivTensorProduct R R₁ N).toLinearMap
        (balancedExtensionEquivTensorProduct R R₂ N).toLinearMap ofModule_patchedTransition_map)
      (LinearMap.ext fun _ ↦ PatchedModule.ext (by simp) (by simp))
      (LinearMap.ext fun _ ↦ PatchedModule.ext (by simp) (by simp))
  (GlueingDatum.sectionsEquivPatchedModule R _).trans e
/-- `GlueingDatum.sectionsOfModuleEquivPatchedModule` intertwines
`GlueingDatum.toSectionsOfModule` with `TauCeti.toPatchedModule`. -/
@[simp] theorem GlueingDatum.sectionsOfModuleEquivPatchedModule_toSectionsOfModule (n : N) :
    GlueingDatum.sectionsOfModuleEquivPatchedModule R₁ R₂ R₁₂ R N
        (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n) =
      toPatchedModule (GlueingDatum.commSq R R₁ R₂ R₁₂) N n :=
  PatchedModule.ext (by simp [sectionsOfModuleEquivPatchedModule])
    (by simp [sectionsOfModuleEquivPatchedModule])

private theorem ofModule_cocycle_eq_rTensor (z : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :
    LinearMap.rTensor N
      ((IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
        (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂))
      ((TensorProduct.prodLeft R R R₁ R₂ N).symm z) =
    (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₁ (1 ⊗ₜ z.1) -
      (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).ψ₂ (1 ⊗ₜ z.2) := by
  obtain ⟨w, rfl⟩ := (TensorProduct.prodLeft R R R₁ R₂ N).surjective z
  rw [LinearEquiv.symm_apply_apply]; induction w using TensorProduct.inductionOn with
  | tmul r _ => rcases r with ⟨_, _⟩; simp [Algebra.algebraMap_eq_smul_one]
  | add _ _ h₁ h₂ => simp only [map_add, Prod.fst_add, Prod.snd_add, tmul_add, h₁, h₂]; abel

omit [Algebra R R₁₂] [IsScalarTower R R₁ R₁₂] [IsScalarTower R R₂ R₁₂]
  [AddCommGroup N] [Module R N] in
/-- An exact ring diagram `0 → R → R₁ × R₂ → R₁₂` satisfies `TauCeti.patchedModuleEquiv`'s
fibre-product hypothesis. -/
theorem GlueingDatum.existsUnique_of_exact
    (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
      fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)
    {a₁ : R₁} {a₂ : R₂} (ha : algebraMap R₁ R₁₂ a₁ = algebraMap R₂ R₁₂ a₂) :
    ∃! r : R, algebraMap R R₁ r = a₁ ∧ algebraMap R R₂ r = a₂ := by
  obtain ⟨r, hr⟩ := (hexact (a₁, a₂)).mp (sub_eq_zero.mpr ha)
  exact ⟨r, Prod.ext_iff.mp hr, fun r' hr' ↦ hinj ((Prod.ext hr'.1 hr'.2).trans hr.symm)⟩

section Exact
variable (hinj : Function.Injective fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
  (hexact : Function.Exact (fun r : R ↦ (algebraMap R R₁ r, algebraMap R R₂ r))
    fun x : R₁ × R₂ ↦ algebraMap R₁ R₁₂ x.1 - algebraMap R₂ R₁₂ x.2)

section Flat
variable [Module.Flat R N]
include hinj hexact
/-- Whenever `0 → R → R₁ × R₂ → R₁₂` is exact and `N` is a flat `R`-module,
`GlueingDatum.toSectionsOfModule` is bijective. -/
theorem GlueingDatum.bijective_toSectionsOfModule_of_flat :
    Function.Bijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N) := by
  let ι : R →ₗ[R] R₁ × R₂ := (Algebra.linearMap R R₁).prod (Algebra.linearMap R R₂)
  let δ : (R₁ × R₂) →ₗ[R] R₁₂ :=
    (IsScalarTower.toAlgHom R R₁ R₁₂).toLinearMap.comp (LinearMap.fst R R₁ R₂) -
      (IsScalarTower.toAlgHom R R₂ R₁₂).toLinearMap.comp (LinearMap.snd R R₁ R₂)
  let e := TensorProduct.prodLeft R R R₁ R₂ N
  have hval (n : N) : e (ι.rTensor N ((TensorProduct.lid R N).symm n)) =
      (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) := by
    simp [e, ι]
  refine ⟨fun n₁ n₂ hn ↦ (TensorProduct.lid R N).symm.injective <|
      Module.Flat.rTensor_preserves_injective_linearMap ι hinj <| e.injective <| by
        simpa only [hval] using congrArg Subtype.val hn, fun ⟨z, hz⟩ ↦ ?_⟩
  obtain ⟨w, hw⟩ := (Module.Flat.rTensor_exact N (f := ι) (g := δ) hexact (e.symm z)).mp
    (by rw [ofModule_cocycle_eq_rTensor z, sub_eq_zero]; exact hz)
  exact ⟨TensorProduct.lid R N w, Subtype.ext <| by
    rw [← hval, LinearEquiv.symm_apply_apply, hw, LinearEquiv.apply_symm_apply]⟩
/-- For a flat `R`-module `N` over an exact ring diagram `0 → R → R₁ × R₂ → R₁₂`, the sections of
`GlueingDatum.ofModule R₁ R₂ R₁₂ R N` are canonically `R`-linearly isomorphic to `N`. -/
noncomputable def GlueingDatum.equivSectionsOfModule :
    N ≃ₗ[R] (GlueingDatum.ofModule R₁ R₂ R₁₂ R N).sections R :=
  LinearEquiv.ofBijective (GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N)
    (GlueingDatum.bijective_toSectionsOfModule_of_flat hinj hexact)
@[simp] theorem GlueingDatum.equivSectionsOfModule_apply (n : N) :
    GlueingDatum.equivSectionsOfModule hinj hexact n =
      GlueingDatum.toSectionsOfModule R₁ R₂ R₁₂ R N n := by rfl
end Flat
/-- For a finite projective `R`-module `N`, `GlueingDatum.sectionsOfModuleEquivPatchedModule`
intertwines `GlueingDatum.equivSectionsOfModule` with `TauCeti.patchedModuleEquiv`. -/
theorem GlueingDatum.sectionsOfModuleEquivPatchedModule_equivSectionsOfModule
    [Module.Finite R N] [Module.Projective R N] (n : N) :
    GlueingDatum.sectionsOfModuleEquivPatchedModule R₁ R₂ R₁₂ R N
        (GlueingDatum.equivSectionsOfModule hinj hexact n) =
      patchedModuleEquiv (GlueingDatum.commSq R R₁ R₂ R₁₂)
        (fun _ _ ha ↦ GlueingDatum.existsUnique_of_exact hinj hexact ha) N n := by
  rw [patchedModuleEquiv_apply, equivSectionsOfModule_apply,
    sectionsOfModuleEquivPatchedModule_toSectionsOfModule]
end Exact
end OfModule
end GlueingDatum
end TauCeti
end
