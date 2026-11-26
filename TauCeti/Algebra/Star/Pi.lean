/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
import TauCeti.Algebra.Star.StarAlgHom

/-!
# `⋆`-algebra homomorphisms and equivalences on `Pi` types

Single-factor inclusions into dependent products of non-unital `⋆`-algebras and `⋆`-algebra
equivalences for products indexed by a `Unique` type:

* `NonUnitalStarAlgHom.single`: the single-coordinate inclusion `A i →⋆ₙₐ[R] ∀ j, A j` sending `x`
  to `Pi.single i x`.
* `StarAlgEquiv.funUnique`: the `⋆`-algebra equivalence `(ι → A) ≃⋆ₐ[R] A` for `[Unique ι]`, built
  from `AlgEquiv.funUnique`.
* `NonUnitalStarAlgHom.singleFunUnique`: the single-coordinate inclusion
  `(ι' → A i) →⋆ₙₐ[R] ∀ j, A j` from a `Unique`-indexed copy of factor `A i`.
* `NonUnitalStarAlgHom.funUniqueEquiv` and `StarAlgHom.funUniqueEquiv`: the equivalences
  `((ι → A) →⋆ₙₐ[R] (κ → B)) ≃ (A →⋆ₙₐ[R] B)` and `((ι → A) →⋆ₐ[R] (κ → B)) ≃ (A →⋆ₐ[R] B)` for
  `[Unique ι] [Unique κ]`, together with application, composition, injectivity, and unitary
  conjugacy transport lemmas.
-/

public section

namespace NonUnitalStarAlgHom

section Single

variable (R : Type*) {ι : Type*} [DecidableEq ι] (A : ι → Type*) [Monoid R]
  [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
  [∀ i, StarAddMonoid (A i)]

/-- The non-unital `⋆`-algebra homomorphism including a single factor `A i` into the dependent
product `∀ j, A j` as functions supported at `i`. -/
def single (i : ι) : A i →⋆ₙₐ[R] ∀ j, A j :=
  { AddMonoidHom.single A i, MulHom.single i with
    map_smul' := Pi.single_smul i
    map_star' := Pi.single_star i }

/-- Coercion of `NonUnitalStarAlgHom.single` to a function is `Pi.single`. -/
@[simp]
theorem coe_single (i : ι) : ⇑(single R A i) = Pi.single i :=
  (rfl)

/-- Applying `NonUnitalStarAlgHom.single` gives `Pi.single`. -/
theorem single_apply {R : Type*} {ι : Type*} [DecidableEq ι] {A : ι → Type*} [Monoid R]
    [∀ i, NonUnitalNonAssocSemiring (A i)] [∀ i, DistribMulAction R (A i)]
    [∀ i, StarAddMonoid (A i)] (i : ι) (x : A i) :
    single R A i x = Pi.single i x :=
  (rfl)

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at the same coordinate `i` gives the identity. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_single_same (i : ι) :
    (Pi.evalNonUnitalStarAlgHom R A i).comp (single R A i) = .id R (A i) :=
  ext <| Pi.single_eq_same i

/-- Evaluating `NonUnitalStarAlgHom.single R A i` at a distinct coordinate `j ≠ i` gives zero. -/
@[simp]
theorem evalNonUnitalStarAlgHom_comp_single_of_ne {i j : ι} (h : j ≠ i) :
    (Pi.evalNonUnitalStarAlgHom R A j).comp (single R A i) = 0 :=
  ext <| Pi.single_eq_of_ne h

end Single

end NonUnitalStarAlgHom

namespace StarAlgEquiv

section Unique

/-- Functions from a `Unique` type `ι` to `A` are `⋆`-algebra equivalent to `A`. -/
def funUnique (R ι A : Type*) [Unique ι] [CommSemiring R] [Semiring A] [Algebra R A] [Star A] :
    (ι → A) ≃⋆ₐ[R] A :=
  StarAlgEquiv.ofAlgEquiv (AlgEquiv.funUnique R ι A) fun _ ↦ by simp

/-- Applying `StarAlgEquiv.funUnique` evaluates at `default`. -/
@[simp low]
theorem funUnique_apply {R ι A : Type*} [Unique ι] [CommSemiring R] [Semiring A] [Algebra R A]
    [Star A] (f : ι → A) :
    funUnique R ι A f = f default := by
  rw [funUnique, StarAlgEquiv.ofAlgEquiv_apply, AlgEquiv.funUnique_apply, Equiv.funUnique_apply]

/-- Applying `(StarAlgEquiv.funUnique R ι A).symm a` at any index returns `a`. -/
@[simp low]
theorem funUnique_symm_apply {R ι A : Type*} [Unique ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [Star A] (a : A) (i : ι) :
    (funUnique R ι A).symm a i = a := by
  have h : (funUnique R ι A).symm a = fun _ ↦ a := by
    rw [symm_apply_eq, funUnique_apply]
  exact congrFun h i

end Unique

end StarAlgEquiv

namespace NonUnitalStarAlgHom

section FunUnique

/-- The single-coordinate inclusion `(ι' → A i) →⋆ₙₐ[R] ∀ j, A j` from a `Unique`-indexed copy of
factor `A i` into the dependent product `∀ j, A j`. -/
def singleFunUnique (R : Type*) {ι : Type*} (ι' : Type*) [DecidableEq ι] [Unique ι']
    (A : ι → Type*) [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [∀ i, StarAddMonoid (A i)] (i : ι) :
    (ι' → A i) →⋆ₙₐ[R] ∀ j, A j :=
  (single R A i).comp (StarAlgEquiv.funUnique R ι' (A i)).toNonUnitalStarAlgHom

/-- Applying `NonUnitalStarAlgHom.singleFunUnique` embeds `f default` at coordinate `i`. -/
@[simp]
theorem singleFunUnique_apply {R ι ι' : Type*} [DecidableEq ι] [Unique ι'] {A : ι → Type*}
    [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, StarAddMonoid (A i)]
    (i : ι) (f : ι' → A i) :
    singleFunUnique R ι' A i f = Pi.single i (f default) := by
  simp [singleFunUnique]

/-- Equivalence between non-unital `⋆`-algebra homomorphisms `(ι → A) →⋆ₙₐ[R] (κ → B)` on
`Unique`-indexed products and single-factor homomorphisms `A →⋆ₙₐ[R] B`. -/
def funUniqueEquiv (R ι κ A B : Type*) [Unique ι] [Unique κ] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] :
    ((ι → A) →⋆ₙₐ[R] (κ → B)) ≃ (A →⋆ₙₐ[R] B) :=
  StarAlgEquiv.arrowCongr' (StarAlgEquiv.funUnique R ι A) (StarAlgEquiv.funUnique R κ B)

variable {R ι κ μ A B C : Type*} [Unique ι] [Unique κ] [Unique μ] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Applying `NonUnitalStarAlgHom.funUniqueEquiv` evaluates on constant functions at `default`. -/
@[simp]
theorem funUniqueEquiv_apply (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) (a : A) :
    funUniqueEquiv R ι κ A B φ a = φ (fun _ ↦ a) default := by
  have h : (StarAlgEquiv.funUnique R ι A).symm a = fun _ ↦ a :=
    funext (StarAlgEquiv.funUnique_symm_apply a)
  simp [funUniqueEquiv, h]

/-- Applying `(NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B).symm` evaluates `φ` at `default`. -/
@[simp]
theorem funUniqueEquiv_symm_apply (φ : A →⋆ₙₐ[R] B) (x : ι → A) (j : κ) :
    (funUniqueEquiv R ι κ A B).symm φ x j = φ (x default) := by
  simp [funUniqueEquiv]

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves composition. -/
theorem funUniqueEquiv_comp (ψ : (κ → B) →⋆ₙₐ[R] (μ → C)) (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    funUniqueEquiv R ι μ A C (ψ.comp φ) =
      (funUniqueEquiv R κ μ B C ψ).comp (funUniqueEquiv R ι κ A B φ) := by
  simp only [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr'_comp _ (StarAlgEquiv.funUnique R κ B) _ φ ψ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves composition. -/
theorem funUniqueEquiv_symm_comp (ψ : B →⋆ₙₐ[R] C) (φ : A →⋆ₙₐ[R] B) :
    (funUniqueEquiv R ι μ A C).symm (ψ.comp φ) =
      ((funUniqueEquiv R κ μ B C).symm ψ).comp ((funUniqueEquiv R ι κ A B).symm φ) := by
  simp only [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.arrowCongr'_comp _ (StarAlgEquiv.funUnique R κ B).symm _ φ ψ

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_injective_iff (φ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    Function.Injective (funUniqueEquiv R ι κ A B φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr'_injective_iff _ _ φ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_symm_injective_iff (φ : A →⋆ₙₐ[R] B) :
    Function.Injective ((funUniqueEquiv R ι κ A B).symm φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.arrowCongr'_injective_iff _ _ φ

/-- `NonUnitalStarAlgHom.funUniqueEquiv` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : (ι → A) →⋆ₙₐ[R] (κ → B)) :
    (∃ u : unitary B, ∀ x, (u : B) * funUniqueEquiv R ι κ A B φ x * star (u : B) =
        funUniqueEquiv R ι κ A B ψ x) ↔
      ∃ u : unitary (κ → B), ∀ x, (u : κ → B) * φ x * star (u : κ → B) = ψ x := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff _ _ φ ψ

/-- `(NonUnitalStarAlgHom.funUniqueEquiv).symm` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_symm_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : A →⋆ₙₐ[R] B) :
    (∃ u : unitary (κ → B), ∀ x, (u : κ → B) * (funUniqueEquiv R ι κ A B).symm φ x *
        star (u : κ → B) = (funUniqueEquiv R ι κ A B).symm ψ x) ↔
      ∃ u : unitary B, ∀ x, (u : B) * φ x * star (u : B) = ψ x := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr']
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr'_iff _ _ φ ψ

end FunUnique

end NonUnitalStarAlgHom

namespace StarAlgHom

section FunUnique

/-- Equivalence between unital `⋆`-algebra homomorphisms `(ι → A) →⋆ₐ[R] (κ → B)` on
`Unique`-indexed products and single-factor homomorphisms `A →⋆ₐ[R] B`. -/
def funUniqueEquiv (R ι κ A B : Type*) [Unique ι] [Unique κ] [CommSemiring R]
    [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B] :
    ((ι → A) →⋆ₐ[R] (κ → B)) ≃ (A →⋆ₐ[R] B) :=
  StarAlgEquiv.arrowCongr (StarAlgEquiv.funUnique R ι A) (StarAlgEquiv.funUnique R κ B)

variable {R ι κ μ A B C : Type*} [Unique ι] [Unique κ] [Unique μ] [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A] [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Forgetting unitality intertwines `StarAlgHom.funUniqueEquiv` with
`NonUnitalStarAlgHom.funUniqueEquiv`. -/
@[simp]
theorem toNonUnitalStarAlgHom_funUniqueEquiv (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    (funUniqueEquiv R ι κ A B φ).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B φ.toNonUnitalStarAlgHom := by
  rw [funUniqueEquiv, NonUnitalStarAlgHom.funUniqueEquiv,
    StarAlgEquiv.toNonUnitalStarAlgHom_arrowCongr]

/-- Forgetting unitality intertwines `(StarAlgHom.funUniqueEquiv).symm` with
`(NonUnitalStarAlgHom.funUniqueEquiv).symm`. -/
@[simp]
theorem toNonUnitalStarAlgHom_funUniqueEquiv_symm (φ : A →⋆ₐ[R] B) :
    ((funUniqueEquiv R ι κ A B).symm φ).toNonUnitalStarAlgHom =
      (NonUnitalStarAlgHom.funUniqueEquiv R ι κ A B).symm φ.toNonUnitalStarAlgHom := by
  rw [funUniqueEquiv, NonUnitalStarAlgHom.funUniqueEquiv, StarAlgEquiv.symm_arrowCongr,
    StarAlgEquiv.symm_arrowCongr', StarAlgEquiv.toNonUnitalStarAlgHom_arrowCongr]

/-- Applying `StarAlgHom.funUniqueEquiv` evaluates on constant functions at `default`. -/
@[simp]
theorem funUniqueEquiv_apply (φ : (ι → A) →⋆ₐ[R] (κ → B)) (a : A) :
    funUniqueEquiv R ι κ A B φ a = φ (fun _ ↦ a) default := by
  rw [← coe_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_funUniqueEquiv,
    NonUnitalStarAlgHom.funUniqueEquiv_apply, coe_toNonUnitalStarAlgHom]

/-- Applying `(StarAlgHom.funUniqueEquiv R ι κ A B).symm` evaluates `φ` at `default`. -/
@[simp]
theorem funUniqueEquiv_symm_apply (φ : A →⋆ₐ[R] B) (x : ι → A) (j : κ) :
    (funUniqueEquiv R ι κ A B).symm φ x j = φ (x default) := by
  rw [← coe_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_funUniqueEquiv_symm,
    NonUnitalStarAlgHom.funUniqueEquiv_symm_apply, coe_toNonUnitalStarAlgHom]

/-- `StarAlgHom.funUniqueEquiv` preserves composition. -/
theorem funUniqueEquiv_comp (ψ : (κ → B) →⋆ₐ[R] (μ → C)) (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    funUniqueEquiv R ι μ A C (ψ.comp φ) =
      (funUniqueEquiv R κ μ B C ψ).comp (funUniqueEquiv R ι κ A B φ) := by
  simp only [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr_comp _ (StarAlgEquiv.funUnique R κ B) _ φ ψ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves composition. -/
theorem funUniqueEquiv_symm_comp (ψ : B →⋆ₐ[R] C) (φ : A →⋆ₐ[R] B) :
    (funUniqueEquiv R ι μ A C).symm (ψ.comp φ) =
      ((funUniqueEquiv R κ μ B C).symm ψ).comp ((funUniqueEquiv R ι κ A B).symm φ) := by
  simp only [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.arrowCongr_comp _ (StarAlgEquiv.funUnique R κ B).symm _ φ ψ

/-- `StarAlgHom.funUniqueEquiv` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_injective_iff (φ : (ι → A) →⋆ₐ[R] (κ → B)) :
    Function.Injective (funUniqueEquiv R ι κ A B φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.arrowCongr_injective_iff _ _ φ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves injectivity. -/
@[simp]
theorem funUniqueEquiv_symm_injective_iff (φ : A →⋆ₐ[R] B) :
    Function.Injective ((funUniqueEquiv R ι κ A B).symm φ) ↔ Function.Injective φ := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.arrowCongr_injective_iff _ _ φ

/-- `StarAlgHom.funUniqueEquiv` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : (ι → A) →⋆ₐ[R] (κ → B)) :
    (∃ u : unitary B, ∀ x, (u : B) * funUniqueEquiv R ι κ A B φ x * star (u : B) =
        funUniqueEquiv R ι κ A B ψ x) ↔
      ∃ u : unitary (κ → B), ∀ x, (u : κ → B) * φ x * star (u : κ → B) = ψ x := by
  rw [funUniqueEquiv]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr_iff _ _ φ ψ

/-- `(StarAlgHom.funUniqueEquiv).symm` preserves unitary conjugacy in the target. -/
theorem exists_unitary_conj_funUniqueEquiv_symm_iff {B : Type*} [Semiring B] [Algebra R B]
    [StarMul B] (φ ψ : A →⋆ₐ[R] B) :
    (∃ u : unitary (κ → B), ∀ x, (u : κ → B) * (funUniqueEquiv R ι κ A B).symm φ x *
        star (u : κ → B) = (funUniqueEquiv R ι κ A B).symm ψ x) ↔
      ∃ u : unitary B, ∀ x, (u : B) * φ x * star (u : B) = ψ x := by
  rw [funUniqueEquiv, StarAlgEquiv.symm_arrowCongr]
  exact StarAlgEquiv.exists_unitary_conj_arrowCongr_iff _ _ φ ψ

end FunUnique

end StarAlgHom
