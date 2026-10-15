/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import TauCeti.LinearAlgebra.Graded.ExtendByZero
public import TauCeti.LinearAlgebra.Graded.LinearMap
import TauCeti.Algebra.DirectSum.Internal

/-!
# The direct-sum module of a nonnegative cochain complex

The terms of a cochain complex form one module by external direct sum. Its differential sends
the degree-`n` inclusion to the degree-`n + 1` inclusion of the original differential. This gives
a square-zero endomorphism of degree one, with zero homogeneous pieces in negative degrees.
The construction lets finite tensor products of complexes use a differential on one carrier.

The universal-property and componentwise map constructions are Mathlib's `DirectSum.toModule`
and `DirectSum.lmap`. No exactness or decomposition assumption is required. The inclusion
equations accept the caller's decision procedure for equality on natural numbers; the
constructions themselves do not depend on that choice.
-/

public section

open CategoryTheory
open scoped DirectSum

namespace CochainComplex

universe u v

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℕ)

/-- The external direct sum of the terms of a nonnegative cochain complex. -/
abbrev directSumModule := ⨁ n, K.X n

/-- The endomorphism which applies the differential and raises the summand index by one. -/
def directSumDifferential : K.directSumModule →ₗ[R] K.directSumModule :=
  DirectSum.toModule R ℕ _ fun n ↦
    (DirectSum.lof R ℕ (fun n ↦ K.X n) (n + 1)).comp (K.d n (n + 1)).hom

/-- The total differential on an included term is the included original differential. -/
@[simp]
theorem directSumDifferential_lof [h : DecidableEq ℕ] (n : ℕ) (x : K.X n) :
    K.directSumDifferential (DirectSum.lof R ℕ (fun n ↦ K.X n) n x) =
      DirectSum.lof R ℕ (fun n ↦ K.X n) (n + 1) ((K.d n (n + 1)).hom x) := by
  cases Subsingleton.elim h Nat.decEq
  simp [directSumDifferential]

/-- The total differential squares to zero. -/
theorem directSumDifferential_sq (x : K.directSumModule) :
    K.directSumDifferential (K.directSumDifferential x) = 0 := by
  have h : K.directSumDifferential.comp K.directSumDifferential = 0 := by
    apply DirectSum.linearMap_ext R
    intro n
    ext x
    simp only [LinearMap.comp_apply, directSumDifferential_lof]
    have hd := congrArg (fun f ↦ f x) (K.d_comp_d n (n + 1) (n + 1 + 1))
    simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hd
    simp [hd]
  exact DFunLike.congr_fun h x

/-- The homogeneous pieces of the total module, extended by zero in negative degrees. -/
def directSumPiece : ℤ → Submodule R K.directSumModule :=
  TauCeti.Graded.extendByZero fun n ↦
    LinearMap.range (DirectSum.lof R ℕ (fun n ↦ K.X n) n)

/-- The homogeneous pieces decompose the total module as an internal direct sum. -/
theorem isInternal_directSumPiece : DirectSum.IsInternal K.directSumPiece := by
  apply TauCeti.Graded.isInternal_extendByZero
  refine TauCeti.DirectSum.isInternal_of_lof
    (e := fun n ↦ LinearEquiv.ofInjective
      (DirectSum.lof R ℕ (fun n ↦ K.X n) n) (DirectSum.of_injective n))
    (E := LinearEquiv.refl R K.directSumModule) ?_
  intro n x
  rfl

/-- A nonnegative homogeneous piece is the range of the corresponding inclusion. -/
@[simp]
theorem directSumPiece_natCast [h : DecidableEq ℕ] (n : ℕ) :
    K.directSumPiece n = LinearMap.range (DirectSum.lof R ℕ (fun n ↦ K.X n) n) := by
  cases Subsingleton.elim h Nat.decEq
  simp [directSumPiece]

/-- Negative homogeneous pieces vanish. -/
theorem directSumPiece_of_neg {p : ℤ} (hp : p < 0) : K.directSumPiece p = ⊥ :=
  TauCeti.Graded.extendByZero_of_neg _ hp

/-- Every included term is homogeneous in its summand degree. -/
theorem lof_mem_directSumPiece [DecidableEq ℕ] (n : ℕ) (x : K.X n) :
    DirectSum.lof R ℕ (fun n ↦ K.X n) n x ∈ K.directSumPiece n := by
  rw [directSumPiece_natCast]
  exact ⟨x, rfl⟩

/-- The total differential is homogeneous of degree one. -/
theorem isHomogeneous_directSumDifferential :
    TauCeti.LinearMap.IsHomogeneous K.directSumDifferential K.directSumPiece
      K.directSumPiece 1 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rcases lt_or_ge p 0 with hp | hp
  · rw [K.directSumPiece_of_neg hp, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [directSumPiece_natCast] at hx
    obtain ⟨y, rfl⟩ := hx
    simpa only [Nat.cast_add, Nat.cast_one, directSumDifferential_lof] using
      K.lof_mem_directSumPiece (n + 1) ((K.d n (n + 1)).hom y)

variable {K} {L : CochainComplex (ModuleCat.{v} R) ℕ}

/-- The componentwise map of total modules induced by a cochain morphism. -/
def directSumMap (f : K ⟶ L) : K.directSumModule →ₗ[R] L.directSumModule :=
  DirectSum.lmap fun n ↦ (f.f n).hom

/-- On an included term the total map is the component of the cochain morphism. -/
@[simp]
theorem directSumMap_lof [DecidableEq ℕ] (f : K ⟶ L) (n : ℕ) (x : K.X n) :
    directSumMap f (DirectSum.lof R ℕ (fun n ↦ K.X n) n x) =
      DirectSum.lof R ℕ (fun n ↦ L.X n) n ((f.f n).hom x) := by
  simp [directSumMap]

/-- Taking the total map preserves identity morphisms. -/
@[simp]
theorem directSumMap_id : directSumMap (𝟙 K) = LinearMap.id := by
  simp [directSumMap]

/-- Taking the total map preserves composition. -/
@[simp]
theorem directSumMap_comp {N : CochainComplex (ModuleCat.{v} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ N) :
    directSumMap (f ≫ g) = (directSumMap g).comp (directSumMap f) := by
  simp [directSumMap, DirectSum.lmap_comp]

/-- A total map commutes with the total differentials. -/
theorem directSumMap_differential (f : K ⟶ L) (x : K.directSumModule) :
    directSumMap f (K.directSumDifferential x) =
      L.directSumDifferential (directSumMap f x) := by
  have h : (directSumMap f).comp K.directSumDifferential =
      L.directSumDifferential.comp (directSumMap f) := by
    apply DirectSum.linearMap_ext R
    intro n
    ext x
    simp only [LinearMap.comp_apply, directSumDifferential_lof, directSumMap_lof]
    have hf := congrArg (fun g ↦ g x) (f.comm n (n + 1))
    simp only [ModuleCat.comp_apply] at hf
    rw [hf]
  exact DFunLike.congr_fun h x

/-- A cochain morphism preserves the homogeneous pieces in the total module. -/
theorem isHomogeneous_directSumMap (f : K ⟶ L) :
    TauCeti.LinearMap.IsHomogeneous (directSumMap f) K.directSumPiece L.directSumPiece 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  simp only [add_zero]
  rcases lt_or_ge p 0 with hp | hp
  · rw [K.directSumPiece_of_neg hp, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [directSumPiece_natCast] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨_, (directSumMap_lof f n y).symm⟩

end CochainComplex
