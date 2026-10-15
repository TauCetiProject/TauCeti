/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Serre classes of abelian groups

This file proves that abelian groups annihilated by some power of a fixed integer satisfy the
zero, subobject, quotient, and extension closure properties in Mathlib's Serre-class interface.
Such classes are used in Hurewicz theorems modulo a Serre class.

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953).
-/

public section

universe u

open CategoryTheory Limits

namespace AddCommGrpCat

/-- The property of being annihilated by some power of `d`, viewed as an object property on
abelian groups. -/
def isKilledBySomePower (d : ℕ) : ObjectProperty AddCommGrpCat.{u} := fun M ↦
  ∃ n : ℕ, Module.IsTorsionBy ℤ M ((d : ℤ) ^ n)

/-- An abelian group belongs to `isKilledBySomePower d` exactly when one power of `d` annihilates
the whole group. -/
@[simp]
lemma prop_isKilledBySomePower_iff (d : ℕ) (M : AddCommGrpCat.{u}) :
    isKilledBySomePower d M ↔ ∃ n : ℕ, ∀ x : M, ((d : ℤ) ^ n) • x = 0 := Iff.rfl

/-- For fixed `d`, abelian groups annihilated by some power of `d` satisfy the closure properties
of a Serre class in an abelian category. -/
instance (d : ℕ) : (isKilledBySomePower d).IsSerreClass where
  exists_zero := by
    refine ⟨AddCommGrpCat.of PUnit, AddCommGrpCat.isZero_of_subsingleton _, ?_⟩
    rw [prop_isKilledBySomePower_iff]
    refine ⟨1, fun x ↦ ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  prop_of_mono {M N} f hf hN := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    rw [prop_isKilledBySomePower_iff] at hN ⊢
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, fun x ↦ hf ?_⟩
    simp only [map_zsmul, hn, map_zero]
  prop_of_epi {M N} f hf hM := by
    rw [AddCommGrpCat.epi_iff_surjective] at hf
    rw [prop_isKilledBySomePower_iff] at hM ⊢
    obtain ⟨n, hn⟩ := hM
    refine ⟨n, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hf y
    rw [← map_zsmul, hn, map_zero]
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [prop_isKilledBySomePower_iff] at h₁ h₃ ⊢
    obtain ⟨m, hm⟩ := h₁
    obtain ⟨n, hn⟩ := h₃
    refine ⟨m + n, fun x₂ ↦ ?_⟩
    have hx₃ : S.g (((d : ℤ) ^ n) • x₂) = 0 := by
      simp only [map_zsmul, hn]
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.ab_exact_iff S).1 hS.exact
      (((d : ℤ) ^ n) • x₂) hx₃
    calc
      ((d : ℤ) ^ (m + n)) • x₂ = ((d : ℤ) ^ m) • (((d : ℤ) ^ n) • x₂) := by
        rw [pow_add, mul_smul]
      _ = ((d : ℤ) ^ m) • S.f x₁ := by rw [hx₁]
      _ = S.f (((d : ℤ) ^ m) • x₁) := by rw [← map_zsmul]
      _ = 0 := by rw [hm]; simp

end AddCommGrpCat
