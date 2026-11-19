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
public import TauCeti.Algebra.Category.ModuleCat.Annihilated

/-!
# Serre classes of abelian groups

This file proves that abelian groups annihilated by some power of a fixed integer satisfy the
zero, subobject, quotient, and extension closure properties in Mathlib's Serre-class interface.
Such classes are used in Hurewicz theorems modulo a Serre class.

## Main definitions

* `AddCommGrpCat.isKilledBySomePower d`: the abelian groups annihilated by some power of `d`, as
  an object property of `AddCommGrpCat`, with its `IsSerreClass` instance.

## Main results

* `AddCommGrpCat.prop_inverseImage_isKilledBySomePower_iff`: a `ℤ`-module lies in the class, read
  through the forgetful functor, exactly when some power of `d` annihilates every element.
* `AddCommGrpCat.isKilledBy_pow_le_inverseImage_isKilledBySomePower`: a `ℤ`-module killed by
  `d ^ n` lies in the class, read through the forgetful functor.

## References

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
  exists_zero := ⟨AddCommGrpCat.of PUnit, isZero_of_subsingleton _,
    (prop_isKilledBySomePower_iff _ _).2 ⟨0, fun _ ↦ Subsingleton.elim _ _⟩⟩
  prop_of_mono {M N} f hf hN := by
    obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d N).1 hN
    exact (prop_isKilledBySomePower_iff d M).2
      ⟨n, fun x ↦ (AddCommGrpCat.mono_iff_injective f).1 hf (by simp [hn])⟩
  prop_of_epi {M N} f hf hM := by
    obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d M).1 hM
    refine (prop_isKilledBySomePower_iff d N).2 ⟨n, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := (AddCommGrpCat.epi_iff_surjective f).1 hf y
    rw [← map_zsmul, hn, map_zero]
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨m, hm⟩ := (prop_isKilledBySomePower_iff d _).1 h₁
    obtain ⟨n, hn⟩ := (prop_isKilledBySomePower_iff d _).1 h₃
    refine (prop_isKilledBySomePower_iff d _).2 ⟨m + n, fun x₂ ↦ ?_⟩
    -- `d ^ n • x₂` lies in the kernel of `S.g`, hence comes from some `x₁ : S.X₁`.
    obtain ⟨x₁, hx₁⟩ :=
      (ShortComplex.ab_exact_iff S).1 hS.exact ((d : ℤ) ^ n • x₂) (by simp [hn])
    rw [pow_add, mul_smul, ← hx₁, ← map_zsmul, hm, map_zero]

/-- A `ℤ`-module lies in the inverse image of `isKilledBySomePower d` along the forgetful functor to
abelian groups exactly when some power of `d` annihilates every element. -/
theorem prop_inverseImage_isKilledBySomePower_iff (d : ℕ) (M : ModuleCat.{u} ℤ) :
    (isKilledBySomePower d).inverseImage (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat) M ↔
      ∃ n : ℕ, ∀ x : M, ((d : ℤ) ^ n) • x = 0 := by
  rw [ObjectProperty.prop_inverseImage_iff, prop_isKilledBySomePower_iff]
  -- The forgetful functor keeps the carrier and its additive group, and an integer acts on both
  -- sides through that additive group's `zsmul`.
  rfl

/-- A `ℤ`-module killed by `d ^ n`, in the sense of `CategoryTheory.ObjectProperty.isKilledBy`, is
annihilated by some power of `d` as an abelian group. -/
theorem isKilledBy_pow_le_inverseImage_isKilledBySomePower (d n : ℕ) :
    ObjectProperty.isKilledBy (ModuleCat.{u} ℤ) (d ^ n) ≤
      (isKilledBySomePower d).inverseImage (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat) :=
  fun M hM ↦ (prop_inverseImage_isKilledBySomePower_iff d M).2 ⟨n, fun x ↦ by
    rw [← Nat.cast_pow, natCast_zsmul]
    exact (ModuleCat.prop_isKilledBy_iff _ M).1 hM x⟩

end AddCommGrpCat
