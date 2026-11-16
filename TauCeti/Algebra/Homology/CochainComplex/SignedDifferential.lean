/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Data.ZMod.IntUnitsPower
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

/-!
# Multiplying the differential of a cochain complex by a sign

For `τ : ZMod 2`, `CochainComplex.signedDifferential K τ` is the cochain complex with the terms
of `K` and the differential `(-1)^τ d`. The sign is Mathlib's power `(-1 : ℤˣ) ^ τ` of a unit of
`ℤ` by an element of `ZMod 2`, so that it only depends on the parity `τ`. Multiplying the term of
degree `k` by `(-1)^(τ k)` is an isomorphism `K.signedDifferential τ ≅ K`
(`CochainComplex.signedDifferentialIso`), natural in `K`.

Such complexes appear in the super sign convention for tensor products of complexes whose terms
carry a parity independent of their degree: there the differential of the second factor of a
tensor product is multiplied by `(-1)^τ` when the first factor has independent parity `τ`, and the
isomorphism above is the comparison with the ordinary tensor product of complexes.

## Main definitions

* `CochainComplex.signedDifferential K τ`: the terms of `K` with the differential `(-1)^τ d`.
* `CochainComplex.signedDifferentialIso K τ`: the isomorphism `K.signedDifferential τ ≅ K`,
  multiplication by `(-1)^(τ k)` in degree `k`.
* `CochainComplex.signedDifferentialFunctor τ` and `CochainComplex.signedDifferentialNatIso τ`:
  the construction is functorial, and the comparison is natural.
-/

public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- The cochain complex with the terms of `K` and its differential multiplied by `(-1)^τ`. -/
def signedDifferential (K : CochainComplex C ℤ) (τ : ZMod 2) : CochainComplex C ℤ where
  X := K.X
  d i j := (((-1 : ℤˣ) ^ τ : ℤˣ) : ℤ) • K.d i j
  shape i j hij := by simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- Multiplying the differential by a sign does not change the terms. -/
def signedDifferentialXIso (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferential τ).X k ≅ K.X k :=
  Iso.refl _

/-- The differential of `K.signedDifferential τ` is `(-1)^τ` times that of `K`, under the
identifications of terms. -/
@[reassoc (attr := simp)]
theorem signedDifferential_d (K : CochainComplex C ℤ) (τ : ZMod 2) (i j : ℤ) :
    (K.signedDifferential τ).d i j ≫ (K.signedDifferentialXIso τ j).hom =
      (((-1 : ℤˣ) ^ τ : ℤˣ) : ℤ) • ((K.signedDifferentialXIso τ i).hom ≫ K.d i j) := by
  dsimp only [signedDifferentialXIso, signedDifferential, Iso.refl_hom]
  simp only [Category.comp_id, Category.id_comp]
  -- The two sides use the `ℤ`-action on morphisms through different, defeq instance paths.
  rfl

/-- The differential of `K.signedDifferential τ` is `(-1)^τ` times that of `K`, transported along
the identifications of terms. -/
theorem signedDifferential_d_eq (K : CochainComplex C ℤ) (τ : ZMod 2) (i j : ℤ) :
    (K.signedDifferential τ).d i j = (((-1 : ℤˣ) ^ τ : ℤˣ) : ℤ) •
      ((K.signedDifferentialXIso τ i).hom ≫ K.d i j ≫ (K.signedDifferentialXIso τ j).inv) := by
  rw [← cancel_mono (K.signedDifferentialXIso τ j).hom]
  simp [Preadditive.zsmul_comp]

/-- The comparison of degree `k`: multiplication by `(-1)^(τ k)`. -/
private def signedDifferentialIsoX (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferential τ).X k ≅ K.X k where
  hom := (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) • (K.signedDifferentialXIso τ k).hom
  inv := (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) • (K.signedDifferentialXIso τ k).inv
  hom_inv_id := by
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul]
  inv_hom_id := by
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul]

/-- The sign `(-1)^(τ k)` changes by `(-1)^τ` from degree `i` to degree `i + 1`. -/
private theorem uzpow_mul_intCast_add_one (τ : ZMod 2) (i : ℤ) :
    (-1 : ℤˣ) ^ (τ * ((i + 1 : ℤ) : ZMod 2)) * (-1 : ℤˣ) ^ τ = (-1 : ℤˣ) ^ (τ * i) := by
  rw [← uzpow_add]
  congr 1
  have h2 : (2 : ZMod 2) = 0 := rfl
  push_cast
  linear_combination τ * h2

/-- **The sign comparison.** Multiplying the term of degree `k` by `(-1)^(τ k)` is an isomorphism
from `K.signedDifferential τ` to `K`. -/
def signedDifferentialIso (K : CochainComplex C ℤ) (τ : ZMod 2) : K.signedDifferential τ ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (K.signedDifferentialIsoX τ) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [← cancel_epi (K.signedDifferentialXIso τ i).inv]
    simp only [signedDifferentialIsoX, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      signedDifferential_d, Iso.inv_hom_id_assoc, smul_smul, ← Units.val_mul,
      uzpow_mul_intCast_add_one])

@[simp]
theorem signedDifferentialIso_hom_f (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferentialIso τ).hom.f k =
      (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) • (K.signedDifferentialXIso τ k).hom := (rfl)

@[simp]
theorem signedDifferentialIso_inv_f (K : CochainComplex C ℤ) (τ : ZMod 2) (k : ℤ) :
    (K.signedDifferentialIso τ).inv.f k =
      (((-1 : ℤˣ) ^ (τ * k) : ℤˣ) : ℤ) • (K.signedDifferentialXIso τ k).inv := (rfl)

/-- A cochain map commutes with the signed differentials, with the same components under the
identifications of terms. -/
def signedDifferentialMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (τ : ZMod 2) :
    K.signedDifferential τ ⟶ L.signedDifferential τ where
  f k := (K.signedDifferentialXIso τ k).hom ≫ f.f k ≫ (L.signedDifferentialXIso τ k).inv
  comm' i j _ := by
    rw [← cancel_mono (L.signedDifferentialXIso τ j).hom]
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

@[simp]
theorem signedDifferentialMap_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (τ : ZMod 2) (k : ℤ) :
    (signedDifferentialMap f τ).f k =
      (K.signedDifferentialXIso τ k).hom ≫ f.f k ≫ (L.signedDifferentialXIso τ k).inv := (rfl)

variable (C) in
/-- Multiplying differentials by `(-1)^τ` is functorial. The functor body is exposed so that its
object types reduce in the component formulas; the complex itself remains opaque. -/
@[expose]
def signedDifferentialFunctor (τ : ZMod 2) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.signedDifferential τ
  map f := signedDifferentialMap f τ
  map_id K := by ext k; simp
  map_comp f g := by ext k; simp

@[simp]
theorem signedDifferentialFunctor_obj (τ : ZMod 2) (K : CochainComplex C ℤ) :
    (signedDifferentialFunctor C τ).obj K = K.signedDifferential τ := (rfl)

@[simp]
theorem signedDifferentialFunctor_map (τ : ZMod 2) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (signedDifferentialFunctor C τ).map f = signedDifferentialMap f τ := (rfl)

/-- The sign comparison commutes with cochain maps. -/
@[reassoc (attr := simp)]
theorem signedDifferentialMap_comp_signedDifferentialIso_hom {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (τ : ZMod 2) :
    signedDifferentialMap f τ ≫ (L.signedDifferentialIso τ).hom =
      (K.signedDifferentialIso τ).hom ≫ f := by
  ext k
  simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

variable (C) in
/-- The sign comparison is natural in the complex. -/
def signedDifferentialNatIso (τ : ZMod 2) : signedDifferentialFunctor C τ ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ K.signedDifferentialIso τ)
    (fun f ↦ signedDifferentialMap_comp_signedDifferentialIso_hom f τ)

@[simp]
theorem signedDifferentialNatIso_hom_app (τ : ZMod 2) (K : CochainComplex C ℤ) :
    (signedDifferentialNatIso C τ).hom.app K = (K.signedDifferentialIso τ).hom := (rfl)

@[simp]
theorem signedDifferentialNatIso_inv_app (τ : ZMod 2) (K : CochainComplex C ℤ) :
    (signedDifferentialNatIso C τ).inv.app K = (K.signedDifferentialIso τ).inv := (rfl)

end CochainComplex
