/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Data.Int.Order.Units

/-!
# Multiplying the differentials of a cochain complex by signs

For a family of signs `ε : ℤ → ℤˣ`, `CochainComplex.scaleDifferential K ε` is the cochain complex
with the terms of `K` and the differential `ε i • d` out of degree `i`. Given signs `c : ℤ → ℤˣ`
with `c (i + 1) * ε i = c i`, multiplying the term of degree `k` by `c k` is an isomorphism
`K.scaleDifferential ε ≅ K` (`CochainComplex.scaleDifferentialIso`), natural in `K`.

The alternating differential `(-1)^(k+1) d` (`CochainComplex.alternatingDifferential`) and the
differential `(-1)^τ d` multiplied by a constant sign (`CochainComplex.signedDifferential`) are the
two instances used in Tau Ceti.

## Main definitions

* `CochainComplex.scaleDifferential K ε`: the terms of `K` with the differential `ε i • d`.
* `CochainComplex.scaleDifferentialIso K ε c hc`: the isomorphism `K.scaleDifferential ε ≅ K`,
  multiplication by `c k` in degree `k`.
* `CochainComplex.scaleDifferentialFunctor C ε` and `CochainComplex.scaleDifferentialNatIso`:
  the construction is functorial, and the comparison is natural.
-/

public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- The cochain complex with the terms of `K` and its differential out of degree `i` multiplied
by the sign `ε i`. -/
def scaleDifferential (K : CochainComplex C ℤ) (ε : ℤ → ℤˣ) : CochainComplex C ℤ where
  X := K.X
  d i j := (ε i : ℤ) • K.d i j
  shape i j hij := by simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- Multiplying the differentials by signs does not change the terms. -/
def scaleDifferentialXIso (K : CochainComplex C ℤ) (ε : ℤ → ℤˣ) (k : ℤ) :
    (K.scaleDifferential ε).X k ≅ K.X k :=
  Iso.refl _

/-- The differential of `K.scaleDifferential ε` out of degree `i` is `ε i` times that of `K`,
under the identifications of terms. -/
@[reassoc (attr := simp)]
theorem scaleDifferential_d (K : CochainComplex C ℤ) (ε : ℤ → ℤˣ) (i j : ℤ) :
    (K.scaleDifferential ε).d i j ≫ (K.scaleDifferentialXIso ε j).hom =
      (ε i : ℤ) • ((K.scaleDifferentialXIso ε i).hom ≫ K.d i j) := by
  dsimp only [scaleDifferentialXIso, scaleDifferential, Iso.refl_hom]
  simp only [Category.comp_id, Category.id_comp]
  -- The two sides use the `ℤ`-action on morphisms through different, defeq instance paths.
  rfl

/-- The differential of `K.scaleDifferential ε` out of degree `i` is `ε i` times that of `K`,
transported along the identifications of terms. -/
theorem scaleDifferential_d_eq (K : CochainComplex C ℤ) (ε : ℤ → ℤˣ) (i j : ℤ) :
    (K.scaleDifferential ε).d i j = (ε i : ℤ) •
      ((K.scaleDifferentialXIso ε i).hom ≫ K.d i j ≫ (K.scaleDifferentialXIso ε j).inv) := by
  rw [← cancel_mono (K.scaleDifferentialXIso ε j).hom]
  simp [Preadditive.zsmul_comp]

/-- The comparison of degree `k`: multiplication by `c k`. -/
private def scaleDifferentialIsoX (K : CochainComplex C ℤ) (ε c : ℤ → ℤˣ) (k : ℤ) :
    (K.scaleDifferential ε).X k ≅ K.X k where
  hom := (c k : ℤ) • (K.scaleDifferentialXIso ε k).hom
  inv := (c k : ℤ) • (K.scaleDifferentialXIso ε k).inv
  hom_inv_id := by
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self]
  inv_hom_id := by
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
      Int.units_mul_self]

/-- **The sign comparison.** If the signs `c` satisfy `c (i + 1) * ε i = c i`, multiplying the
term of degree `k` by `c k` is an isomorphism from `K.scaleDifferential ε` to `K`. -/
def scaleDifferentialIso (K : CochainComplex C ℤ) (ε c : ℤ → ℤˣ)
    (hc : ∀ i, c (i + 1) * ε i = c i) : K.scaleDifferential ε ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (K.scaleDifferentialIsoX ε c) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    rw [← cancel_epi (K.scaleDifferentialXIso ε i).inv]
    simp only [scaleDifferentialIsoX, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
      scaleDifferential_d, Iso.inv_hom_id_assoc, smul_smul, ← Units.val_mul, hc])

@[simp]
theorem scaleDifferentialIso_hom_f (K : CochainComplex C ℤ) (ε c : ℤ → ℤˣ)
    (hc : ∀ i, c (i + 1) * ε i = c i) (k : ℤ) :
    (K.scaleDifferentialIso ε c hc).hom.f k = (c k : ℤ) • (K.scaleDifferentialXIso ε k).hom :=
  (rfl)

@[simp]
theorem scaleDifferentialIso_inv_f (K : CochainComplex C ℤ) (ε c : ℤ → ℤˣ)
    (hc : ∀ i, c (i + 1) * ε i = c i) (k : ℤ) :
    (K.scaleDifferentialIso ε c hc).inv.f k = (c k : ℤ) • (K.scaleDifferentialXIso ε k).inv :=
  (rfl)

/-- A cochain map commutes with the scaled differentials, with the same components under the
identifications of terms. -/
def scaleDifferentialMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (ε : ℤ → ℤˣ) :
    K.scaleDifferential ε ⟶ L.scaleDifferential ε where
  f k := (K.scaleDifferentialXIso ε k).hom ≫ f.f k ≫ (L.scaleDifferentialXIso ε k).inv
  comm' i j _ := by
    rw [← cancel_mono (L.scaleDifferentialXIso ε j).hom]
    simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

@[simp]
theorem scaleDifferentialMap_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (ε : ℤ → ℤˣ) (k : ℤ) :
    (scaleDifferentialMap f ε).f k =
      (K.scaleDifferentialXIso ε k).hom ≫ f.f k ≫ (L.scaleDifferentialXIso ε k).inv := (rfl)

variable (C) in
/-- Multiplying differentials by signs is functorial. The functor body is exposed so that its
object types reduce in the component formulas; the complex itself remains opaque. -/
@[expose]
def scaleDifferentialFunctor (ε : ℤ → ℤˣ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.scaleDifferential ε
  map f := scaleDifferentialMap f ε
  map_id K := by ext k; simp
  map_comp f g := by ext k; simp

@[simp]
theorem scaleDifferentialFunctor_obj (ε : ℤ → ℤˣ) (K : CochainComplex C ℤ) :
    (scaleDifferentialFunctor C ε).obj K = K.scaleDifferential ε := (rfl)

@[simp]
theorem scaleDifferentialFunctor_map (ε : ℤ → ℤˣ) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (scaleDifferentialFunctor C ε).map f = scaleDifferentialMap f ε := (rfl)

/-- The sign comparison commutes with cochain maps. -/
@[reassoc (attr := simp)]
theorem scaleDifferentialMap_comp_scaleDifferentialIso_hom {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (ε c : ℤ → ℤˣ) (hc : ∀ i, c (i + 1) * ε i = c i) :
    scaleDifferentialMap f ε ≫ (L.scaleDifferentialIso ε c hc).hom =
      (K.scaleDifferentialIso ε c hc).hom ≫ f := by
  ext k
  simp [Preadditive.zsmul_comp, Preadditive.comp_zsmul]

variable (C) in
/-- The sign comparison is natural in the complex. -/
def scaleDifferentialNatIso (ε c : ℤ → ℤˣ) (hc : ∀ i, c (i + 1) * ε i = c i) :
    scaleDifferentialFunctor C ε ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K ↦ K.scaleDifferentialIso ε c hc)
    (fun f ↦ scaleDifferentialMap_comp_scaleDifferentialIso_hom f ε c hc)

@[simp]
theorem scaleDifferentialNatIso_hom_app (ε c : ℤ → ℤˣ) (hc : ∀ i, c (i + 1) * ε i = c i)
    (K : CochainComplex C ℤ) :
    (scaleDifferentialNatIso C ε c hc).hom.app K = (K.scaleDifferentialIso ε c hc).hom := (rfl)

@[simp]
theorem scaleDifferentialNatIso_inv_app (ε c : ℤ → ℤˣ) (hc : ∀ i, c (i + 1) * ε i = c i)
    (K : CochainComplex C ℤ) :
    (scaleDifferentialNatIso C ε c hc).inv.app K = (K.scaleDifferentialIso ε c hc).inv := (rfl)

end CochainComplex
