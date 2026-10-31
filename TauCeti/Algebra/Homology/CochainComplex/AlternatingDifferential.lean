/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.Ring

/-!
# Alternating differentials and the cap-product grading

For an integer-graded cochain complex, multiplying the differential out of degree `k` by
`(-1)^(k+1)` gives an isomorphic complex. The comparison multiplies degree `k` by
`(-1)^(k(k+1)/2)`, also in negative degrees. It is natural in cochain maps, so it can be
applied to inverse systems without changing their transition maps.

In particular, extend a nonnegative chain complex by zero using the degree map `j ↦ m-j`.
The resulting signed differential is the one for cap product with a fundamental cycle in the
front-face/back-face convention. The comparison here transports homological algebra between
signed and unsigned complexes; it does not insert a sign into the cap-product map itself.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.3, the cap-product boundary identity.
-/

public section

open CategoryTheory

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C]

/-- Multiply the differential out of integer degree `k` by `(-1)^(k+1)`, leaving the
objects unchanged. -/
def alternatingDifferential (K : CochainComplex C ℤ) : CochainComplex C ℤ where
  X := K.X
  d i j := ((i + 1).negOnePow : ℤ) • K.d i j
  shape i j hij := by simp [K.shape i j hij]
  d_comp_d' i j k _ _ := by simp

/-- The alternating differential does not change the objects. -/
def alternatingDifferentialXIso (K : CochainComplex C ℤ) (k : ℤ) :
    K.alternatingDifferential.X k ≅ K.X k := Iso.refl _

/-- The differential under the canonical identifications of objects. -/
@[reassoc (attr := simp)]
theorem alternatingDifferential_d (K : CochainComplex C ℤ) (i j : ℤ) :
    K.alternatingDifferential.d i j ≫ (K.alternatingDifferentialXIso j).hom =
      ((i + 1).negOnePow : ℤ) • ((K.alternatingDifferentialXIso i).hom ≫ K.d i j) := by
  dsimp [alternatingDifferentialXIso, alternatingDifferential]
  simp only [Category.comp_id, Category.id_comp]
  -- Compute the differential after removing the identity object identifications.
  rfl

/-- The alternating-differential comparison has degree-`k` component
`(-1)^(k(k+1)/2)`. No boundedness assumption is needed. -/
def alternatingDifferentialIso (K : CochainComplex C ℤ) : K ≅ K.alternatingDifferential :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦
      { hom := ((k * (k + 1) / 2).negOnePow : ℤ) • (K.alternatingDifferentialXIso k).inv
        inv := ((k * (k + 1) / 2).negOnePow : ℤ) • (K.alternatingDifferentialXIso k).hom
        hom_inv_id := by simp [smul_smul, ← Units.val_mul]
        inv_hom_id := by simp [smul_smul, ← Units.val_mul] }) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      have hexp : (i + 1) * (i + 1 + 1) / 2 = i * (i + 1) / 2 + (i + 1) := by
        have h : (i + 1) * (i + 1 + 1) = i * (i + 1) + (i + 1) * 2 := by ring
        rw [h, Int.add_mul_ediv_right _ _ (by decide)]
      apply (cancel_mono (K.alternatingDifferentialXIso (i + 1)).hom).1
      simp only [Preadditive.zsmul_comp, Category.assoc, alternatingDifferential_d,
        Preadditive.comp_zsmul, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, smul_smul, hexp, Int.negOnePow_add, Units.val_mul])

@[simp]
theorem alternatingDifferentialIso_hom_f (K : CochainComplex C ℤ) (k : ℤ) :
    K.alternatingDifferentialIso.hom.f k =
      ((k * (k + 1) / 2).negOnePow : ℤ) • (K.alternatingDifferentialXIso k).inv := (rfl)

@[simp]
theorem alternatingDifferentialIso_inv_f (K : CochainComplex C ℤ) (k : ℤ) :
    K.alternatingDifferentialIso.inv.f k =
      ((k * (k + 1) / 2).negOnePow : ℤ) • (K.alternatingDifferentialXIso k).hom := (rfl)

/-- A cochain map also commutes with the alternating differentials, with the same
components under the canonical identifications. -/
def alternatingDifferentialMap {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    K.alternatingDifferential ⟶ L.alternatingDifferential where
  f k := (K.alternatingDifferentialXIso k).hom ≫ f.f k ≫
    (L.alternatingDifferentialXIso k).inv
  comm' i j _ := by
    dsimp [alternatingDifferentialXIso, alternatingDifferential]
    simp [f.comm]

@[simp]
theorem alternatingDifferentialMap_f {K L : CochainComplex C ℤ} (f : K ⟶ L) (k : ℤ) :
    (alternatingDifferentialMap f).f k = (K.alternatingDifferentialXIso k).hom ≫
      f.f k ≫ (L.alternatingDifferentialXIso k).inv := (rfl)

/-- Alternating the differential is functorial, retaining the transition maps of any
system of complexes degreewise. The functor body is exposed so that its object types reduce
in the component formulas; the complex itself remains opaque. -/
@[expose]
def alternatingDifferentialFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := alternatingDifferential
  map := alternatingDifferentialMap
  map_id K := by ext k; simp
  map_comp f g := by ext k; simp

@[simp]
theorem alternatingDifferentialFunctor_obj (K : CochainComplex C ℤ) :
    alternatingDifferentialFunctor.obj K = K.alternatingDifferential := (rfl)

@[simp]
theorem alternatingDifferentialFunctor_map {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    alternatingDifferentialFunctor.map f = alternatingDifferentialMap f := (rfl)

/-- The signed/unsigned comparison is natural, so homology and limit comparisons may be
transported along it. -/
def alternatingDifferentialNatIso :
    𝟭 (CochainComplex C ℤ) ≅ alternatingDifferentialFunctor :=
  NatIso.ofComponents alternatingDifferentialIso (by
    intro K L f
    ext k
    simp [alternatingDifferentialFunctor])

@[simp]
theorem alternatingDifferentialNatIso_hom_app (K : CochainComplex C ℤ) :
    alternatingDifferentialNatIso.hom.app K = K.alternatingDifferentialIso.hom := (rfl)

@[simp]
theorem alternatingDifferentialNatIso_inv_app (K : CochainComplex C ℤ) :
    alternatingDifferentialNatIso.inv.app K = K.alternatingDifferentialIso.inv := (rfl)

end CochainComplex

namespace ChainComplex

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- Extend nonnegative chains by zero along `j ↦ m-j`, then give the resulting integer
cochain complex differential `(-1)^(k+1) ∂` in degree `k`. The functor body is exposed to
identify the object types in its map and comparison formulas. -/
@[expose]
noncomputable def capGradedFunctor (m : ℤ) : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
  (ComplexShape.embeddingUpIntLE m).extendFunctor C ⋙
    CochainComplex.alternatingDifferentialFunctor

@[simp]
theorem capGradedFunctor_obj (m : ℤ) (K : ChainComplex C ℕ) :
    (capGradedFunctor m).obj K =
      CochainComplex.alternatingDifferential
        (K.extend (ComplexShape.embeddingUpIntLE m)) := (rfl)

@[simp]
theorem capGradedFunctor_map (m : ℤ) {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    (capGradedFunctor m).map f = CochainComplex.alternatingDifferentialMap
      (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntLE m)) := (rfl)

/-- Natural comparison from the unsigned zero extension to the cap-product grading.
It multiplies degree `k` by `(-1)^(k(k+1)/2)` under the canonical object identifications. -/
noncomputable def capGradedNatIso (m : ℤ) :
    (ComplexShape.embeddingUpIntLE m).extendFunctor C ≅ capGradedFunctor (C := C) m :=
  NatIso.ofComponents
    (fun K ↦ CochainComplex.alternatingDifferentialIso
      (K.extend (ComplexShape.embeddingUpIntLE m)))
    (fun f ↦ CochainComplex.alternatingDifferentialNatIso.hom.naturality
      (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntLE m)))

@[simp]
theorem capGradedNatIso_hom_app (m : ℤ) (K : ChainComplex C ℕ) :
    (capGradedNatIso (C := C) m).hom.app K =
      (CochainComplex.alternatingDifferentialIso
        (K.extend (ComplexShape.embeddingUpIntLE m))).hom := (rfl)

@[simp]
theorem capGradedNatIso_inv_app (m : ℤ) (K : ChainComplex C ℕ) :
    (capGradedNatIso (C := C) m).inv.app K =
      (CochainComplex.alternatingDifferentialIso
        (K.extend (ComplexShape.embeddingUpIntLE m))).inv := (rfl)

end ChainComplex
