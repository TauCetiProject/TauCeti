/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import TauCeti.Algebra.Homology.CochainComplex.ScaleDifferential
public import TauCeti.Algebra.Ring.NegOnePow

/-!
# Alternating differentials and the cap-product grading

For an integer-graded cochain complex, multiplying the differential out of degree `k` by
`(-1)^(k+1)` gives an isomorphic complex, an instance of `CochainComplex.scaleDifferential`.
The comparison multiplies degree `k` by `(-1)^(k(k+1)/2)`, also in negative degrees. It is
natural in cochain maps, so it can be applied to inverse systems without changing their
transition maps.

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
objects unchanged. It is an abbreviation, so that the API of
`CochainComplex.scaleDifferential` applies to it. -/
abbrev alternatingDifferential (K : CochainComplex C ℤ) : CochainComplex C ℤ :=
  K.scaleDifferential fun i ↦ (i + 1).negOnePow

/-- The alternating-differential comparison has degree-`k` component
`(-1)^(k(k+1)/2)`. No boundedness assumption is needed. -/
def alternatingDifferentialIso (K : CochainComplex C ℤ) : K ≅ K.alternatingDifferential :=
  (K.scaleDifferentialIso _ (fun k ↦ (k * (k + 1) / 2).negOnePow)
    Int.negOnePow_mul_succ_div_two_succ_mul).symm

@[simp]
theorem alternatingDifferentialIso_hom_f (K : CochainComplex C ℤ) (k : ℤ) :
    K.alternatingDifferentialIso.hom.f k = ((k * (k + 1) / 2).negOnePow : ℤ) •
      (K.scaleDifferentialXIso (fun i ↦ (i + 1).negOnePow) k).inv := by
  simp [alternatingDifferentialIso]

@[simp]
theorem alternatingDifferentialIso_inv_f (K : CochainComplex C ℤ) (k : ℤ) :
    K.alternatingDifferentialIso.inv.f k = ((k * (k + 1) / 2).negOnePow : ℤ) •
      (K.scaleDifferentialXIso (fun i ↦ (i + 1).negOnePow) k).hom := by
  simp [alternatingDifferentialIso]

variable (C) in
/-- The signed/unsigned comparison is natural, so homology and limit comparisons may be
transported along it. -/
def alternatingDifferentialNatIso :
    𝟭 (CochainComplex C ℤ) ≅ scaleDifferentialFunctor C fun i ↦ (i + 1).negOnePow :=
  (scaleDifferentialNatIso C _ (fun k ↦ (k * (k + 1) / 2).negOnePow)
    Int.negOnePow_mul_succ_div_two_succ_mul).symm

@[simp]
theorem alternatingDifferentialNatIso_hom_app (K : CochainComplex C ℤ) :
    (alternatingDifferentialNatIso C).hom.app K = K.alternatingDifferentialIso.hom :=
  scaleDifferentialNatIso_inv_app _ _ _ K

@[simp]
theorem alternatingDifferentialNatIso_inv_app (K : CochainComplex C ℤ) :
    (alternatingDifferentialNatIso C).inv.app K = K.alternatingDifferentialIso.inv :=
  scaleDifferentialNatIso_hom_app _ _ _ K

end CochainComplex

namespace TauCeti

open CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- Extend nonnegative chains by zero along `j ↦ m-j`, then give the resulting integer
cochain complex differential `(-1)^(k+1) ∂` in degree `k`. The functor body is exposed to
identify the object types in its map and comparison formulas. -/
@[expose]
noncomputable def extendIntLEAlternatingDifferentialFunctor (m : ℤ) :
    ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
  (ComplexShape.embeddingUpIntLE m).extendFunctor C ⋙
    CochainComplex.scaleDifferentialFunctor C fun i ↦ (i + 1).negOnePow

@[simp]
theorem extendIntLEAlternatingDifferentialFunctor_obj (m : ℤ) (K : ChainComplex C ℕ) :
    (extendIntLEAlternatingDifferentialFunctor m).obj K =
      CochainComplex.alternatingDifferential
        (K.extend (ComplexShape.embeddingUpIntLE m)) := (rfl)

@[simp]
theorem extendIntLEAlternatingDifferentialFunctor_map (m : ℤ) {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    (extendIntLEAlternatingDifferentialFunctor m).map f = CochainComplex.scaleDifferentialMap
      (HomologicalComplex.extendMap f (ComplexShape.embeddingUpIntLE m))
      (fun i ↦ (i + 1).negOnePow) := (rfl)

/-- Natural comparison from the unsigned zero extension to its alternating differential.
It multiplies degree `k` by `(-1)^(k(k+1)/2)` under the canonical object identifications. -/
noncomputable def extendIntLEAlternatingDifferentialNatIso (m : ℤ) :
    (ComplexShape.embeddingUpIntLE m).extendFunctor C ≅
      extendIntLEAlternatingDifferentialFunctor (C := C) m :=
  Functor.isoWhiskerLeft ((ComplexShape.embeddingUpIntLE m).extendFunctor C)
    (CochainComplex.alternatingDifferentialNatIso C)

@[simp]
theorem extendIntLEAlternatingDifferentialNatIso_hom_app (m : ℤ) (K : ChainComplex C ℕ) :
    (extendIntLEAlternatingDifferentialNatIso (C := C) m).hom.app K =
      (CochainComplex.alternatingDifferentialIso
        (K.extend (ComplexShape.embeddingUpIntLE m))).hom :=
  CochainComplex.alternatingDifferentialNatIso_hom_app _

@[simp]
theorem extendIntLEAlternatingDifferentialNatIso_inv_app (m : ℤ) (K : ChainComplex C ℕ) :
    (extendIntLEAlternatingDifferentialNatIso (C := C) m).inv.app K =
      (CochainComplex.alternatingDifferentialIso
        (K.extend (ComplexShape.embeddingUpIntLE m))).inv :=
  CochainComplex.alternatingDifferentialNatIso_inv_app _

end TauCeti
