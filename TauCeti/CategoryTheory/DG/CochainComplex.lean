/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Enrichment
public import TauCeti.CategoryTheory.DG.Basic

/-!
# Cochain complexes as a differential graded category

Cochain complexes in an `R`-linear preadditive category are enriched in cochain complexes of
`R`-modules through `TauCeti.linearHomComplex`, so they form a differential graded category.  This
file evaluates the differential graded operations of `TauCeti/CategoryTheory/DG/Basic.lean` on that
example: the degree-`n` morphisms are the degree-`n` cochains, the differential is Mathlib's
signed `CochainComplex.HomComplex.δ`, the identity is the identity cochain, and composition is
composition of cochains with the Koszul sign.

That sign is the whole content of the comparison.  A differential graded category composes
`Hom(X, Y) ⊗ Hom(Y, Z) ⟶ Hom(X, Z)` while composition of cochains is a closed map out of
`Hom(Y, Z) ⊗ Hom(X, Y)`, and interchanging the two factors of a tensor product of complexes is
the Koszul braiding.  Hence a degree-`p` cochain `z₁` followed by a degree-`q` cochain `z₂`
composes to `(-1) ^ (p * q) • z₁.comp z₂`.  This is the bridge between Mathlib's enriched factor
order and Keller's untwisted operation `m₂ (g, f) = g ∘ f`, and it is what fixes the sign
conventions of every later differential graded construction.

## Main results

* `TauCeti.dgDifferential_linearHomComplex`, `TauCeti.dgId_linearHomComplex` and
  `TauCeti.dgComp_linearHomComplex`: the differential, identity and composition of this
  differential graded category.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory MonoidalCategory CochainComplex.HomComplex HomologicalComplex

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The differential of the differential graded category of cochain complexes is the signed
differential `δ` of cochains. -/
@[simp]
theorem dgDifferential_linearHomComplex {F G : CochainComplex C ℤ} (n : ℤ)
    (z : DGHom R n F G) : dgDifferential R n z = δ n (n + 1) z :=
  linearHomComplex_d_apply R F G n (n + 1) z

/-- The identity of the differential graded category of cochain complexes is the identity
cochain. -/
@[simp]
theorem dgId_linearHomComplex (F : CochainComplex C ℤ) :
    dgId R F = (Cochain.ofHom (𝟙 F) : ModuleCat.of R (Cochain F F 0)) := by
  rw [dgId_def, linearHomComplexEnrichedCategory_eId, linearHomComplexUnit_f_zero_apply,
    one_smul]

/-- Composition in the differential graded category of cochain complexes is composition of
cochains, carrying the Koszul sign which converts Mathlib's enriched factor order into Keller's
untwisted operation. -/
@[simp]
theorem dgComp_linearHomComplex {F G K : CochainComplex C ℤ} {p q n : ℤ}
    (z₁ : DGHom R p F G) (z₂ : DGHom R q G K) (h : p + q = n) :
    dgComp R z₁ z₂ h =
      ((p * q).negOnePow • Cochain.comp (z₁ : Cochain F G p) (z₂ : Cochain G K q) h :
        ModuleCat.of R (Cochain F K n)) := by
  have hmap : dgCompMap R F G K p q n h =
      (p * q).negOnePow •
        ((β_ ((linearHomComplex R F G).X p) ((linearHomComplex R G K).X q)).hom ≫
          cochainCompTensor R F G K q p n (by dsimp; omega)) := by
    rw [dgCompMap_def, linearHomComplexEnrichedCategory_eComp]
    exact ι_linearHomComplexEnrichedComp R F G K p q n h
  rw [← dgCompMap_tmul, hmap]
  exact cochainCompTensor_braiding_tmul R F G K p q n h z₁ z₂

end TauCeti
