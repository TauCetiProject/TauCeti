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
* `TauCeti.xIsoOfEq_hom_v` and `TauCeti.dgComp_v`: component formulas for degree transport and
  composition.
* `CochainComplex.HomComplex.Cochain.v_apply_mem_ker_of_δ_eq_zero`: a closed degree-zero cochain
  of complexes of modules sends closed elements to closed elements.

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

/-- Degree transport of a cochain does not change its components. -/
theorem xIsoOfEq_hom_v {K L : CochainComplex C ℤ} {a b : ℤ} (h : a = b)
    (z : DGHom R a K L) (p q : ℤ) (hpq : p + b = q) :
    (((dgHomComplex R K L).XIsoOfEq h).hom z : Cochain K L b).v p q hpq =
      (z : Cochain K L a).v p q (by omega) := by
  subst h
  rfl

/-- The component of the DG composition of cochains is their componentwise composition with
the Koszul sign. -/
theorem dgComp_v {K L M : CochainComplex C ℤ} {a b c : ℤ} (z₁ : DGHom R a K L)
    (z₂ : DGHom R b L M) (h : a + b = c) (x y w : ℤ) (h₁ : x + a = y) (h₂ : y + b = w) :
    (dgComp R z₁ z₂ h : Cochain K M c).v x w (by omega) =
      (a * b).negOnePow • ((z₁ : Cochain K L a).v x y h₁ ≫ (z₂ : Cochain L M b).v y w h₂) := by
  rw [dgComp_linearHomComplex, Cochain.units_smul_v]
  exact congrArg _ (Cochain.comp_v (z₁ : Cochain K L a) (z₂ : Cochain L M b) h x y w h₁ h₂)

end TauCeti

namespace CochainComplex.HomComplex.Cochain

/-- A closed cochain of degree zero between complexes of modules sends elements killed by the
differential to elements killed by the differential. -/
theorem v_apply_mem_ker_of_δ_eq_zero {R : Type*} [Ring R] {K L : CochainComplex (ModuleCat R) ℤ}
    (z : Cochain K L 0) (hz : δ 0 1 z = 0) {p q : ℤ} (hpq : p + 1 = q) {a : K.X p}
    (ha : (K.d p q).hom a = 0) :
    (z.v p p (add_zero p)).hom a ∈ LinearMap.ker (L.d p q).hom := by
  have key := congrArg (fun φ ↦ ModuleCat.Hom.hom φ a) (Cochain.congr_v hz p q hpq)
  simpa only [δ_zero_cochain_v, Cochain.zero_v, ModuleCat.hom_sub, ModuleCat.hom_comp,
    LinearMap.sub_apply, LinearMap.comp_apply, ha, map_zero, sub_zero, ModuleCat.hom_zero,
    LinearMap.zero_apply, LinearMap.mem_ker] using key

end CochainComplex.HomComplex.Cochain
