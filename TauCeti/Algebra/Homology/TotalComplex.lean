/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.GradedObject.Monoidal

/-!
# Total complexes of first-quadrant bicomplexes

A bicomplex indexed by `ℕ × ℕ` with homological differentials has only finitely many terms
`(K.X p).X q` with `p + q = n`, so its total complex exists in any preadditive category with finite
coproducts. Its differential is `d₁ + (-1)ᵖ d₂` on the summand `(K.X p).X q`, by Mathlib's sign
convention `TotalComplexShape (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)`.

An augmentation `ε : K.X 0 ⟶ E` of the column `0` by a chain complex `E`, that is a chain map
vanishing on the image of the horizontal differential `K.d 1 0`, induces a chain map
`HomologicalComplex₂.totalAugmentation` from the total complex to `E`. It is the map whose being a
quasi-isomorphism expresses that the augmented rows `⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q ⟶ E.X q` are
exact, as for the Čech complex of a cover or an acyclic resolution.

## Main definitions

* `HomologicalComplex₂.hasTotal_down_nat`: first-quadrant bicomplexes have total complexes.
* `HomologicalComplex₂.totalAugmentation`: the chain map from the total complex induced by an
  augmentation of the column `0`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]

/-- A first-quadrant bicomplex has a total complex as soon as finite coproducts exist. -/
instance hasTotal_down_nat
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ)) :
    K.HasTotal (ComplexShape.down ℕ) := fun n ↦
  have : Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) :=
    inferInstanceAs (Finite ((fun i : ℕ × ℕ ↦ i.1 + i.2) ⁻¹' {n}))
  inferInstance

variable (K : HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ))
  {E : ChainComplex C ℕ} (ε : K.X 0 ⟶ E) (hε : K.d 1 0 ≫ ε = 0)

/-- The components of `totalAugmentation`: `ε` on the column `0` and zero on the other columns. -/
private def totalAugmentationAux (n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p, q) = n) :
    (K.X p).X q ⟶ E.X n :=
  match p, h with
  | 0, h => ε.f q ≫ (E.XIsoOfEq (by simpa using h)).hom
  | _ + 1, _ => 0

/-- The chain map from the total complex of a first-quadrant bicomplex `K` to a chain complex `E`
induced by an augmentation `ε : K.X 0 ⟶ E` of the column `0` vanishing on the image of the
horizontal differential: it is `ε` on the summands `(K.X 0).X q` and zero on the other columns. -/
def totalAugmentation : K.total (ComplexShape.down ℕ) ⟶ E where
  f n := K.totalDesc (totalAugmentationAux K ε n)
  comm' := by
    rintro _ n rfl
    refine total.hom_ext _ fun p q h ↦ ?_
    rw [ι_totalDesc_assoc, total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc,
      ι_D₂_assoc]
    -- On the column `0` this is the commutation of `ε` with the vertical differentials, and on
    -- the column `1` it is `K.d 1 0 ≫ ε = 0`; the other terms land in columns `p ≥ 1`.
    rcases p with _ | p
    · obtain rfl : q = n + 1 := by simpa using h
      rw [d₁_eq_zero _ _ _ _ _ (by simp), zero_comp, zero_add,
        d₂_eq K _ 0 (show (ComplexShape.down ℕ).Rel (n + 1) n by simp) n (by simp)]
      simp [totalAugmentationAux]
    · have h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, q) = n := by
        simp at h ⊢
        omega
      rw [d₁_eq K _ (show (ComplexShape.down ℕ).Rel (p + 1) p by simp) q n h']
      have h₂ : K.d₂ (ComplexShape.down ℕ) (p + 1) q n ≫
          K.totalDesc (K.totalAugmentationAux ε n) = 0 := by
        rcases q with _ | q
        · rw [d₂_eq_zero _ _ _ _ _ (by simp), zero_comp]
        · rw [d₂_eq K _ (p + 1) (show (ComplexShape.down ℕ).Rel (q + 1) q by simp) n
            (by simp at h ⊢; omega)]
          simp [totalAugmentationAux]
      rw [h₂, add_zero]
      rcases p with _ | p
      · simp [totalAugmentationAux, ← HomologicalComplex.comp_f_assoc, hε]
      · simp [totalAugmentationAux]

/-- On the summand `(K.X 0).X q`, the augmentation of the total complex is the component of `ε` in
degree `q`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalAugmentation_f_zero (q : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) 0 q q (zero_add q) ≫ (K.totalAugmentation ε hε).f q =
      ε.f q := by
  simp [totalAugmentation, totalAugmentationAux]

/-- The augmentation of the total complex vanishes on the columns `p + 1`. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalAugmentation_f_succ (p q n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (p + 1, q) = n) :
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q n h ≫ (K.totalAugmentation ε hε).f n = 0 := by
  simp [totalAugmentation, totalAugmentationAux]

end HomologicalComplex₂
