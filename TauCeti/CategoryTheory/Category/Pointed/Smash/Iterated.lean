/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Category.Pointed.Smash.Power

/-!
# Iterated smash powers of pointed types

Grouping coordinates identifies `X^∧(ι × κ)` with `(X^∧κ)^∧ι`. The first index labels
blocks, and the second labels coordinates within each block. This identification also works
for empty index types: the empty smash power is the two-point unit, not the one-point type.
The construction supplies the degreewise comparison for iterated simplicial sphere powers.

The coordinate convention is that of Hovey, Shipley and Smith, *Symmetric spectra*,
Section 1: permutations of the outer index permute whole blocks.
-/

public section

universe u v

open CategoryTheory

namespace Pointed.smashPow

variable {X Y : Pointed.{u}} {ι κ : Type v}

/-- Group a family of smash coordinates into rows, with the first index labeling rows. -/
noncomputable def curry (X : Pointed.{u}) (ι κ : Type v) :
    X.smashPow (ι × κ) ⟶ (X.smashPow κ).smashPow ι :=
  lift (fun f ↦ mk fun i ↦ mk fun j ↦ f (i, j)) fun _ p hp ↦
    mk_eq_point p.1 (mk_eq_point p.2 hp)

@[simp]
lemma curry_mk (f : ι × κ → X) :
    (curry X ι κ).toFun (mk f) = mk (fun i ↦ mk fun j ↦ f (i, j)) :=
  lift_mk _ _ f

/-- Grouping coordinates is a bijection, including when either index type is empty. -/
lemma curry_bijective : Function.Bijective (curry X ι κ).toFun := by
  classical
  have hpoint (f : ι × κ → X) :
      (mk fun i ↦ mk fun j ↦ f (i, j)) = ((X.smashPow κ).smashPow ι).point ↔
        mk f = (X.smashPow (ι × κ)).point := by
    simp only [mk_eq_point_iff, Prod.exists]
  constructor
  -- Away from the fat wedge, equality of rows is equality of every coordinate.
  · intro a b hab
    induction a using ind with
    | point =>
      induction b using ind with
      | point => rfl
      | mk g =>
        exact ((hpoint g).1
          (by simpa only [curry_mk, Pointed.Hom.map_point] using hab.symm)).symm
    | mk f =>
      induction b using ind with
      | point => exact (hpoint f).1 (by simpa only [curry_mk, Pointed.Hom.map_point] using hab)
      | mk g =>
        by_cases hf : mk f = (X.smashPow (ι × κ)).point
        · have hg : mk g = (X.smashPow (ι × κ)).point :=
            (hpoint g).1 (by simpa only [hf, curry_mk, Pointed.Hom.map_point] using hab.symm)
          exact hf.trans hg.symm
        · have hf' : ∀ i j, f (i, j) ≠ X.point := by
            simpa only [mk_eq_point_iff, Prod.exists, not_exists] using hf
          rcases mk_eq_mk_iff.1 (by simpa only [curry_mk] using hab) with h | h
          · apply congrArg mk
            funext p
            rcases mk_eq_mk_iff.1 (congrFun h p.1) with hrow | hrow
            · exact congrFun hrow p.2
            · obtain ⟨j, hj⟩ := hrow.1
              exact (hf' p.1 j hj).elim
          · obtain ⟨i, hi⟩ := h.1
            obtain ⟨j, hj⟩ := mk_eq_point_iff.1 hi
            exact (hf' i j hj).elim
  -- For a non-basepoint family, choose representatives of its non-basepoint rows.
  · intro a
    induction a using ind with
    | point => exact ⟨_, (curry X ι κ).map_point⟩
    | mk f =>
      by_cases hf : ∃ i, f i = (X.smashPow κ).point
      · exact ⟨_, (curry X ι κ).map_point.trans (mk_eq_point_iff.2 hf).symm⟩
      · have hrow (i : ι) : ∃ g : κ → X, mk g = f i := by
          have hi : f i ≠ (X.smashPow κ).point := fun h ↦ hf ⟨i, h⟩
          generalize ha : f i = a at hi ⊢
          induction a using ind with
          | point => exact (hi rfl).elim
          | mk g => exact ⟨g, rfl⟩
        choose g hg using hrow
        exact ⟨mk (fun p ↦ g p.1 p.2), by simp [hg]⟩

/-- Flattening nested smash powers identifies the outer index with the block index. -/
noncomputable def prodIso (X : Pointed.{u}) (ι κ : Type v) :
    (X.smashPow κ).smashPow ι ≅ X.smashPow (ι × κ) :=
  (Pointed.Iso.mk (Equiv.ofBijective (curry X ι κ).toFun curry_bijective)
    (curry X ι κ).map_point).symm

@[simp]
lemma prodIso_inv_toFun : (prodIso X ι κ).inv.toFun = (curry X ι κ).toFun := (rfl)

@[simp]
lemma prodIso_hom_mk_mk (f : ι → κ → X) :
    (prodIso X ι κ).hom.toFun (mk fun i ↦ mk (f i)) = mk (Function.uncurry f) := by
  apply curry_bijective.injective
  exact (congrFun (congrArg Pointed.Hom.toFun (prodIso X ι κ).hom_inv_id) _).trans
    (curry_mk (Function.uncurry f)).symm

/-- Grouping smash coordinates commutes with applying a pointed map in every coordinate. -/
@[reassoc]
lemma map_curry (f : X ⟶ Y) :
    map (ι × κ) f ≫ curry Y ι κ = curry X ι κ ≫ map ι (map κ f) := by
  ext g
  simp [Function.comp_def]

end Pointed.smashPow
