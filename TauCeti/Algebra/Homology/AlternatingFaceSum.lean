/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Alternating sums of face maps

The differential of the chain complex of a simplicial object is the alternating sum
`∑ᵢ (-1)ⁱ δᵢ` of its face maps, and its square vanishes because of the simplicial identities
`δⱼ₊₁ ≫ δᵢ = δᵢ ≫ δⱼ` for `i ≤ j`. Degeneracies play no role in this argument. This file isolates
it for two consecutive families of morphisms in a preadditive category, so that it applies to
semisimplicial and augmented semisimplicial objects, which have faces but no degeneracies.

## Main declarations

* `TauCeti.alternatingFaceSum`: the alternating sum `∑ᵢ (-1)ⁱ δᵢ` of a finite family of
  morphisms.
* `TauCeti.alternatingFaceSum_comp_alternatingFaceSum`: if two consecutive families of faces
  satisfy the simplicial identities, the composite of their alternating sums is zero.

The proof follows Mathlib's `AlgebraicTopology.AlternatingFaceMapComplex.d_squared`, which is the
case of the faces of a simplicial object.
-/

public section

open CategoryTheory Preadditive

namespace TauCeti

variable {C : Type*} [Category* C] [Preadditive C]

/-- The alternating sum `∑ᵢ (-1)ⁱ δᵢ` of a finite family of morphisms `δ₀, …, δₙ₋₁`. For the face
maps of a simplicial object it is the differential of the alternating face map complex. -/
def alternatingFaceSum {X Y : C} {n : ℕ} (δ : Fin n → (X ⟶ Y)) : X ⟶ Y :=
  ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) • δ i

theorem alternatingFaceSum_def {X Y : C} {n : ℕ} (δ : Fin n → (X ⟶ Y)) :
    alternatingFaceSum δ = ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) • δ i :=
  (rfl)

/-- If the faces `δ₀, …, δₙ₊₁ : X ⟶ Y` and `δ'₀, …, δ'ₙ : Y ⟶ Z` satisfy the simplicial identities
`δⱼ₊₁ ≫ δ'ᵢ = δᵢ ≫ δ'ⱼ` for `i ≤ j`, then the composite of their alternating sums vanishes. -/
theorem alternatingFaceSum_comp_alternatingFaceSum {X Y Z : C} {n : ℕ}
    (δ : Fin (n + 2) → (X ⟶ Y)) (δ' : Fin (n + 1) → (Y ⟶ Z))
    (h : ∀ i j : Fin (n + 1), i ≤ j → δ j.succ ≫ δ' i = δ i.castSucc ≫ δ' j) :
    alternatingFaceSum δ ≫ alternatingFaceSum δ' = 0 := by
  simp only [alternatingFaceSum, comp_sum, sum_comp, ← Finset.sum_product']
  -- The terms are indexed by pairs `(b, a)`, `b` indexing `δ'` and `a` indexing `δ`. Split them
  -- into those with `b < a` and the rest, and match `(i, j + 1)`, `i ≤ j`, with `(j, i)`: the
  -- two terms are equal morphisms with opposite signs.
  let S : Finset (Fin (n + 1) × Fin (n + 2)) := {ba | (ba.1 : ℕ) < ba.2}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun ba hba => (ba.2.pred fun h0 => by simp [S, h0] at hba,
    ba.1.castSucc)) ?_ ?_ ?_ ?_
  · rintro ⟨b, a⟩ hba
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_lt, Fin.val_castSucc,
      Fin.val_pred] at hba ⊢
    lia
  · rintro ⟨b, a⟩ hba ⟨b', a'⟩ hba' heq
    simp only [Prod.mk.injEq, Fin.castSucc_inj, Fin.pred_inj] at heq
    rw [heq.1, heq.2]
  · rintro ⟨j, i⟩ hij
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_lt] at hij
    refine ⟨(i.castLT (by lia), j.succ), by simp [S]; lia, ?_⟩
    simp
  · rintro ⟨b, a⟩ hba
    simp only [S, Finset.mem_filter_univ] at hba
    obtain ⟨j, rfl⟩ : ∃ j : Fin (n + 1), j.succ = a :=
      Fin.exists_succ_eq.2 fun h0 => by simp [h0] at hba
    have hbj : b ≤ j := by
      rw [Fin.le_def]
      simp only [Fin.val_succ] at hba
      lia
    simp only [Fin.pred_succ, zsmul_comp, comp_zsmul, smul_smul, h b j hbj, ← neg_smul]
    congr 1
    rw [Fin.val_succ, Fin.val_castSucc, pow_succ, mul_neg_one, mul_neg, mul_comm]

end TauCeti
